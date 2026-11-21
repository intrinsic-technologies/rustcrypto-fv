import P256.Proofs.Program.Copy
import P256.Proofs.ReadBe.Loop.Setup
import P256.Proofs.ReadBe.CopyValue

set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.Program (memcpy_correct)

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def loopCopyComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .flags, .rip,
   .mem (frameBase s + 16) 8, .mem (stackPtr s - 80) 8]

theorem Pre.loop_copy_writes [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) : WritesWithin (loopCopyComponents s) #v[scratchRegion s] := by
  intro c hc a ha
  simp only [loopCopyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact ha.elim
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨scratchRegion s, by simp, ?_⟩
    rw [frameBase_add16]
    exact pre.scratch_contains (offset := 56) (len := 8) (by decide) (by decide) (by decide) hi
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨scratchRegion s, by simp,
      pre.scratch_contains (offset := 80) (len := 8) (by decide) (by decide) (by decide) hi⟩

theorem Pre.scratch_input_bytes [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : Pre s boundary)
    (frame : MemoryWriteFrame t u #v[scratchRegion s])
    (bytes : (registerRegion s .rdi 32).HasBytes t.external input) :
    (registerRegion s .rdi 32).HasBytes u.external input := by
  refine ⟨bytes.1, ?_⟩
  intro i
  have hsize : input.size = 32 := bytes.1
  have hb := bytes.2 i
  change u.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat+i.val)]? = _
  change t.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat+i.val)]? = _ at hb
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
  exact (pre.scratch_input_byte frame (hsize ▸ i.isLt)).trans hb

structure LoopCopyResult [Bindings] (s t u : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) (k : Nat) : Prop where
  execution : ∃ fuel, Advances boundary fuel t u
  frame : Frame s u
  rip : u.RIP = 0x119131
  agrees : AgreesExcept (loopCopyComponents s) t u
  value : P256.Proofs.Common.Instructions.bswap64 (memLoad u.external (frameBase s + 16) 64) =
    BitVec.ofNat 64 (Arith.uint input / 2^(64*k))

theorem loop_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {k : Nat} (pre : Pre s boundary) (state : LoopState s t input k)
    (hk : k < 4) : ∃ u, LoopCopyResult s t u boundary input k := by
  obtain ⟨v, setup⟩ := loop_setup pre state hk
  have push : pushAddr v = stackPtr s - 80 := setup.frame.push_address
  have writable : MemWritable v (pushAddr v) 8 := by
    rw [push]
    exact writable_of_grow
      (stack_sub_writable8 pre.stack pre.stack_avoids_tables (offset := 80) (by decide) (by decide)) setup.frame.allocated
  have apart : RangeApart (pushAddr v) 8 0x11912b 6 := by
    rw [push]
    exact pre.stack_code_apart (offset := 80) (len := 8) (codeOffset := 0x1912b)
      (by decide) (by decide) (by decide)
  have pointer := P256.Proofs.Program.memcpy_pointer setup.frame.loaded
  have target : callMemPtr 0x11912b (.rip 0xeb3c7) v = 0x11c930 := pointer.2
  obtain ⟨call, step, ready, effect⟩ := call_m64_effect_step 0x11912b (.rip 0xeb3c7)
    trivial rfl rfl v (readyToStep setup.frame.machine setup.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn setup.frame.loaded) 0x1912b _
      (by decide +kernel) (by decide +kernel))
    ⟨⟨⟨setup.rip, writable, apart⟩, by rw [target]; decide +kernel⟩, pointer.1⟩
  change (callEffect (callMemPtr 0x11912b (.rip 0xeb3c7)) 0x119131 v).Holds v call at effect
  have effect' : (callEffect (fun _ => 0x11c930) 0x119131 v).Holds v call := by
    simpa only [callEffect, pushEffect, target] using effect
  have callRun : Advances boundary 1 v call := Advances.of_step step (.inl (by
    rw [effect'.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
  have callPre := pre.memcpy_pre setup.frame hk ready effect' setup.source setup.destination
  have count : call.regValue .rdx = BitVec.ofNat 64 8 :=
    (effect'.agrees.read (n := 64) (r := 2) (by simp)).trans setup.count
  obtain ⟨u, result, copied, copyAgree⟩ := memcpy_correct callPre count (by decide +kernel)
  have dst : call.regValue .rdi = frameBase s + 16 :=
    (effect'.agrees.read (n := 64) (r := 7) (by simp)).trans setup.destination
  have callAgree : AgreesExcept [.reg 4, .mem (stackPtr s - 80) 8, .rip] v call := by
    have h := effect'.agrees
    simp only [pushEffect_components, push] at h
    exact h
  have total : AgreesExcept (loopCopyComponents s) t u :=
    ((setup.agrees.trans callAgree).trans copyAgree).mono (by
      simp [loopSetupComponents, loopCopyComponents, P256.Proofs.Program.Copy.copyComponents,
        P256.Proofs.Program.Copy.registerComponents, dst])
  have setupAgree : AgreesExcept (loopCopyComponents s) t v := setup.agrees.mono (by
    simp [loopSetupComponents, loopCopyComponents])
  have setupBytes := pre.scratch_input_bytes
    (setupAgree.memoryWriteFrame pre.loop_copy_writes) state.inputBytes
  refine ⟨u, ⟨?_, setup.frame.after_memcpy pre effect' setup.destination result,
    result.rip.trans (callEffect_stack effect').1, total,
    pre.copied_limb setup.frame hk setupBytes effect' setup.source setup.destination copied⟩⟩
  obtain ⟨m, hm⟩ := setup.execution
  obtain ⟨n, hn⟩ := result.execution
  exact ⟨m+1+n, (hm.trans callRun).trans hn⟩

end P256.Proofs.ReadBe
