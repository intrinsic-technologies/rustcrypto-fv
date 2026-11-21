import P256.Proofs.SignatureFromDer.Decode.Saved
import P256.Proofs.Program.WrapperArena
import P256.Proofs.Sec1.Wrapper.Arena
import P256.Proofs.Sec1.Wrapper.Save

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Initialized [Bindings] (initial s : RamState) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x101813
  rsp : stackPtr s = stackPtr initial - 232
  savedRbx : memLoad s.external (stackPtr initial - 24) 64 = initial.regValue .rbx
  savedR14 : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .r14
  savedR15 : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .r15
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  agrees : AgreesExcept (saveComponents initial ++ arenaComponents) initial s
  frame : MemoryWriteFrame initial s (wrapperRegions publicKeyFromSec1Bytes initial)

theorem initialize_correct [bindings : Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hcall : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices) :
    ∃ t, Initialized initial t := by
  obtain ⟨s, hs⟩ := save_correct hb hm hcall
  have pre : ArenaPre s := by
    refine ⟨hs.rip, ?_, ?_⟩
    · have hsp : stackPtr s + 240 = stackPtr initial + 8 := by
        rw [hs.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [hsp]
      exact heap_length_memReadable hcall hs.agrees.grow
    · intro off hoff
      exact call_statics_writable hcall hs.agrees.grow (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        omega)
  obtain ⟨n, t, run, ready, _, effect⟩ :=
    arena_correct (returnBoundary initial) (outer_boundary hcall hm hb) s hs.ready
      (programText_slice (programLoaded_codeIn hs.loaded) 0x17dc arenaBytes
        (by decide +kernel) (by decide +kernel)) pre
  have agrees : AgreesExcept arenaComponents s t := by
    simpa [arenaEffect, Effect.components, Write.component, Operand.component, arenaComponents] using effect.agrees
  have frame : MemoryWriteFrame s t (wrapperRegions publicKeyFromSec1Bytes initial) := by
    apply agrees.memoryWriteFrame
    have lift {off : Nat} (ho : off ∈ ([0,8,16,24,32] : List Nat)) {a : BitVec 64}
        (hc : (Component.mem (0x300000 + BitVec.ofNat 64 off) 8).Covers a) :
        ∃ region ∈ wrapperRegions publicKeyFromSec1Bytes initial, region.Contains a.toNat := by
      obtain ⟨region, hr, hc⟩ := static_component_within ho hc
      exact ⟨region, by
        have hr' : region = allocatorStateRegion ∨ region = randomSourceRegion := by simpa using hr
        rcases hr' with rfl | rfl <;> simp [wrapperRegions], hc⟩
    intro c hc a hv
    simp only [arenaComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hv.elim
    · exact lift (off := 0) (by simp) hv
    · exact lift (off := 8) (by simp) hv
    · exact lift (off := 16) (by simp) hv
    · exact lift (off := 24) (by simp) hv
    · exact lift (off := 32) (by simp) hv
    · exact hv.elim
  have savedFrame := saved_frame hcall.stackAvailable.1 hs
  have fullFrame := memoryWriteFrame_trans savedFrame frame
  have saved := P256.Proofs.SignatureFromDer.Decode.savedMemory_words initial
  change memLoad (savedMemory initial) (stackPtr initial - 24) 64 = initial.regValue .rbx ∧
    memLoad (savedMemory initial) (stackPtr initial - 16) 64 = initial.regValue .r14 ∧
    memLoad (savedMemory initial) (stackPtr initial - 8) 64 = initial.regValue .r15 ∧
    memLoad (savedMemory initial) (stackPtr initial) 64 = (returnBoundary initial).rip at saved
  rw [← hs.memory] at saved
  have hb := (arena_preserves_stack_word hcall agrees (offset := 24) (by decide)).trans saved.1
  have h14 := (arena_preserves_stack_word hcall agrees (offset := 16) (by decide)).trans saved.2.1
  have h15 := (arena_preserves_stack_word hcall agrees (offset := 8) (by decide)).trans saved.2.2.1
  have hret := arena_preserves_stack_word hcall agrees (offset := 0) (by decide)
  simp only [BitVec.sub_zero] at hret
  exact ⟨t, ⟨⟨4 + n, hs.execution.trans run⟩, ready,
    wrapper_frame_loaded hcall hcall.programLoaded fullFrame, effect.rip,
    (agrees.read (n := 64) (r := 4) (by simp [arenaComponents])).trans hs.rsp,
    hb, h14, h15, hret.trans saved.2.2.2, hs.agrees.trans agrees, fullFrame⟩⟩

end P256.Proofs.Sec1.Wrapper
