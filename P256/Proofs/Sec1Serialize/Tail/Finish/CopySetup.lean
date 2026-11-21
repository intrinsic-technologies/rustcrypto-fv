import P256.Proofs.Sec1Serialize.Tail.State
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.Copy.Pointer
import P256.Proofs.Program.CalleeStackOutput
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

structure CopyEntry [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) : Prop where
  pre : CalleePre t boundary 0x11c930 65 65 8
  state : FrameState s t 65 328 320
  execution : ∃ fuel, Advances boundary fuel s t
  source : t.regValue .rsi = stackPtr s - 296
  destination : t.regValue .rdi = s.regValue .rdi
  count : t.regValue .rdx = 65
  savedDestination : t.regValue .rbp = s.regValue .rdi
  returnAddress : (returnBoundary t).rip = 0x1111e1
  selected : (bufferRegion s 296).HasBytes t.external bytes

theorem copy_setup [bindings : Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (entry : SelectionExit s t boundary bytes) :
    ∃ u, CopyEntry s u boundary bytes := by
  have code := programLoaded_codeIn entry.state.loaded
  have hc1 : CodeIn (codeRange 0x1111ce [0x48, 0x8d, 0x74, 0x24, 0x10]) t :=
    programText_slice code 0x111ce _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, hs1, hr1, he1⟩ :=
    lea_r64_effect_step 0x1111ce 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid]) (by decide) (by decide)
      t (readyToStep entry.state.machine entry.state.bindingsSupported) hc1 entry.rip
  change (leaR64Effect 0x1111ce 6 (.sib 4 none 0 (.d8 16)) t).Holds t t1 at he1
  have stage1 := entry.state.after_registers hr1 he1.agrees
    (by simp [Component.Covers]) (by simp)
  have hm1 : t1.external = t.external := he1.agrees.external (by simp [Component.Covers])
  have hsrc1 : t1.regValue .rsi = s.regValue .rsp - 296 := by
    have hw : t1.regValue .rsi = t.regValue .rsp + 16 := he1.writes
    rw [hw]
    change stackPtr t + 16 = stackPtr s - 296
    rw [entry.state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hc2 : CodeIn (codeRange 0x1111d3 [0xba, 0x41, 0, 0, 0]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x111d3 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, hs2, hr2, he2⟩ := mov_r32_imm32_effect_step 0x1111d3 0xba
    (by decide) 65 t1 hr1 hc2 he1.rip
  change (movR32Imm32Effect 0x1111d3 5 2 65 t1).Holds t1 t2 at he2
  have stage2 := stage1.after_registers hr2 he2.agrees
    (by simp [Component.Covers]) (by simp)
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hc3 : CodeIn (codeRange 0x1111d8 [0x48, 0x89, 0xef]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x111d8 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, hs3, hr3, he3⟩ := mov_r64_r64_effect_step 0x1111d8 0x48 0xef
    (by simp [RexWPrefix]) (by decide) t2 hr2 hc3 he2.rip
  change (movR64R64Effect 0x1111d8 7 5 t2).Holds t2 t3 at he3
  have stage3 := stage2.after_registers hr3 he3.agrees
    (by simp [Component.Covers]) (by simp)
  have hm3 : t3.external = t.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hsrc3 : t3.regValue .rsi = s.regValue .rsp - 296 :=
    (he3.agrees.read (n := 64) (r := 6) (by simp)).trans
      ((he2.agrees.read (n := 64) (r := 6) (by simp)).trans hsrc1)
  have hdst3 : t3.regValue .rdi = s.regValue .rdi := by
    have hw : t3.regValue .rdi = t2.regValue .rbp := he3.writes
    exact hw.trans ((he2.agrees.read (n := 64) (r := 5) (by simp)).trans
      ((he1.agrees.read (n := 64) (r := 5) (by simp)).trans entry.destination))
  have hcount3 : t3.regValue .rdx = 65 :=
    (he3.agrees.read (n := 64) (r := 2) (by simp)).trans he2.writes
  have hpush : pushAddr t3 = s.regValue .rsp - 320 := by
    rw [pushAddr, stage3.rsp, BitVec.sub_sub]
    rfl
  have hw : MemWritable t3 (pushAddr t3) 8 := by
    rw [hpush]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (offset := 320) (by decide) (by decide))
      stage3.allocated
  have hn320 : (s.regValue .rsp - 320).toNat = (s.regValue .rsp).toNat - 320 :=
    stack_sub_toNat pre.stack (offset := 320) (by decide)
  have hcodeApart : RangeApart (pushAddr t3) 8 0x1111db 6 := by
    intro i hi j hj he
    apply pre.avoids (Stack.region s 328) (by simp) (pushAddr t3 + BitVec.ofNat 64 i)
    · rw [hpush]
      apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
      · rw [hn320]
        change (s.regValue .rsp).toNat - 328 ≤ (s.regValue .rsp).toNat - 320
        omega
      · rw [stack_region_end, hn320, stackPtr_eq_regValue_rsp]
        omega
    · left
      rw [he]
      have hp := inProgram_of_textOffset (0x111db + j) (by omega)
      simpa [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress] using hp
  have hpointer := memcpy_pointer stage3.loaded
  have htarget : callMemPtr 0x1111db (.rip 0xf3317) t3 = 0x11c930 := hpointer.2
  have hc4 : CodeIn (codeRange 0x1111db (encodeCallM64 (.rip 0xf3317))) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x111db _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, hs4, hr4, he4⟩ := call_m64_effect_step 0x1111db (.rip 0xf3317)
    trivial rfl rfl t3 hr3 hc4 ⟨⟨⟨he3.rip, hw, hcodeApart⟩,
      by rw [htarget]; decide⟩, hpointer.1⟩
  have hip4 : u.RIP = 0x11c930 := he4.rip.trans htarget
  have hsp4 : u.regValue .rsp = s.regValue .rsp - 320 := he4.writes.1.trans hpush
  have hsrc4 : u.regValue .rsi = s.regValue .rsp - 296 :=
    (he4.agrees.read (n := 64) (r := 6) (by simp)).trans hsrc3
  have hdst4 : u.regValue .rdi = s.regValue .rdi :=
    (he4.agrees.read (n := 64) (r := 7) (by simp)).trans hdst3
  have hcount4 : u.regValue .rdx = 65 :=
    (he4.agrees.read (n := 64) (r := 2) (by simp)).trans hcount3
  have hreturn : (returnBoundary u).rip = 0x1111e1 := (callEffect_stack he4).1
  have state4 := stage3.after_call pre (by decide) (by decide) hr4 he4
  have hpre := CalleePre.of_stack_and_output pre
    (⟨320, 296, by decide, by decide, by decide, by decide⟩ : StackBufferLayout 328 65 8)
    state4.bindingsSupported state4.machine state4.directionFlag state4.loaded
    state4.allocated hip4 state4.rsp hsrc4 hdst4
    (hreturn ▸ inProgram_of_textOffset 0x111e1 (by decide))
  refine ⟨u, hpre, state4, ?_, hsrc4, hdst4, hcount4, ?_, hreturn, ?_⟩
  · obtain ⟨n, hn⟩ := entry.execution
    have a1 := Advances.of_step hs1 (.inl (by rw [he1.rip]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111d3 (by decide))))
    have a2 := Advances.of_step hs2 (.inl (by rw [he2.rip]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111d8 (by decide))))
    have a3 := Advances.of_step hs3 (.inl (by rw [he3.rip]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111db (by decide))))
    have a4 := Advances.of_step hs4 (.inl (by rw [hip4]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
    exact ⟨_, (((hn.trans a1).trans a2).trans a3).trans a4⟩
  · exact (he4.agrees.read (n := 64) (r := 5) (by simp)).trans
      ((he3.agrees.read (n := 64) (r := 5) (by simp)).trans
      ((he2.agrees.read (n := 64) (r := 5) (by simp)).trans
      ((he1.agrees.read (n := 64) (r := 5) (by simp)).trans entry.destination)))
  · refine ⟨entry.selected.1, ?_⟩
    intro i
    have hsize : bytes.size = 65 := entry.selected.1
    have hb := entry.selected.2 i
    change u.external[BitVec.ofNat 64 ((stackPtr s - 296).toNat + i.val)]? = _
    change t.external[BitVec.ofNat 64 ((stackPtr s - 296).toNat + i.val)]? = _ at hb
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
    have keep := scalar_call_byte (by decide) stage3 he4
      (offset := 296) (len := 65) (i := i.val) (by decide) (by decide) (by have := i.isLt; omega)
    rw [hm3] at keep
    exact keep.trans hb

end P256.Proofs.Sec1Serialize
