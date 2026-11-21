import P256.Proofs.Nonce.Fill.Tail.Decode.Scan.State
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Scan

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : ScanState initial s orderAddress state) (rip : s.RIP = 0x1074b4)
    (order : s.regValue .r15 = orderAddress)
    (scratch : s.regValue .r12 = frameBase initial + 8)
    (shift : s.regValue .r14 = 0) (bits : s.regValue .r8 = 256)
    (zero : (StatusFlags.ofRFLAGS s.RFLAGS).ZF = true) :
    ∃ t, Advances boundary 3 s t ∧ ScanReady initial t orderAddress state := by
  obtain ⟨a, step, ra, raw⟩ := jcc_rel8_effect_step 0x1074b4 4 0x2a s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x74b4 _ (by decide) (by decide +kernel))
    ⟨rip, by intro; decide⟩
  have ae := jccEffect_taken (show condHolds 4 (StatusFlags.ofRFLAGS s.RFLAGS) = true from zero) raw
  have ga : AgreesExcept [.rip] s a := ae.agrees
  have aa : Advances boundary 1 s a := Advances.of_step step (.inl (by
    rw [ae.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74e0 (by decide))))
  have fa := input.after_registers ra ga (by simp [Component.Covers]) (by simp)
  obtain ⟨b, ab, rb, eb⟩ :=
    (mov_r64_m64_effect_step 0x1074e0 0x4c (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl).advances
      (readyToStep fa.machine fa.bindingsSupported)
      (programText_slice (programLoaded_codeIn fa.loaded) 0x74e0 _ (by decide) (by decide +kernel))
      ⟨ae.rip, Fill.stack_readable pre fa.toFrame (offset := 48) (len := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74e5 (by decide)))
  have gb : AgreesExcept [.reg 13, .rip] a b := eb.agrees
  have fb := fa.after_registers rb gb (by simp [Component.Covers]) (by simp)
  have length : b.regValue .r13 = 32 := by
    have h : b.regValue .r13 = memLoad a.external (stackPtr a + 48) 64 := eb.writes
    rw [fa.rsp, fa.lengthSlot] at h
    exact h
  obtain ⟨t, advanceT, rt, et⟩ :=
    (mov_r64_r64_effect_step 0x1074e5 0x4c 0xee (by simp [RexWPrefix]) rfl).advances
      (readyToStep fb.machine fb.bindingsSupported)
      (programText_slice (programLoaded_codeIn fb.loaded) 0x74e5 _ (by decide) (by decide +kernel)) eb.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74e8 (by decide)))
  have gt : AgreesExcept [.reg 6, .rip] b t := et.agrees
  have ft := fb.after_registers rt gt (by simp [Component.Covers]) (by simp)
  have total := (ga.trans gb).trans gt
  refine ⟨t, (aa.trans ab).trans advanceT, ⟨ft.toFrame, ft.toSlots,
    (gt.read (n := 64) (r := 13) (by simp)).trans length,
    (total.read (n := 64) (r := 15) (by simp)).trans order, ft.generator⟩, et.rip,
    (total.read (n := 64) (r := 12) (by simp)).trans scratch,
    (total.read (n := 64) (r := 14) (by simp)).trans shift,
    (total.read (n := 64) (r := 8) (by simp)).trans bits,
    (show t.regValue .rsi = b.regValue .r13 from et.writes).trans length, ft.output⟩

end P256.Proofs.Nonce.Fill.Tail.Decode.Scan
