import P256.Proofs.Generate.Wrapper.Tail.Registers
import P256.Proofs.Sec1.Representation
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem prepare_serializer [Bindings] {initial s : RamState} {written : Option MemoryRegion} {point : Standards.SECG.ECC.Curve.Point}
    (state : State initial s 264 written) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x106de8)
    (affine : Sec1.AffineAt s (stackPtr initial - 152) point) :
    ∃ t, State initial t 264 written ∧ t.RIP = 0x106df4 ∧
      t.regValue .rsi = stackPtr initial - 152 ∧
      t.regValue .rdi = stackPtr initial - 256 ∧ t.regValue .rdx = 0 ∧
      Sec1.AffineAt t (stackPtr initial - 152) point ∧ t.external = s.external := by
  have code := programLoaded_codeIn state.loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (lea_r64_effect_step 0x106de8 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice code 0x6de8 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x6ded (by decide)))
  have g1 : AgreesExcept [.reg 6, .rip] s s1 := e1.agrees
  have m1 := g1.external (by simp [Component.Covers])
  have src1 : s1.regValue .rsi = stackPtr initial - 152 := by
    have h : s1.regValue .rsi = stackPtr s + 112 := e1.writes
    rw [h, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  obtain ⟨s2, a2, r2, e2⟩ :=
    (lea_r64_effect_step 0x106ded 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x6ded _ (by decide +kernel)
        (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x6df2 (by decide)))
  have g2 : AgreesExcept [.reg 7, .rip] s1 s2 := e2.agrees
  have m2 := (g2.external (by simp [Component.Covers])).trans m1
  have dst2 : s2.regValue .rdi = stackPtr initial - 256 := by
    have h : s2.regValue .rdi = stackPtr s1 + 8 := e2.writes
    have sp : stackPtr s1 = stackPtr s := g1.read (n := 64) (r := 4) (by simp)
    rw [h,sp,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  obtain ⟨t, a3, r3, e3⟩ := (xor_r32_r32_effect_step 0x106df2 0xd2 rfl).advances r2
    (programText_slice (code.of_external_eq m2) 0x6df2 _ (by decide +kernel)
      (by decide +kernel)) e2.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6df4 (by decide)))
  have g3 : AgreesExcept [.reg 2, .flags, .rip] s2 t := e3.agrees
  have ag : AgreesExcept [.reg 7, .reg 6, .reg 2, .flags, .rip] s t :=
    ((g1.trans g2).trans g3).mono (by simp)
  have memory := ag.external (by simp [Component.Covers])
  refine ⟨t, state.after_registers (a1.trans (a2.trans a3)) r3 ag
    (by simp [Component.Covers]) (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp),
    e3.rip, ((g2.trans g3).read (n := 64) (r := 6) (by simp)).trans src1,
    (g3.read (n := 64) (r := 7) (by simp)).trans dst2, ?_, ?_⟩
  · have h : t.regValue .rdx =
        ((s2.regValue .rdx).setWidth 32 ^^^ (s2.regValue .rdx).setWidth 32).setWidth 64 :=
      e3.writes
    simpa using h
  · exact ⟨affine.of_bytes_eq (fun _ _ => by rw [memory]),memory⟩

end P256.Proofs.Generate.Wrapper
