import P256.Proofs.Projective.Double.CrossTerms.Memory

set_option autoImplicit false



namespace P256.Proofs.Projective.Double.CrossTerms

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem doubleDifference [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = 0x105f75) :
    ∃ u, Advances boundary 3 t u ∧ FrameState s u 96 1016 728 ∧ u.RIP = 0x105f80 ∧
      AgreesExcept (scratchComponents s [13, 7, 6]) t u ∧
      u.regValue .r13 = stackSlot s 40 ∧
      u.regValue .rdi = stackSlot s 40 ∧
      u.regValue .rsi = t.regValue .r12 := by
  obtain ⟨t1, run1, frame1, effect1⟩ := step_registers pre state
    (offset := 0x5f75) (lea_r64_effect_step 0x105f75 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip
    (inProgram_of_textOffset 0x5f7a (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 13, .rip]; decide)
  have agree1 : AgreesExcept [.reg 13, .rip] t t1 := effect1.agrees
  have part1 : AgreesExcept (scratchComponents s [13, 7, 6]) t t1 :=
    scratch_reg agree1 (by decide)
  have reg1_13 : t1.regValue .r13 = stackSlot s 40 := by
    have h : t1.regValue .r13 = stackPtr t + 40 := effect1.writes
    rw [state.rsp] at h
    exact h
  have all1 := part1
  obtain ⟨t2, run2, frame2, effect2⟩ := step_registers pre frame1
    (offset := 0x5f7a) (mov_r64_r64_effect_step 0x105f7a 0x4c 0xef (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect1.rip
    (inProgram_of_textOffset 0x5f7d (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 7, .rip]; decide)
  have agree2 : AgreesExcept [.reg 7, .rip] t1 t2 := effect2.agrees
  have part2 : AgreesExcept (scratchComponents s [13, 7, 6]) t1 t2 :=
    scratch_reg agree2 (by decide)
  have reg2_7 : t2.regValue .rdi = stackSlot s 40 := by
    exact effect2.writes.trans reg1_13
  have all2 := scratch_trans all1 part2
  have reg1_12 : t1.regValue .r12 = t.regValue .r12 :=
    (agree1.read (n := 64) (r := 12) (by simp)).trans (rfl)
  have reg2_12 : t2.regValue .r12 = t.regValue .r12 :=
    (agree2.read (n := 64) (r := 12) (by simp)).trans reg1_12
  obtain ⟨t3, run3, frame3, effect3⟩ := step_registers pre frame2
    (offset := 0x5f7d) (mov_r64_r64_effect_step 0x105f7d 0x4c 0xe6 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect2.rip
    (inProgram_of_textOffset 0x5f80 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 6, .rip]; decide)
  have agree3 : AgreesExcept [.reg 6, .rip] t2 t3 := effect3.agrees
  have part3 : AgreesExcept (scratchComponents s [13, 7, 6]) t2 t3 :=
    scratch_reg agree3 (by decide)
  have reg3_6 : t3.regValue .rsi = t.regValue .r12 := by
    exact effect3.writes.trans reg2_12
  have all3 := scratch_trans all2 part3
  have reg2_13 : t2.regValue .r13 = stackSlot s 40 :=
    (agree2.read (n := 64) (r := 13) (by simp)).trans reg1_13
  have reg3_13 : t3.regValue .r13 = stackSlot s 40 :=
    (agree3.read (n := 64) (r := 13) (by simp)).trans reg2_13
  have reg3_7 : t3.regValue .rdi = stackSlot s 40 :=
    (agree3.read (n := 64) (r := 7) (by simp)).trans reg2_7
  exact ⟨t3, ((run1.trans run2).trans run3), frame3, effect3.rip, all3, reg3_13, reg3_7, reg3_6⟩

end P256.Proofs.Projective.Double.CrossTerms
