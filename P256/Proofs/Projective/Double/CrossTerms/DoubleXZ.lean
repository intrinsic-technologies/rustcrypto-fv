import P256.Proofs.Projective.Double.CrossTerms.Memory

set_option autoImplicit false



namespace P256.Proofs.Projective.Double.CrossTerms

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem doubleXZ [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = 0x105e92) :
    ∃ u, Advances boundary 2 t u ∧ FrameState s u 96 1016 728 ∧ u.RIP = 0x105e9d ∧
      AgreesExcept (scratchComponents s [7, 6]) t u ∧
      u.regValue .rdi = stackSlot s 200 ∧
      u.regValue .rsi = t.regValue .r15 := by
  obtain ⟨t1, run1, frame1, effect1⟩ := step_registers pre state
    (offset := 0x5e92) (lea_r64_effect_step 0x105e92 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip
    (inProgram_of_textOffset 0x5e9a (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 7, .rip]; decide)
  have agree1 : AgreesExcept [.reg 7, .rip] t t1 := effect1.agrees
  have part1 : AgreesExcept (scratchComponents s [7, 6]) t t1 :=
    scratch_reg agree1 (by decide)
  have reg1_7 : t1.regValue .rdi = stackSlot s 200 := by
    have h : t1.regValue .rdi = stackPtr t + 200 := effect1.writes
    rw [state.rsp] at h
    exact h
  have all1 := part1
  have reg1_15 : t1.regValue .r15 = t.regValue .r15 :=
    (agree1.read (n := 64) (r := 15) (by simp)).trans (rfl)
  obtain ⟨t2, run2, frame2, effect2⟩ := step_registers pre frame1
    (offset := 0x5e9a) (mov_r64_r64_effect_step 0x105e9a 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect1.rip
    (inProgram_of_textOffset 0x5e9d (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 6, .rip]; decide)
  have agree2 : AgreesExcept [.reg 6, .rip] t1 t2 := effect2.agrees
  have part2 : AgreesExcept (scratchComponents s [7, 6]) t1 t2 :=
    scratch_reg agree2 (by decide)
  have reg2_6 : t2.regValue .rsi = t.regValue .r15 := by
    exact effect2.writes.trans reg1_15
  have all2 := scratch_trans all1 part2
  have reg2_7 : t2.regValue .rdi = stackSlot s 200 :=
    (agree2.read (n := 64) (r := 7) (by simp)).trans reg1_7
  exact ⟨t2, (run1.trans run2), frame2, effect2.rip, all2, reg2_7, reg2_6⟩

end P256.Proofs.Projective.Double.CrossTerms
