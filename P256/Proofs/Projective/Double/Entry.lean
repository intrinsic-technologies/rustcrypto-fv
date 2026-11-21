import P256.Proofs.Projective.Double.Prologue
import P256.Proofs.Projective.Double.PointCall
import P256.Proofs.Projective.Double.Values
import P256.Proofs.Field.Square
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (input : ProjectiveAt s (s.regValue .rdi) point) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1016 728 ∧
      t.RIP = 0x105dc3 ∧ SquaresAt s t point := by
  obtain ⟨t0, run0, frame0, rip0, _, agrees0⟩ := frame_entry pre
  have point0 := point_of_stack pre (save_frame pre (by decide) agrees0 (by simp [Component.Covers])) input
  have hd0 : t0.regValue .rdi = s.regValue .rdi :=
    agrees0.read (n := 64) (r := 7) (by simp [saveFrame])
  obtain ⟨t1, run1, frame1, effect1⟩ := step_registers pre frame0
    (offset := 0x5d91) (mov_r64_r64_effect_step 0x105d91 0x48 0xfb (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) rip0
    (inProgram_of_textOffset 0x5d94 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 3, .rip]; decide +kernel)
  have bx1 : t1.regValue .rbx = s.regValue .rdi := effect1.writes.trans hd0
  obtain ⟨t2, run2, frame2, effect2⟩ := step_registers pre frame1
    (offset := 0x5d94) (lea_r64_effect_step 0x105d94 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect1.rip
    (inProgram_of_textOffset 0x5d99 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  obtain ⟨t3, run3, frame3, effect3⟩ := step_registers pre frame2
    (offset := 0x5d99) (mov_r64_r64_effect_step 0x105d99 0x48 0xde (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect2.rip
    (inProgram_of_textOffset 0x5d9c (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have bx3 : t3.regValue .rbx = s.regValue .rdi :=
    (effect3.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans
      ((effect2.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans bx1)
  have in3 : t3.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 0 := by
    have hw : t3.regValue .rsi = t2.regValue .rbx := effect3.writes
    simpa only [BitVec.add_zero] using hw.trans ((effect2.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans bx1)
  have out3 : t3.regValue .rdi = stackPtr s - BitVec.ofNat 64 624 := by
    have hw : t2.regValue .rdi = stackPtr t1 + 104 := effect2.writes
    have addr : stackPtr t1 + 104 = stackPtr s - BitVec.ofNat 64 624 :=
      scalar_stack_address (frameOffset := 728) frame1.rsp (by decide) (offset := 104) (by decide)
    rw [addr] at hw
    exact (effect3.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 6, .rip]; decide +kernel)).trans hw
  have ext3 : t3.external = t0.external :=
    ((effect1.agrees.trans effect2.agrees).trans effect3.agrees).external (by simp [Component.Covers])
  have point3 : ProjectiveAt t3 (s.regValue .rdi) point := by
    simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using point0
  obtain ⟨n4, t4, run4, frame4, rip4, square4, regs4, bytes4, work4⟩ :=
    point_unary_call pre frame3 (entry := 0x113800) (reserve := 280)
      (inputOffset := 0) (outputOffset := 624) (x := point.x)
      (op := fun x => x * x % P256.Spec.Operations.domain.p)
      (by decide) (by decide +kernel) (by decide) (by decide) 0x5d9c 0xda5f
      (by decide) (by decide +kernel) (by decide) (by decide)
      (inProgram_of_textOffset 0x13800 (by decide))
      (fun _ hp hx => field_square_correct hp hx)
      effect3.rip in3 out3 (by simpa only [BitVec.add_zero] using point3.1)
  have bx4 : t4.regValue .rbx = s.regValue .rdi :=
    (regs4 .rbx (by decide)).trans bx3
  have point4 := point_of_stack pre (work_stack_frame pre work4) point3
  obtain ⟨t5, run5, frame5, effect5⟩ := step_registers pre frame4
    (offset := 0x5da1) (lea_r64_effect_step 0x105da1 0x48 (by simp [RexWPrefix]) 6 (.base 3 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip4
    (inProgram_of_textOffset 0x5da5 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  obtain ⟨t6, run6, frame6, effect6⟩ := step_registers pre frame5
    (offset := 0x5da5) (lea_r64_effect_step 0x105da5 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect5.rip
    (inProgram_of_textOffset 0x5dad (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have bx6 : t6.regValue .rbx = s.regValue .rdi :=
    (effect6.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans
      ((effect5.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans bx4)
  have in6 : t6.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 32 := by
    have hw : t5.regValue .rsi = t4.regValue .rbx + 32 := effect5.writes
    rw [bx4] at hw
    exact (effect6.agrees.read (n := 64) (r := 6) (by change Component.reg 6 ∉ [Component.reg 7, .rip]; decide +kernel)).trans hw
  have out6 : t6.regValue .rdi = stackPtr s - BitVec.ofNat 64 592 := by
    have hw : t6.regValue .rdi = stackPtr t5 + 136 := effect6.writes
    have addr : stackPtr t5 + 136 = stackPtr s - BitVec.ofNat 64 592 :=
      scalar_stack_address (frameOffset := 728) frame5.rsp (by decide) (offset := 136) (by decide)
    rw [addr] at hw
    exact hw
  have ext6 : t6.external = t4.external :=
    (effect5.agrees.trans effect6.agrees).external (by simp [Component.Covers])
  have point6 : ProjectiveAt t6 (s.regValue .rdi) point := by
    simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using point4
  obtain ⟨n7, t7, run7, frame7, rip7, square7, regs7, bytes7, work7⟩ :=
    point_unary_call pre frame6 (entry := 0x113800) (reserve := 280)
      (inputOffset := 32) (outputOffset := 592) (x := point.y)
      (op := fun x => x * x % P256.Spec.Operations.domain.p)
      (by decide) (by decide +kernel) (by decide) (by decide) 0x5dad 0xda4e
      (by decide) (by decide +kernel) (by decide) (by decide)
      (inProgram_of_textOffset 0x13800 (by decide))
      (fun _ hp hx => field_square_correct hp hx)
      effect6.rip in6 out6 (by exact point6.2.1)
  have bx7 : t7.regValue .rbx = s.regValue .rdi :=
    (regs7 .rbx (by decide)).trans bx6
  have point7 := point_of_stack pre (work_stack_frame pre work7) point6
  obtain ⟨t8, run8, frame8, effect8⟩ := step_registers pre frame7
    (offset := 0x5db2) (lea_r64_effect_step 0x105db2 0x48 (by simp [RexWPrefix]) 6 (.base 3 (.d8 64)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip7
    (inProgram_of_textOffset 0x5db6 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  obtain ⟨t9, run9, frame9, effect9⟩ := step_registers pre frame8
    (offset := 0x5db6) (lea_r64_effect_step 0x105db6 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect8.rip
    (inProgram_of_textOffset 0x5dbe (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have bx9 : t9.regValue .rbx = s.regValue .rdi :=
    (effect9.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans
      ((effect8.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans bx7)
  have in9 : t9.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 64 := by
    have hw : t8.regValue .rsi = t7.regValue .rbx + 64 := effect8.writes
    rw [bx7] at hw
    exact (effect9.agrees.read (n := 64) (r := 6) (by change Component.reg 6 ∉ [Component.reg 7, .rip]; decide +kernel)).trans hw
  have out9 : t9.regValue .rdi = stackPtr s - BitVec.ofNat 64 560 := by
    have hw : t9.regValue .rdi = stackPtr t8 + 168 := effect9.writes
    have addr : stackPtr t8 + 168 = stackPtr s - BitVec.ofNat 64 560 :=
      scalar_stack_address (frameOffset := 728) frame8.rsp (by decide) (offset := 168) (by decide)
    rw [addr] at hw
    exact hw
  have ext9 : t9.external = t7.external :=
    (effect8.agrees.trans effect9.agrees).external (by simp [Component.Covers])
  have point9 : ProjectiveAt t9 (s.regValue .rdi) point := by
    simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using point7
  obtain ⟨n10, t10, run10, frame10, rip10, square10, regs10, bytes10, work10⟩ :=
    point_unary_call pre frame9 (entry := 0x113800) (reserve := 280)
      (inputOffset := 64) (outputOffset := 560) (x := point.z)
      (op := fun x => x * x % P256.Spec.Operations.domain.p)
      (by decide) (by decide +kernel) (by decide) (by decide) 0x5dbe 0xda3d
      (by decide) (by decide +kernel) (by decide) (by decide)
      (inProgram_of_textOffset 0x13800 (by decide))
      (fun _ hp hx => field_square_correct hp hx)
      effect9.rip in9 out9 (by exact point9.2.2)
  have bx10 : t10.regValue .rbx = s.regValue .rdi :=
    (regs10 .rbx (by decide)).trans bx9
  have point10 := point_of_stack pre (work_stack_frame pre work10) point9
  have xx6 : MontgomeryAt t6 (stackPtr s - 624) (values point).xx := by
    exact ⟨square4.1, square4.2.1, fun i hi => by rw [ext6]; exact square4.2.2 i hi⟩
  have xx7 : MontgomeryAt t7 (stackPtr s - 624) (values point).xx :=
    ⟨xx6.1, xx6.2.1, fun i hi => (bytes7 624 32 (by decide) (by decide) (by decide) i hi).trans (xx6.2.2 i hi)⟩
  have xx9 : MontgomeryAt t9 (stackPtr s - 624) (values point).xx := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using xx7
  have yy9 : MontgomeryAt t9 (stackPtr s - 592) (values point).yy := by
    exact ⟨square7.1, square7.2.1, fun i hi => by rw [ext9]; exact square7.2.2 i hi⟩
  have xx10 : MontgomeryAt t10 (stackPtr s - 624) (values point).xx :=
    ⟨xx9.1, xx9.2.1, fun i hi => (bytes10 624 32 (by decide) (by decide) (by decide) i hi).trans (xx9.2.2 i hi)⟩
  have yy10 : MontgomeryAt t10 (stackPtr s - 592) (values point).yy :=
    ⟨yy9.1, yy9.2.1, fun i hi => (bytes10 592 32 (by decide) (by decide) (by decide) i hi).trans (yy9.2.2 i hi)⟩
  have execution := (((((((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10
  exact ⟨_, t10, execution, frame10, rip10, point10, bx10, xx10, yy10, square10⟩

end P256.Proofs.Projective.Double
