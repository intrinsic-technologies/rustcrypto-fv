import P256.Proofs.Projective.Add.Values
import P256.Proofs.Projective.Add.Call.Sites
import P256.Proofs.Field.Add
import P256.Proofs.Field.Subtract
import P256.Proofs.Field.Montgomery
import P256.Proofs.Projective.Add.Output.Preserve
import P256.Proofs.Projective.Add.Output.Setup

set_option autoImplicit false


namespace P256.Proofs.Projective.Add

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

open Output

theorem output_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left right : Projective}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (state : FrameState s t 96 920 632) (rip : t.RIP = 0x105af0)
    (input : CombinationsAt s t left right) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x105d6d ∧ ProjectiveAt u (s.regValue .rdi) (left.add right) := by
  obtain ⟨fuel1, t1, run1, state1, rip1, value1, agrees1⟩ :=
    Copy.execute_stack (entryOffset := 0x5af0) pre state
      (copy_yy_plus_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (offset := 40) (by decide) rfl
      (Copy.stack_pre pre state (by decide) rfl rip
        (stack_readable (frameOffset := 632) pre state (by decide) (offset := 360) (len := 32) (by decide))
        (by change RangeApart (stackPtr t + BitVec.ofNat 64 40) 32 (stackPtr t + BitVec.ofNat 64 360) 32
            rw [scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 40) (by decide), scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 360) (by decide)]
            exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (by decide)))
      (by change MontgomeryAt t (stackPtr t + BitVec.ofNat 64 360) _
          rw [scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 360) (by decide)]
          exact input.yyPlus)
  have dest1 : (Operand.reg 4 : Operand 64).read t + 40 = stackPtr s - 592 :=
    scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by decide)
  rw [dest1] at value1 agrees1
  have mem1_stack112 : MontgomeryAt t1 (stackPtr s - 112) (values left right).bxz3 := copy_stack_stack pre agrees1 (by decide) (by decide) (by decide) (by decide) (by decide) input.bxz3
  have mem1_stack272 : MontgomeryAt t1 (stackPtr s - 272) (values left right).yyPlus := copy_stack_stack pre agrees1 (by decide) (by decide) (by decide) (by decide) (by decide) input.yyPlus
  have mem1_stack304 : MontgomeryAt t1 (stackPtr s - 304) (values left right).yyMinus := copy_stack_stack pre agrees1 (by decide) (by decide) (by decide) (by decide) (by decide) input.yyMinus
  have mem1_stack368 : MontgomeryAt t1 (stackPtr s - 368) (values left right).yz := copy_stack_stack pre agrees1 (by decide) (by decide) (by decide) (by decide) (by decide) input.yz
  have mem1_stack400 : MontgomeryAt t1 (stackPtr s - 400) (values left right).xy := copy_stack_stack pre agrees1 (by decide) (by decide) (by decide) (by decide) (by decide) input.xy
  have mem1_stack432 : MontgomeryAt t1 (stackPtr s - 432) (values left right).xxMinus := copy_stack_stack pre agrees1 (by decide) (by decide) (by decide) (by decide) (by decide) input.xxMinus
  have reg1_3 : t1.regValue .rbx = s.regValue .rdi := (agrees1.read (n := 64) (r := 3) (by simp [Copy32.components])).trans input.rbx
  have reg1_12 : t1.regValue .r12 = stackPtr s - 112 := (agrees1.read (n := 64) (r := 12) (by simp [Copy32.components])).trans input.r12
  have reg1_13 : t1.regValue .r13 = stackPtr s - 432 := (agrees1.read (n := 64) (r := 13) (by simp [Copy32.components])).trans input.r13
  obtain ⟨fuel2, t2, run2, state2, rip2, value2, agrees2⟩ :=
    Copy.execute_stack (entryOffset := 0x5b24) pre state1
      (copy_xy_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (offset := 8) (by decide) rfl
      (Copy.stack_pre pre state1 (by decide) rfl rip1
        (stack_readable (frameOffset := 632) pre state1 (by decide) (offset := 232) (len := 32) (by decide))
        (by change RangeApart (stackPtr t1 + BitVec.ofNat 64 8) 32 (stackPtr t1 + BitVec.ofNat 64 232) 32
            rw [scalar_stack_address (frameOffset := 632) state1.rsp (by decide) (offset := 8) (by decide), scalar_stack_address (frameOffset := 632) state1.rsp (by decide) (offset := 232) (by decide)]
            exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (by decide)))
      (by change MontgomeryAt t1 (stackPtr t1 + BitVec.ofNat 64 232) _
          rw [scalar_stack_address (frameOffset := 632) state1.rsp (by decide) (offset := 232) (by decide)]
          exact mem1_stack400)
  have dest2 : (Operand.reg 4 : Operand 64).read t1 + 8 = stackPtr s - 624 :=
    scalar_stack_address (frameOffset := 632) state1.rsp (by decide) (by decide)
  rw [dest2] at value2 agrees2
  have mem2_stack112 : MontgomeryAt t2 (stackPtr s - 112) (values left right).bxz3 := copy_stack_stack pre agrees2 (by decide) (by decide) (by decide) (by decide) (by decide) mem1_stack112
  have mem2_stack272 : MontgomeryAt t2 (stackPtr s - 272) (values left right).yyPlus := copy_stack_stack pre agrees2 (by decide) (by decide) (by decide) (by decide) (by decide) mem1_stack272
  have mem2_stack304 : MontgomeryAt t2 (stackPtr s - 304) (values left right).yyMinus := copy_stack_stack pre agrees2 (by decide) (by decide) (by decide) (by decide) (by decide) mem1_stack304
  have mem2_stack368 : MontgomeryAt t2 (stackPtr s - 368) (values left right).yz := copy_stack_stack pre agrees2 (by decide) (by decide) (by decide) (by decide) (by decide) mem1_stack368
  have mem2_stack400 : MontgomeryAt t2 (stackPtr s - 400) (values left right).xy := copy_stack_stack pre agrees2 (by decide) (by decide) (by decide) (by decide) (by decide) mem1_stack400
  have mem2_stack432 : MontgomeryAt t2 (stackPtr s - 432) (values left right).xxMinus := copy_stack_stack pre agrees2 (by decide) (by decide) (by decide) (by decide) (by decide) mem1_stack432
  have mem2_stack592 : MontgomeryAt t2 (stackPtr s - 592) (values left right).yyPlus := copy_stack_stack pre agrees2 (by decide) (by decide) (by decide) (by decide) (by decide) value1
  have reg2_3 : t2.regValue .rbx = s.regValue .rdi := (agrees2.read (n := 64) (r := 3) (by simp [Copy32.components])).trans reg1_3
  have reg2_12 : t2.regValue .r12 = stackPtr s - 112 := (agrees2.read (n := 64) (r := 12) (by simp [Copy32.components])).trans reg1_12
  have reg2_13 : t2.regValue .r13 = stackPtr s - 432 := (agrees2.read (n := 64) (r := 13) (by simp [Copy32.components])).trans reg1_13
  obtain ⟨fuel3, t3, run3, state3, effect3, memory3⟩ :=
    execute_registers (offset := 0x5b58) state2 (yyPlusXY_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip2
      (by simp [yyPlusXYSetupEffect, Effect.components, Component.Covers])
      (by simp [yyPlusXYSetupEffect, Effect.components])
  have rip3 : t3.RIP = 0x105b6d := effect3.rip
  have reg3_2 : t3.regValue .rdx = stackPtr s - 624 := by
    have h := effect3.writes.1
    change t3.regValue .rdx = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state2.rsp (by decide) (by decide)
  have reg3_5 : t3.regValue .rbp = stackPtr s - 80 := by
    have h := effect3.writes.2.1
    change t3.regValue .rbp = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state2.rsp (by decide) (by decide)
  have reg3_6 : t3.regValue .rsi = stackPtr s - 592 := by
    have h := effect3.writes.2.2.1
    change t3.regValue .rsi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state2.rsp (by decide) (by decide)
  have reg3_7 : t3.regValue .rdi = stackPtr s - 80 := by
    have h := effect3.writes.2.2.2
    change t3.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state2.rsp (by decide) (by decide)
  have mem3_stack112 : MontgomeryAt t3 (stackPtr s - 112) (values left right).bxz3 := montgomery_external memory3 mem2_stack112
  have mem3_stack272 : MontgomeryAt t3 (stackPtr s - 272) (values left right).yyPlus := montgomery_external memory3 mem2_stack272
  have mem3_stack304 : MontgomeryAt t3 (stackPtr s - 304) (values left right).yyMinus := montgomery_external memory3 mem2_stack304
  have mem3_stack368 : MontgomeryAt t3 (stackPtr s - 368) (values left right).yz := montgomery_external memory3 mem2_stack368
  have mem3_stack400 : MontgomeryAt t3 (stackPtr s - 400) (values left right).xy := montgomery_external memory3 mem2_stack400
  have mem3_stack432 : MontgomeryAt t3 (stackPtr s - 432) (values left right).xxMinus := montgomery_external memory3 mem2_stack432
  have mem3_stack592 : MontgomeryAt t3 (stackPtr s - 592) (values left right).yyPlus := montgomery_external memory3 mem2_stack592
  have mem3_stack624 : MontgomeryAt t3 (stackPtr s - 624) (values left right).xy := montgomery_external memory3 value2
  have reg3_3 : t3.regValue .rbx = s.regValue .rdi := (effect3.agrees.read (n := 64) (r := 3) (by simp [yyPlusXYSetupEffect, Effect.components])).trans reg2_3
  have reg3_12 : t3.regValue .r12 = stackPtr s - 112 := (effect3.agrees.read (n := 64) (r := 12) (by simp [yyPlusXYSetupEffect, Effect.components])).trans reg2_12
  have reg3_13 : t3.regValue .r13 = stackPtr s - 432 := (effect3.agrees.read (n := 64) (r := 13) (by simp [yyPlusXYSetupEffect, Effect.components])).trans reg2_13
  obtain ⟨fuel4, t4, run4, state4, rip4, value4, saved4, kept4, frame4⟩ :=
    Call.binary_call (x := (values left right).yyPlus) (y := (values left right).xy) (op := fun x y => x * y % P256.Spec.Operations.domain.p) pre state3 Call.Sites.call_10381d
      (fun _ cp hx hy => P256.Proofs.Field.field_mul_correct cp hx hy)
      rip3 reg3_6 reg3_2 reg3_7 mem3_stack592 mem3_stack624
  have mem4_stack112 : MontgomeryAt t4 (stackPtr s - 112) (values left right).bxz3 := mem3_stack112.of_bytes_eq (fun i hi => (kept4 112 32 (by decide) (by decide) (by decide) i hi))
  have mem4_stack272 : MontgomeryAt t4 (stackPtr s - 272) (values left right).yyPlus := mem3_stack272.of_bytes_eq (fun i hi => (kept4 272 32 (by decide) (by decide) (by decide) i hi))
  have mem4_stack304 : MontgomeryAt t4 (stackPtr s - 304) (values left right).yyMinus := mem3_stack304.of_bytes_eq (fun i hi => (kept4 304 32 (by decide) (by decide) (by decide) i hi))
  have mem4_stack368 : MontgomeryAt t4 (stackPtr s - 368) (values left right).yz := mem3_stack368.of_bytes_eq (fun i hi => (kept4 368 32 (by decide) (by decide) (by decide) i hi))
  have mem4_stack400 : MontgomeryAt t4 (stackPtr s - 400) (values left right).xy := mem3_stack400.of_bytes_eq (fun i hi => (kept4 400 32 (by decide) (by decide) (by decide) i hi))
  have mem4_stack432 : MontgomeryAt t4 (stackPtr s - 432) (values left right).xxMinus := mem3_stack432.of_bytes_eq (fun i hi => (kept4 432 32 (by decide) (by decide) (by decide) i hi))
  have reg4_3 : t4.regValue .rbx = s.regValue .rdi := (saved4 .rbx (by simp)).trans reg3_3
  have reg4_5 : t4.regValue .rbp = stackPtr s - 80 := (saved4 .rbp (by simp)).trans reg3_5
  have reg4_12 : t4.regValue .r12 = stackPtr s - 112 := (saved4 .r12 (by simp)).trans reg3_12
  have reg4_13 : t4.regValue .r13 = stackPtr s - 432 := (saved4 .r13 (by simp)).trans reg3_13
  obtain ⟨fuel5, t5, run5, state5, rip5, value5, agrees5⟩ :=
    Copy.execute_stack (entryOffset := 0x5b72) pre state4
      (copy_yz_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (offset := 40) (by decide) rfl
      (Copy.stack_pre pre state4 (by decide) rfl rip4
        (stack_readable (frameOffset := 632) pre state4 (by decide) (offset := 264) (len := 32) (by decide))
        (by change RangeApart (stackPtr t4 + BitVec.ofNat 64 40) 32 (stackPtr t4 + BitVec.ofNat 64 264) 32
            rw [scalar_stack_address (frameOffset := 632) state4.rsp (by decide) (offset := 40) (by decide), scalar_stack_address (frameOffset := 632) state4.rsp (by decide) (offset := 264) (by decide)]
            exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (by decide)))
      (by change MontgomeryAt t4 (stackPtr t4 + BitVec.ofNat 64 264) _
          rw [scalar_stack_address (frameOffset := 632) state4.rsp (by decide) (offset := 264) (by decide)]
          exact mem4_stack368)
  have dest5 : (Operand.reg 4 : Operand 64).read t4 + 40 = stackPtr s - 592 :=
    scalar_stack_address (frameOffset := 632) state4.rsp (by decide) (by decide)
  rw [dest5] at value5 agrees5
  have mem5_stack80 : MontgomeryAt t5 (stackPtr s - 80) ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) := copy_stack_stack pre agrees5 (by decide) (by decide) (by decide) (by decide) (by decide) value4
  have mem5_stack112 : MontgomeryAt t5 (stackPtr s - 112) (values left right).bxz3 := copy_stack_stack pre agrees5 (by decide) (by decide) (by decide) (by decide) (by decide) mem4_stack112
  have mem5_stack272 : MontgomeryAt t5 (stackPtr s - 272) (values left right).yyPlus := copy_stack_stack pre agrees5 (by decide) (by decide) (by decide) (by decide) (by decide) mem4_stack272
  have mem5_stack304 : MontgomeryAt t5 (stackPtr s - 304) (values left right).yyMinus := copy_stack_stack pre agrees5 (by decide) (by decide) (by decide) (by decide) (by decide) mem4_stack304
  have mem5_stack368 : MontgomeryAt t5 (stackPtr s - 368) (values left right).yz := copy_stack_stack pre agrees5 (by decide) (by decide) (by decide) (by decide) (by decide) mem4_stack368
  have mem5_stack400 : MontgomeryAt t5 (stackPtr s - 400) (values left right).xy := copy_stack_stack pre agrees5 (by decide) (by decide) (by decide) (by decide) (by decide) mem4_stack400
  have mem5_stack432 : MontgomeryAt t5 (stackPtr s - 432) (values left right).xxMinus := copy_stack_stack pre agrees5 (by decide) (by decide) (by decide) (by decide) (by decide) mem4_stack432
  have reg5_3 : t5.regValue .rbx = s.regValue .rdi := (agrees5.read (n := 64) (r := 3) (by simp [Copy32.components])).trans reg4_3
  have reg5_5 : t5.regValue .rbp = stackPtr s - 80 := (agrees5.read (n := 64) (r := 5) (by simp [Copy32.components])).trans reg4_5
  have reg5_12 : t5.regValue .r12 = stackPtr s - 112 := (agrees5.read (n := 64) (r := 12) (by simp [Copy32.components])).trans reg4_12
  have reg5_13 : t5.regValue .r13 = stackPtr s - 432 := (agrees5.read (n := 64) (r := 13) (by simp [Copy32.components])).trans reg4_13
  obtain ⟨fuel6, t6, run6, state6, rip6, value6, agrees6⟩ :=
    Copy.execute_stack (entryOffset := 0x5ba6) pre state5
      (copy_bxz3_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (offset := 8) (by decide) rfl
      (Copy.stack_pre pre state5 (by decide) rfl rip5
        (stack_readable (frameOffset := 632) pre state5 (by decide) (offset := 520) (len := 32) (by decide))
        (by change RangeApart (stackPtr t5 + BitVec.ofNat 64 8) 32 (stackPtr t5 + BitVec.ofNat 64 520) 32
            rw [scalar_stack_address (frameOffset := 632) state5.rsp (by decide) (offset := 8) (by decide), scalar_stack_address (frameOffset := 632) state5.rsp (by decide) (offset := 520) (by decide)]
            exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (by decide)))
      (by change MontgomeryAt t5 (stackPtr t5 + BitVec.ofNat 64 520) _
          rw [scalar_stack_address (frameOffset := 632) state5.rsp (by decide) (offset := 520) (by decide)]
          exact mem5_stack112)
  have dest6 : (Operand.reg 4 : Operand 64).read t5 + 8 = stackPtr s - 624 :=
    scalar_stack_address (frameOffset := 632) state5.rsp (by decide) (by decide)
  rw [dest6] at value6 agrees6
  have mem6_stack80 : MontgomeryAt t6 (stackPtr s - 80) ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) := copy_stack_stack pre agrees6 (by decide) (by decide) (by decide) (by decide) (by decide) mem5_stack80
  have mem6_stack112 : MontgomeryAt t6 (stackPtr s - 112) (values left right).bxz3 := copy_stack_stack pre agrees6 (by decide) (by decide) (by decide) (by decide) (by decide) mem5_stack112
  have mem6_stack272 : MontgomeryAt t6 (stackPtr s - 272) (values left right).yyPlus := copy_stack_stack pre agrees6 (by decide) (by decide) (by decide) (by decide) (by decide) mem5_stack272
  have mem6_stack304 : MontgomeryAt t6 (stackPtr s - 304) (values left right).yyMinus := copy_stack_stack pre agrees6 (by decide) (by decide) (by decide) (by decide) (by decide) mem5_stack304
  have mem6_stack368 : MontgomeryAt t6 (stackPtr s - 368) (values left right).yz := copy_stack_stack pre agrees6 (by decide) (by decide) (by decide) (by decide) (by decide) mem5_stack368
  have mem6_stack400 : MontgomeryAt t6 (stackPtr s - 400) (values left right).xy := copy_stack_stack pre agrees6 (by decide) (by decide) (by decide) (by decide) (by decide) mem5_stack400
  have mem6_stack432 : MontgomeryAt t6 (stackPtr s - 432) (values left right).xxMinus := copy_stack_stack pre agrees6 (by decide) (by decide) (by decide) (by decide) (by decide) mem5_stack432
  have mem6_stack592 : MontgomeryAt t6 (stackPtr s - 592) (values left right).yz := copy_stack_stack pre agrees6 (by decide) (by decide) (by decide) (by decide) (by decide) value5
  have reg6_3 : t6.regValue .rbx = s.regValue .rdi := (agrees6.read (n := 64) (r := 3) (by simp [Copy32.components])).trans reg5_3
  have reg6_5 : t6.regValue .rbp = stackPtr s - 80 := (agrees6.read (n := 64) (r := 5) (by simp [Copy32.components])).trans reg5_5
  have reg6_12 : t6.regValue .r12 = stackPtr s - 112 := (agrees6.read (n := 64) (r := 12) (by simp [Copy32.components])).trans reg5_12
  have reg6_13 : t6.regValue .r13 = stackPtr s - 432 := (agrees6.read (n := 64) (r := 13) (by simp [Copy32.components])).trans reg5_13
  obtain ⟨fuel7, t7, run7, state7, effect7, memory7⟩ :=
    execute_registers (offset := 0x5bda) state6 (yzBXZ3_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip6
      (by simp [yzBXZ3SetupEffect, Effect.components, Component.Covers])
      (by simp [yzBXZ3SetupEffect, Effect.components])
  have rip7 : t7.RIP = 0x105bef := effect7.rip
  have reg7_2 : t7.regValue .rdx = stackPtr s - 624 := by
    have h := effect7.writes.1
    change t7.regValue .rdx = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state6.rsp (by decide) (by decide)
  have reg7_7 : t7.regValue .rdi = stackPtr s - 496 := by
    have h := effect7.writes.2.2.1
    change t7.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state6.rsp (by decide) (by decide)
  have reg7_14 : t7.regValue .r14 = stackPtr s - 496 := by
    have h := effect7.writes.2.2.2
    change t7.regValue .r14 = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state6.rsp (by decide) (by decide)
  have reg7_6 : t7.regValue .rsi = stackPtr s - 592 := by
    have h := effect7.writes.2.1
    change t7.regValue .rsi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state6.rsp (by decide) (by decide)
  have mem7_stack80 : MontgomeryAt t7 (stackPtr s - 80) ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) := montgomery_external memory7 mem6_stack80
  have mem7_stack112 : MontgomeryAt t7 (stackPtr s - 112) (values left right).bxz3 := montgomery_external memory7 mem6_stack112
  have mem7_stack272 : MontgomeryAt t7 (stackPtr s - 272) (values left right).yyPlus := montgomery_external memory7 mem6_stack272
  have mem7_stack304 : MontgomeryAt t7 (stackPtr s - 304) (values left right).yyMinus := montgomery_external memory7 mem6_stack304
  have mem7_stack368 : MontgomeryAt t7 (stackPtr s - 368) (values left right).yz := montgomery_external memory7 mem6_stack368
  have mem7_stack400 : MontgomeryAt t7 (stackPtr s - 400) (values left right).xy := montgomery_external memory7 mem6_stack400
  have mem7_stack432 : MontgomeryAt t7 (stackPtr s - 432) (values left right).xxMinus := montgomery_external memory7 mem6_stack432
  have mem7_stack592 : MontgomeryAt t7 (stackPtr s - 592) (values left right).yz := montgomery_external memory7 mem6_stack592
  have mem7_stack624 : MontgomeryAt t7 (stackPtr s - 624) (values left right).bxz3 := montgomery_external memory7 value6
  have reg7_3 : t7.regValue .rbx = s.regValue .rdi := (effect7.agrees.read (n := 64) (r := 3) (by simp [yzBXZ3SetupEffect, Effect.components])).trans reg6_3
  have reg7_5 : t7.regValue .rbp = stackPtr s - 80 := (effect7.agrees.read (n := 64) (r := 5) (by simp [yzBXZ3SetupEffect, Effect.components])).trans reg6_5
  have reg7_12 : t7.regValue .r12 = stackPtr s - 112 := (effect7.agrees.read (n := 64) (r := 12) (by simp [yzBXZ3SetupEffect, Effect.components])).trans reg6_12
  have reg7_13 : t7.regValue .r13 = stackPtr s - 432 := (effect7.agrees.read (n := 64) (r := 13) (by simp [yzBXZ3SetupEffect, Effect.components])).trans reg6_13
  obtain ⟨fuel8, t8, run8, state8, rip8, value8, saved8, kept8, frame8⟩ :=
    Call.binary_call (x := (values left right).yz) (y := (values left right).bxz3) (op := fun x y => x * y % P256.Spec.Operations.domain.p) pre state7 Call.Sites.call_10389f
      (fun _ cp hx hy => P256.Proofs.Field.field_mul_correct cp hx hy)
      rip7 reg7_6 reg7_2 reg7_7 mem7_stack592 mem7_stack624
  have mem8_stack80 : MontgomeryAt t8 (stackPtr s - 80) ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) := mem7_stack80.of_bytes_eq (fun i hi => (kept8 80 32 (by decide) (by decide) (by decide) i hi))
  have mem8_stack112 : MontgomeryAt t8 (stackPtr s - 112) (values left right).bxz3 := mem7_stack112.of_bytes_eq (fun i hi => (kept8 112 32 (by decide) (by decide) (by decide) i hi))
  have mem8_stack272 : MontgomeryAt t8 (stackPtr s - 272) (values left right).yyPlus := mem7_stack272.of_bytes_eq (fun i hi => (kept8 272 32 (by decide) (by decide) (by decide) i hi))
  have mem8_stack304 : MontgomeryAt t8 (stackPtr s - 304) (values left right).yyMinus := mem7_stack304.of_bytes_eq (fun i hi => (kept8 304 32 (by decide) (by decide) (by decide) i hi))
  have mem8_stack368 : MontgomeryAt t8 (stackPtr s - 368) (values left right).yz := mem7_stack368.of_bytes_eq (fun i hi => (kept8 368 32 (by decide) (by decide) (by decide) i hi))
  have mem8_stack400 : MontgomeryAt t8 (stackPtr s - 400) (values left right).xy := mem7_stack400.of_bytes_eq (fun i hi => (kept8 400 32 (by decide) (by decide) (by decide) i hi))
  have mem8_stack432 : MontgomeryAt t8 (stackPtr s - 432) (values left right).xxMinus := mem7_stack432.of_bytes_eq (fun i hi => (kept8 432 32 (by decide) (by decide) (by decide) i hi))
  have reg8_3 : t8.regValue .rbx = s.regValue .rdi := (saved8 .rbx (by simp)).trans reg7_3
  have reg8_5 : t8.regValue .rbp = stackPtr s - 80 := (saved8 .rbp (by simp)).trans reg7_5
  have reg8_12 : t8.regValue .r12 = stackPtr s - 112 := (saved8 .r12 (by simp)).trans reg7_12
  have reg8_13 : t8.regValue .r13 = stackPtr s - 432 := (saved8 .r13 (by simp)).trans reg7_13
  have reg8_14 : t8.regValue .r14 = stackPtr s - 496 := (saved8 .r14 (by simp)).trans reg7_14
  obtain ⟨fuel9, t9, run9, state9, effect9, memory9⟩ :=
    execute_registers (offset := 0x5bf4) state8 (x_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip8
      (by simp [xSetupEffect, Effect.components, Component.Covers])
      (by simp [xSetupEffect, Effect.components])
  have rip9 : t9.RIP = 0x105bff := effect9.rip
  have reg9_2 : t9.regValue .rdx = stackPtr s - 496 := by
    have h := effect9.writes.1
    change t9.regValue .rdx = _ at h
    rw [h]
    exact reg8_14
  have reg9_6 : t9.regValue .rsi = stackPtr s - 80 := by
    have h := effect9.writes.2.1
    change t9.regValue .rsi = _ at h
    rw [h]
    exact reg8_5
  have reg9_7 : t9.regValue .rdi = stackPtr s - 624 := by
    have h := effect9.writes.2.2
    change t9.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state8.rsp (by decide) (by decide)
  have mem9_stack80 : MontgomeryAt t9 (stackPtr s - 80) ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) := montgomery_external memory9 mem8_stack80
  have mem9_stack112 : MontgomeryAt t9 (stackPtr s - 112) (values left right).bxz3 := montgomery_external memory9 mem8_stack112
  have mem9_stack272 : MontgomeryAt t9 (stackPtr s - 272) (values left right).yyPlus := montgomery_external memory9 mem8_stack272
  have mem9_stack304 : MontgomeryAt t9 (stackPtr s - 304) (values left right).yyMinus := montgomery_external memory9 mem8_stack304
  have mem9_stack368 : MontgomeryAt t9 (stackPtr s - 368) (values left right).yz := montgomery_external memory9 mem8_stack368
  have mem9_stack400 : MontgomeryAt t9 (stackPtr s - 400) (values left right).xy := montgomery_external memory9 mem8_stack400
  have mem9_stack432 : MontgomeryAt t9 (stackPtr s - 432) (values left right).xxMinus := montgomery_external memory9 mem8_stack432
  have mem9_stack496 : MontgomeryAt t9 (stackPtr s - 496) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p) := montgomery_external memory9 value8
  have reg9_3 : t9.regValue .rbx = s.regValue .rdi := (effect9.agrees.read (n := 64) (r := 3) (by simp [xSetupEffect, Effect.components])).trans reg8_3
  have reg9_12 : t9.regValue .r12 = stackPtr s - 112 := (effect9.agrees.read (n := 64) (r := 12) (by simp [xSetupEffect, Effect.components])).trans reg8_12
  have reg9_13 : t9.regValue .r13 = stackPtr s - 432 := (effect9.agrees.read (n := 64) (r := 13) (by simp [xSetupEffect, Effect.components])).trans reg8_13
  obtain ⟨fuel10, t10, run10, state10, rip10, value10, saved10, kept10, frame10⟩ :=
    Call.binary_call (x := ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p)) (y := ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) (op := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p) pre state9 Call.Sites.call_1038af
      (fun _ cp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct cp hx hy)
      rip9 reg9_6 reg9_2 reg9_7 mem9_stack80 mem9_stack496
  have mem10_stack112 : MontgomeryAt t10 (stackPtr s - 112) (values left right).bxz3 := mem9_stack112.of_bytes_eq (fun i hi => (kept10 112 32 (by decide) (by decide) (by decide) i hi))
  have mem10_stack272 : MontgomeryAt t10 (stackPtr s - 272) (values left right).yyPlus := mem9_stack272.of_bytes_eq (fun i hi => (kept10 272 32 (by decide) (by decide) (by decide) i hi))
  have mem10_stack304 : MontgomeryAt t10 (stackPtr s - 304) (values left right).yyMinus := mem9_stack304.of_bytes_eq (fun i hi => (kept10 304 32 (by decide) (by decide) (by decide) i hi))
  have mem10_stack368 : MontgomeryAt t10 (stackPtr s - 368) (values left right).yz := mem9_stack368.of_bytes_eq (fun i hi => (kept10 368 32 (by decide) (by decide) (by decide) i hi))
  have mem10_stack400 : MontgomeryAt t10 (stackPtr s - 400) (values left right).xy := mem9_stack400.of_bytes_eq (fun i hi => (kept10 400 32 (by decide) (by decide) (by decide) i hi))
  have mem10_stack432 : MontgomeryAt t10 (stackPtr s - 432) (values left right).xxMinus := mem9_stack432.of_bytes_eq (fun i hi => (kept10 432 32 (by decide) (by decide) (by decide) i hi))
  have reg10_3 : t10.regValue .rbx = s.regValue .rdi := (saved10 .rbx (by simp)).trans reg9_3
  have reg10_12 : t10.regValue .r12 = stackPtr s - 112 := (saved10 .r12 (by simp)).trans reg9_12
  have reg10_13 : t10.regValue .r13 = stackPtr s - 432 := (saved10 .r13 (by simp)).trans reg9_13
  obtain ⟨fuel11, t11, run11, state11, rip11, value11, agrees11⟩ :=
    execute_output (entryOffset := 0x5c04) pre state10
      (copy_x_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (off := 0) (srcOff := 8) (by decide) (by decide) rfl
      (by change t10.regValue .rbx + 0 = _; rw [reg10_3]; rfl) rip10
      (by change MontgomeryAt t10 (stackPtr t10 + BitVec.ofNat 64 8) _
          rw [scalar_stack_address (frameOffset := 632) state10.rsp (by decide) (offset := 8) (by decide)]
          exact value10)
  have dest11 : (Operand.reg 3 : Operand 64).read t10 + 0 = s.regValue .rdi + 0 :=
    congrArg (· + 0) reg10_3
  rw [dest11] at value11 agrees11
  have mem11_stack112 : MontgomeryAt t11 (stackPtr s - 112) (values left right).bxz3 := copy_output_stack pre agrees11 (by decide) (by decide) (by decide) mem10_stack112
  have mem11_stack272 : MontgomeryAt t11 (stackPtr s - 272) (values left right).yyPlus := copy_output_stack pre agrees11 (by decide) (by decide) (by decide) mem10_stack272
  have mem11_stack304 : MontgomeryAt t11 (stackPtr s - 304) (values left right).yyMinus := copy_output_stack pre agrees11 (by decide) (by decide) (by decide) mem10_stack304
  have mem11_stack368 : MontgomeryAt t11 (stackPtr s - 368) (values left right).yz := copy_output_stack pre agrees11 (by decide) (by decide) (by decide) mem10_stack368
  have mem11_stack400 : MontgomeryAt t11 (stackPtr s - 400) (values left right).xy := copy_output_stack pre agrees11 (by decide) (by decide) (by decide) mem10_stack400
  have mem11_stack432 : MontgomeryAt t11 (stackPtr s - 432) (values left right).xxMinus := copy_output_stack pre agrees11 (by decide) (by decide) (by decide) mem10_stack432
  have reg11_3 : t11.regValue .rbx = s.regValue .rdi := (agrees11.read (n := 64) (r := 3) (by simp [Copy32.components])).trans reg10_3
  have reg11_12 : t11.regValue .r12 = stackPtr s - 112 := (agrees11.read (n := 64) (r := 12) (by simp [Copy32.components])).trans reg10_12
  have reg11_13 : t11.regValue .r13 = stackPtr s - 432 := (agrees11.read (n := 64) (r := 13) (by simp [Copy32.components])).trans reg10_13
  obtain ⟨fuel12, t12, run12, state12, rip12, value12, agrees12⟩ :=
    Copy.execute_stack (entryOffset := 0x5c27) pre state11
      (copy_yy_minus_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (offset := 8) (by decide) rfl
      (Copy.stack_pre pre state11 (by decide) rfl rip11
        (stack_readable (frameOffset := 632) pre state11 (by decide) (offset := 328) (len := 32) (by decide))
        (by change RangeApart (stackPtr t11 + BitVec.ofNat 64 8) 32 (stackPtr t11 + BitVec.ofNat 64 328) 32
            rw [scalar_stack_address (frameOffset := 632) state11.rsp (by decide) (offset := 8) (by decide), scalar_stack_address (frameOffset := 632) state11.rsp (by decide) (offset := 328) (by decide)]
            exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (by decide)))
      (by change MontgomeryAt t11 (stackPtr t11 + BitVec.ofNat 64 328) _
          rw [scalar_stack_address (frameOffset := 632) state11.rsp (by decide) (offset := 328) (by decide)]
          exact mem11_stack304)
  have dest12 : (Operand.reg 4 : Operand 64).read t11 + 8 = stackPtr s - 624 :=
    scalar_stack_address (frameOffset := 632) state11.rsp (by decide) (by decide)
  rw [dest12] at value12 agrees12
  have mem12_output0 : MontgomeryAt t12 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := copy_stack_output pre agrees12 (by decide) (by decide) (by decide) value11
  have mem12_stack112 : MontgomeryAt t12 (stackPtr s - 112) (values left right).bxz3 := copy_stack_stack pre agrees12 (by decide) (by decide) (by decide) (by decide) (by decide) mem11_stack112
  have mem12_stack272 : MontgomeryAt t12 (stackPtr s - 272) (values left right).yyPlus := copy_stack_stack pre agrees12 (by decide) (by decide) (by decide) (by decide) (by decide) mem11_stack272
  have mem12_stack304 : MontgomeryAt t12 (stackPtr s - 304) (values left right).yyMinus := copy_stack_stack pre agrees12 (by decide) (by decide) (by decide) (by decide) (by decide) mem11_stack304
  have mem12_stack368 : MontgomeryAt t12 (stackPtr s - 368) (values left right).yz := copy_stack_stack pre agrees12 (by decide) (by decide) (by decide) (by decide) (by decide) mem11_stack368
  have mem12_stack400 : MontgomeryAt t12 (stackPtr s - 400) (values left right).xy := copy_stack_stack pre agrees12 (by decide) (by decide) (by decide) (by decide) (by decide) mem11_stack400
  have mem12_stack432 : MontgomeryAt t12 (stackPtr s - 432) (values left right).xxMinus := copy_stack_stack pre agrees12 (by decide) (by decide) (by decide) (by decide) (by decide) mem11_stack432
  have reg12_3 : t12.regValue .rbx = s.regValue .rdi := (agrees12.read (n := 64) (r := 3) (by simp [Copy32.components])).trans reg11_3
  have reg12_12 : t12.regValue .r12 = stackPtr s - 112 := (agrees12.read (n := 64) (r := 12) (by simp [Copy32.components])).trans reg11_12
  have reg12_13 : t12.regValue .r13 = stackPtr s - 432 := (agrees12.read (n := 64) (r := 13) (by simp [Copy32.components])).trans reg11_13
  obtain ⟨fuel13, t13, run13, state13, effect13, memory13⟩ :=
    execute_registers (offset := 0x5c5b) state12 (yyPlusMinus_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip12
      (by simp [yyPlusMinusSetupEffect, Effect.components, Component.Covers])
      (by simp [yyPlusMinusSetupEffect, Effect.components])
  have rip13 : t13.RIP = 0x105c73 := effect13.rip
  have reg13_2 : t13.regValue .rdx = stackPtr s - 624 := by
    have h := effect13.writes.1
    change t13.regValue .rdx = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state12.rsp (by decide) (by decide)
  have reg13_6 : t13.regValue .rsi = stackPtr s - 272 := by
    have h := effect13.writes.2.1
    change t13.regValue .rsi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state12.rsp (by decide) (by decide)
  have reg13_14 : t13.regValue .r14 = stackPtr s - 496 := by
    have h := effect13.writes.2.2.2
    change t13.regValue .r14 = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state12.rsp (by decide) (by decide)
  have reg13_7 : t13.regValue .rdi = stackPtr s - 496 := by
    have h := effect13.writes.2.2.1
    change t13.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state12.rsp (by decide) (by decide)
  have mem13_output0 : MontgomeryAt t13 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := montgomery_external memory13 mem12_output0
  have mem13_stack112 : MontgomeryAt t13 (stackPtr s - 112) (values left right).bxz3 := montgomery_external memory13 mem12_stack112
  have mem13_stack272 : MontgomeryAt t13 (stackPtr s - 272) (values left right).yyPlus := montgomery_external memory13 mem12_stack272
  have mem13_stack304 : MontgomeryAt t13 (stackPtr s - 304) (values left right).yyMinus := montgomery_external memory13 mem12_stack304
  have mem13_stack368 : MontgomeryAt t13 (stackPtr s - 368) (values left right).yz := montgomery_external memory13 mem12_stack368
  have mem13_stack400 : MontgomeryAt t13 (stackPtr s - 400) (values left right).xy := montgomery_external memory13 mem12_stack400
  have mem13_stack432 : MontgomeryAt t13 (stackPtr s - 432) (values left right).xxMinus := montgomery_external memory13 mem12_stack432
  have mem13_stack624 : MontgomeryAt t13 (stackPtr s - 624) (values left right).yyMinus := montgomery_external memory13 value12
  have reg13_3 : t13.regValue .rbx = s.regValue .rdi := (effect13.agrees.read (n := 64) (r := 3) (by simp [yyPlusMinusSetupEffect, Effect.components])).trans reg12_3
  have reg13_12 : t13.regValue .r12 = stackPtr s - 112 := (effect13.agrees.read (n := 64) (r := 12) (by simp [yyPlusMinusSetupEffect, Effect.components])).trans reg12_12
  have reg13_13 : t13.regValue .r13 = stackPtr s - 432 := (effect13.agrees.read (n := 64) (r := 13) (by simp [yyPlusMinusSetupEffect, Effect.components])).trans reg12_13
  obtain ⟨fuel14, t14, run14, state14, rip14, value14, saved14, kept14, frame14⟩ :=
    Call.binary_call (x := (values left right).yyPlus) (y := (values left right).yyMinus) (op := fun x y => x * y % P256.Spec.Operations.domain.p) pre state13 Call.Sites.call_103923
      (fun _ cp hx hy => P256.Proofs.Field.field_mul_correct cp hx hy)
      rip13 reg13_6 reg13_2 reg13_7 mem13_stack272 mem13_stack624
  have mem14_output0 : MontgomeryAt t14 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := preserve_output_work pre frame14 (by decide) mem13_output0
  have mem14_stack112 : MontgomeryAt t14 (stackPtr s - 112) (values left right).bxz3 := mem13_stack112.of_bytes_eq (fun i hi => (kept14 112 32 (by decide) (by decide) (by decide) i hi))
  have mem14_stack304 : MontgomeryAt t14 (stackPtr s - 304) (values left right).yyMinus := mem13_stack304.of_bytes_eq (fun i hi => (kept14 304 32 (by decide) (by decide) (by decide) i hi))
  have mem14_stack368 : MontgomeryAt t14 (stackPtr s - 368) (values left right).yz := mem13_stack368.of_bytes_eq (fun i hi => (kept14 368 32 (by decide) (by decide) (by decide) i hi))
  have mem14_stack400 : MontgomeryAt t14 (stackPtr s - 400) (values left right).xy := mem13_stack400.of_bytes_eq (fun i hi => (kept14 400 32 (by decide) (by decide) (by decide) i hi))
  have mem14_stack432 : MontgomeryAt t14 (stackPtr s - 432) (values left right).xxMinus := mem13_stack432.of_bytes_eq (fun i hi => (kept14 432 32 (by decide) (by decide) (by decide) i hi))
  have reg14_3 : t14.regValue .rbx = s.regValue .rdi := (saved14 .rbx (by simp)).trans reg13_3
  have reg14_12 : t14.regValue .r12 = stackPtr s - 112 := (saved14 .r12 (by simp)).trans reg13_12
  have reg14_13 : t14.regValue .r13 = stackPtr s - 432 := (saved14 .r13 (by simp)).trans reg13_13
  have reg14_14 : t14.regValue .r14 = stackPtr s - 496 := (saved14 .r14 (by simp)).trans reg13_14
  obtain ⟨fuel15, t15, run15, state15, rip15, value15, agrees15⟩ :=
    Copy.execute_stack (entryOffset := 0x5c78) pre state14
      (copy_xx_minus_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (offset := 8) (by decide) rfl
      (Copy.stack_pre pre state14 (by decide) rfl rip14
        (stack_readable (frameOffset := 632) pre state14 (by decide) (offset := 200) (len := 32) (by decide))
        (by change RangeApart (stackPtr t14 + BitVec.ofNat 64 8) 32 (stackPtr t14 + BitVec.ofNat 64 200) 32
            rw [scalar_stack_address (frameOffset := 632) state14.rsp (by decide) (offset := 8) (by decide), scalar_stack_address (frameOffset := 632) state14.rsp (by decide) (offset := 200) (by decide)]
            exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (by decide)))
      (by change MontgomeryAt t14 (stackPtr t14 + BitVec.ofNat 64 200) _
          rw [scalar_stack_address (frameOffset := 632) state14.rsp (by decide) (offset := 200) (by decide)]
          exact mem14_stack432)
  have dest15 : (Operand.reg 4 : Operand 64).read t14 + 8 = stackPtr s - 624 :=
    scalar_stack_address (frameOffset := 632) state14.rsp (by decide) (by decide)
  rw [dest15] at value15 agrees15
  have mem15_output0 : MontgomeryAt t15 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := copy_stack_output pre agrees15 (by decide) (by decide) (by decide) mem14_output0
  have mem15_stack112 : MontgomeryAt t15 (stackPtr s - 112) (values left right).bxz3 := copy_stack_stack pre agrees15 (by decide) (by decide) (by decide) (by decide) (by decide) mem14_stack112
  have mem15_stack304 : MontgomeryAt t15 (stackPtr s - 304) (values left right).yyMinus := copy_stack_stack pre agrees15 (by decide) (by decide) (by decide) (by decide) (by decide) mem14_stack304
  have mem15_stack368 : MontgomeryAt t15 (stackPtr s - 368) (values left right).yz := copy_stack_stack pre agrees15 (by decide) (by decide) (by decide) (by decide) (by decide) mem14_stack368
  have mem15_stack400 : MontgomeryAt t15 (stackPtr s - 400) (values left right).xy := copy_stack_stack pre agrees15 (by decide) (by decide) (by decide) (by decide) (by decide) mem14_stack400
  have mem15_stack432 : MontgomeryAt t15 (stackPtr s - 432) (values left right).xxMinus := copy_stack_stack pre agrees15 (by decide) (by decide) (by decide) (by decide) (by decide) mem14_stack432
  have mem15_stack496 : MontgomeryAt t15 (stackPtr s - 496) ((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) := copy_stack_stack pre agrees15 (by decide) (by decide) (by decide) (by decide) (by decide) value14
  have reg15_3 : t15.regValue .rbx = s.regValue .rdi := (agrees15.read (n := 64) (r := 3) (by simp [Copy32.components])).trans reg14_3
  have reg15_12 : t15.regValue .r12 = stackPtr s - 112 := (agrees15.read (n := 64) (r := 12) (by simp [Copy32.components])).trans reg14_12
  have reg15_13 : t15.regValue .r13 = stackPtr s - 432 := (agrees15.read (n := 64) (r := 13) (by simp [Copy32.components])).trans reg14_13
  have reg15_14 : t15.regValue .r14 = stackPtr s - 496 := (agrees15.read (n := 64) (r := 14) (by simp [Copy32.components])).trans reg14_14
  obtain ⟨fuel16, t16, run16, state16, effect16, memory16⟩ :=
    execute_registers (offset := 0x5cac) state15 (xxMinusBXZ3_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip15
      (by simp [xxMinusBXZ3SetupEffect, Effect.components, Component.Covers])
      (by simp [xxMinusBXZ3SetupEffect, Effect.components])
  have rip16 : t16.RIP = 0x105cbc := effect16.rip
  have reg16_2 : t16.regValue .rdx = stackPtr s - 112 := by
    have h := effect16.writes.1
    change t16.regValue .rdx = _ at h
    rw [h]
    exact reg15_12
  have reg16_7 : t16.regValue .rdi = stackPtr s - 592 := by
    have h := effect16.writes.2.2.1
    change t16.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state15.rsp (by decide) (by decide)
  have reg16_6 : t16.regValue .rsi = stackPtr s - 624 := by
    have h := effect16.writes.2.1
    change t16.regValue .rsi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state15.rsp (by decide) (by decide)
  have reg16_15 : t16.regValue .r15 = stackPtr s - 592 := by
    have h := effect16.writes.2.2.2
    change t16.regValue .r15 = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state15.rsp (by decide) (by decide)
  have mem16_output0 : MontgomeryAt t16 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := montgomery_external memory16 mem15_output0
  have mem16_stack112 : MontgomeryAt t16 (stackPtr s - 112) (values left right).bxz3 := montgomery_external memory16 mem15_stack112
  have mem16_stack304 : MontgomeryAt t16 (stackPtr s - 304) (values left right).yyMinus := montgomery_external memory16 mem15_stack304
  have mem16_stack368 : MontgomeryAt t16 (stackPtr s - 368) (values left right).yz := montgomery_external memory16 mem15_stack368
  have mem16_stack400 : MontgomeryAt t16 (stackPtr s - 400) (values left right).xy := montgomery_external memory16 mem15_stack400
  have mem16_stack432 : MontgomeryAt t16 (stackPtr s - 432) (values left right).xxMinus := montgomery_external memory16 mem15_stack432
  have mem16_stack496 : MontgomeryAt t16 (stackPtr s - 496) ((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) := montgomery_external memory16 mem15_stack496
  have mem16_stack624 : MontgomeryAt t16 (stackPtr s - 624) (values left right).xxMinus := montgomery_external memory16 value15
  have reg16_3 : t16.regValue .rbx = s.regValue .rdi := (effect16.agrees.read (n := 64) (r := 3) (by simp [xxMinusBXZ3SetupEffect, Effect.components])).trans reg15_3
  have reg16_13 : t16.regValue .r13 = stackPtr s - 432 := (effect16.agrees.read (n := 64) (r := 13) (by simp [xxMinusBXZ3SetupEffect, Effect.components])).trans reg15_13
  have reg16_14 : t16.regValue .r14 = stackPtr s - 496 := (effect16.agrees.read (n := 64) (r := 14) (by simp [xxMinusBXZ3SetupEffect, Effect.components])).trans reg15_14
  obtain ⟨fuel17, t17, run17, state17, rip17, value17, saved17, kept17, frame17⟩ :=
    Call.binary_call (x := (values left right).xxMinus) (y := (values left right).bxz3) (op := fun x y => x * y % P256.Spec.Operations.domain.p) pre state16 Call.Sites.call_10396c
      (fun _ cp hx hy => P256.Proofs.Field.field_mul_correct cp hx hy)
      rip16 reg16_6 reg16_2 reg16_7 mem16_stack624 mem16_stack112
  have mem17_output0 : MontgomeryAt t17 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := preserve_output_work pre frame17 (by decide) mem16_output0
  have mem17_stack304 : MontgomeryAt t17 (stackPtr s - 304) (values left right).yyMinus := mem16_stack304.of_bytes_eq (fun i hi => (kept17 304 32 (by decide) (by decide) (by decide) i hi))
  have mem17_stack368 : MontgomeryAt t17 (stackPtr s - 368) (values left right).yz := mem16_stack368.of_bytes_eq (fun i hi => (kept17 368 32 (by decide) (by decide) (by decide) i hi))
  have mem17_stack400 : MontgomeryAt t17 (stackPtr s - 400) (values left right).xy := mem16_stack400.of_bytes_eq (fun i hi => (kept17 400 32 (by decide) (by decide) (by decide) i hi))
  have mem17_stack432 : MontgomeryAt t17 (stackPtr s - 432) (values left right).xxMinus := mem16_stack432.of_bytes_eq (fun i hi => (kept17 432 32 (by decide) (by decide) (by decide) i hi))
  have mem17_stack496 : MontgomeryAt t17 (stackPtr s - 496) ((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) := mem16_stack496.of_bytes_eq (fun i hi => (kept17 496 32 (by decide) (by decide) (by decide) i hi))
  have reg17_3 : t17.regValue .rbx = s.regValue .rdi := (saved17 .rbx (by simp)).trans reg16_3
  have reg17_13 : t17.regValue .r13 = stackPtr s - 432 := (saved17 .r13 (by simp)).trans reg16_13
  have reg17_14 : t17.regValue .r14 = stackPtr s - 496 := (saved17 .r14 (by simp)).trans reg16_14
  have reg17_15 : t17.regValue .r15 = stackPtr s - 592 := (saved17 .r15 (by simp)).trans reg16_15
  obtain ⟨fuel18, t18, run18, state18, effect18, memory18⟩ :=
    execute_registers (offset := 0x5cc1) state17 (y_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip17
      (by simp [ySetupEffect, Effect.components, Component.Covers])
      (by simp [ySetupEffect, Effect.components])
  have rip18 : t18.RIP = 0x105ccc := effect18.rip
  have reg18_2 : t18.regValue .rdx = stackPtr s - 592 := by
    have h := effect18.writes.1
    change t18.regValue .rdx = _ at h
    rw [h]
    exact reg17_15
  have reg18_6 : t18.regValue .rsi = stackPtr s - 496 := by
    have h := effect18.writes.2.1
    change t18.regValue .rsi = _ at h
    rw [h]
    exact reg17_14
  have reg18_7 : t18.regValue .rdi = stackPtr s - 624 := by
    have h := effect18.writes.2.2
    change t18.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state17.rsp (by decide) (by decide)
  have mem18_output0 : MontgomeryAt t18 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := montgomery_external memory18 mem17_output0
  have mem18_stack304 : MontgomeryAt t18 (stackPtr s - 304) (values left right).yyMinus := montgomery_external memory18 mem17_stack304
  have mem18_stack368 : MontgomeryAt t18 (stackPtr s - 368) (values left right).yz := montgomery_external memory18 mem17_stack368
  have mem18_stack400 : MontgomeryAt t18 (stackPtr s - 400) (values left right).xy := montgomery_external memory18 mem17_stack400
  have mem18_stack432 : MontgomeryAt t18 (stackPtr s - 432) (values left right).xxMinus := montgomery_external memory18 mem17_stack432
  have mem18_stack496 : MontgomeryAt t18 (stackPtr s - 496) ((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) := montgomery_external memory18 mem17_stack496
  have mem18_stack592 : MontgomeryAt t18 (stackPtr s - 592) ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p) := montgomery_external memory18 value17
  have reg18_3 : t18.regValue .rbx = s.regValue .rdi := (effect18.agrees.read (n := 64) (r := 3) (by simp [ySetupEffect, Effect.components])).trans reg17_3
  have reg18_13 : t18.regValue .r13 = stackPtr s - 432 := (effect18.agrees.read (n := 64) (r := 13) (by simp [ySetupEffect, Effect.components])).trans reg17_13
  obtain ⟨fuel19, t19, run19, state19, rip19, value19, saved19, kept19, frame19⟩ :=
    Call.binary_call (x := ((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p)) (y := ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p)) (op := fun x y => (x+y) % P256.Spec.Operations.domain.p) pre state18 Call.Sites.call_10397c
      (fun _ cp hx hy => P256.Proofs.Field.field_add_correct cp hx hy)
      rip18 reg18_6 reg18_2 reg18_7 mem18_stack496 mem18_stack592
  have mem19_output0 : MontgomeryAt t19 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := preserve_output_work pre frame19 (by decide) mem18_output0
  have mem19_stack304 : MontgomeryAt t19 (stackPtr s - 304) (values left right).yyMinus := mem18_stack304.of_bytes_eq (fun i hi => (kept19 304 32 (by decide) (by decide) (by decide) i hi))
  have mem19_stack368 : MontgomeryAt t19 (stackPtr s - 368) (values left right).yz := mem18_stack368.of_bytes_eq (fun i hi => (kept19 368 32 (by decide) (by decide) (by decide) i hi))
  have mem19_stack400 : MontgomeryAt t19 (stackPtr s - 400) (values left right).xy := mem18_stack400.of_bytes_eq (fun i hi => (kept19 400 32 (by decide) (by decide) (by decide) i hi))
  have mem19_stack432 : MontgomeryAt t19 (stackPtr s - 432) (values left right).xxMinus := mem18_stack432.of_bytes_eq (fun i hi => (kept19 432 32 (by decide) (by decide) (by decide) i hi))
  have reg19_3 : t19.regValue .rbx = s.regValue .rdi := (saved19 .rbx (by simp)).trans reg18_3
  have reg19_13 : t19.regValue .r13 = stackPtr s - 432 := (saved19 .r13 (by simp)).trans reg18_13
  obtain ⟨fuel20, t20, run20, state20, rip20, value20, agrees20⟩ :=
    execute_output (entryOffset := 0x5cd1) pre state19
      (copy_y_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (off := 32) (srcOff := 8) (by decide) (by decide) rfl
      (by change t19.regValue .rbx + 32 = _; rw [reg19_3]; rfl) rip19
      (by change MontgomeryAt t19 (stackPtr t19 + BitVec.ofNat 64 8) _
          rw [scalar_stack_address (frameOffset := 632) state19.rsp (by decide) (offset := 8) (by decide)]
          exact value19)
  have dest20 : (Operand.reg 3 : Operand 64).read t19 + 32 = s.regValue .rdi + 32 :=
    congrArg (· + 32) reg19_3
  rw [dest20] at value20 agrees20
  have mem20_output0 : MontgomeryAt t20 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := copy_output_output pre agrees20 (by decide) (by decide) (by decide) mem19_output0
  have mem20_stack304 : MontgomeryAt t20 (stackPtr s - 304) (values left right).yyMinus := copy_output_stack pre agrees20 (by decide) (by decide) (by decide) mem19_stack304
  have mem20_stack368 : MontgomeryAt t20 (stackPtr s - 368) (values left right).yz := copy_output_stack pre agrees20 (by decide) (by decide) (by decide) mem19_stack368
  have mem20_stack400 : MontgomeryAt t20 (stackPtr s - 400) (values left right).xy := copy_output_stack pre agrees20 (by decide) (by decide) (by decide) mem19_stack400
  have mem20_stack432 : MontgomeryAt t20 (stackPtr s - 432) (values left right).xxMinus := copy_output_stack pre agrees20 (by decide) (by decide) (by decide) mem19_stack432
  have reg20_3 : t20.regValue .rbx = s.regValue .rdi := (agrees20.read (n := 64) (r := 3) (by simp [Copy32.components])).trans reg19_3
  have reg20_13 : t20.regValue .r13 = stackPtr s - 432 := (agrees20.read (n := 64) (r := 13) (by simp [Copy32.components])).trans reg19_13
  obtain ⟨fuel21, t21, run21, state21, effect21, memory21⟩ :=
    execute_registers (offset := 0x5cf5) state20 (yyMinusYZ_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip20
      (by simp [yyMinusYZSetupEffect, Effect.components, Component.Covers])
      (by simp [yyMinusYZSetupEffect, Effect.components])
  have rip21 : t21.RIP = 0x105d0d := effect21.rip
  have reg21_2 : t21.regValue .rdx = stackPtr s - 368 := by
    have h := effect21.writes.1
    change t21.regValue .rdx = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state20.rsp (by decide) (by decide)
  have reg21_6 : t21.regValue .rsi = stackPtr s - 304 := by
    have h := effect21.writes.2.1
    change t21.regValue .rsi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state20.rsp (by decide) (by decide)
  have reg21_14 : t21.regValue .r14 = stackPtr s - 592 := by
    have h := effect21.writes.2.2.2
    change t21.regValue .r14 = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state20.rsp (by decide) (by decide)
  have reg21_7 : t21.regValue .rdi = stackPtr s - 592 := by
    have h := effect21.writes.2.2.1
    change t21.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state20.rsp (by decide) (by decide)
  have mem21_output0 : MontgomeryAt t21 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := montgomery_external memory21 mem20_output0
  have mem21_output32 : MontgomeryAt t21 (s.regValue .rdi + 32) ((((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) + ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) := montgomery_external memory21 value20
  have mem21_stack304 : MontgomeryAt t21 (stackPtr s - 304) (values left right).yyMinus := montgomery_external memory21 mem20_stack304
  have mem21_stack368 : MontgomeryAt t21 (stackPtr s - 368) (values left right).yz := montgomery_external memory21 mem20_stack368
  have mem21_stack400 : MontgomeryAt t21 (stackPtr s - 400) (values left right).xy := montgomery_external memory21 mem20_stack400
  have mem21_stack432 : MontgomeryAt t21 (stackPtr s - 432) (values left right).xxMinus := montgomery_external memory21 mem20_stack432
  have reg21_3 : t21.regValue .rbx = s.regValue .rdi := (effect21.agrees.read (n := 64) (r := 3) (by simp [yyMinusYZSetupEffect, Effect.components])).trans reg20_3
  have reg21_13 : t21.regValue .r13 = stackPtr s - 432 := (effect21.agrees.read (n := 64) (r := 13) (by simp [yyMinusYZSetupEffect, Effect.components])).trans reg20_13
  obtain ⟨fuel22, t22, run22, state22, rip22, value22, saved22, kept22, frame22⟩ :=
    Call.binary_call (x := (values left right).yyMinus) (y := (values left right).yz) (op := fun x y => x * y % P256.Spec.Operations.domain.p) pre state21 Call.Sites.call_1039bd
      (fun _ cp hx hy => P256.Proofs.Field.field_mul_correct cp hx hy)
      rip21 reg21_6 reg21_2 reg21_7 mem21_stack304 mem21_stack368
  have mem22_output0 : MontgomeryAt t22 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := preserve_output_work pre frame22 (by decide) mem21_output0
  have mem22_output32 : MontgomeryAt t22 (s.regValue .rdi + 32) ((((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) + ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) := preserve_output_work pre frame22 (by decide) mem21_output32
  have mem22_stack400 : MontgomeryAt t22 (stackPtr s - 400) (values left right).xy := mem21_stack400.of_bytes_eq (fun i hi => (kept22 400 32 (by decide) (by decide) (by decide) i hi))
  have mem22_stack432 : MontgomeryAt t22 (stackPtr s - 432) (values left right).xxMinus := mem21_stack432.of_bytes_eq (fun i hi => (kept22 432 32 (by decide) (by decide) (by decide) i hi))
  have reg22_3 : t22.regValue .rbx = s.regValue .rdi := (saved22 .rbx (by simp)).trans reg21_3
  have reg22_13 : t22.regValue .r13 = stackPtr s - 432 := (saved22 .r13 (by simp)).trans reg21_13
  have reg22_14 : t22.regValue .r14 = stackPtr s - 592 := (saved22 .r14 (by simp)).trans reg21_14
  obtain ⟨fuel23, t23, run23, state23, effect23, memory23⟩ :=
    execute_registers (offset := 0x5d12) state22 (xyXXMinus_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip22
      (by simp [xyXXMinusSetupEffect, Effect.components, Component.Covers])
      (by simp [xyXXMinusSetupEffect, Effect.components])
  have rip23 : t23.RIP = 0x105d25 := effect23.rip
  have reg23_2 : t23.regValue .rdx = stackPtr s - 432 := by
    have h := effect23.writes.1
    change t23.regValue .rdx = _ at h
    rw [h]
    exact reg22_13
  have reg23_7 : t23.regValue .rdi = stackPtr s - 624 := by
    have h := effect23.writes.2.2.1
    change t23.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state22.rsp (by decide) (by decide)
  have reg23_6 : t23.regValue .rsi = stackPtr s - 400 := by
    have h := effect23.writes.2.1
    change t23.regValue .rsi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state22.rsp (by decide) (by decide)
  have reg23_15 : t23.regValue .r15 = stackPtr s - 624 := by
    have h := effect23.writes.2.2.2
    change t23.regValue .r15 = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state22.rsp (by decide) (by decide)
  have mem23_output0 : MontgomeryAt t23 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := montgomery_external memory23 mem22_output0
  have mem23_output32 : MontgomeryAt t23 (s.regValue .rdi + 32) ((((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) + ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) := montgomery_external memory23 mem22_output32
  have mem23_stack400 : MontgomeryAt t23 (stackPtr s - 400) (values left right).xy := montgomery_external memory23 mem22_stack400
  have mem23_stack432 : MontgomeryAt t23 (stackPtr s - 432) (values left right).xxMinus := montgomery_external memory23 mem22_stack432
  have mem23_stack592 : MontgomeryAt t23 (stackPtr s - 592) ((values left right).yyMinus * (values left right).yz % P256.Spec.Operations.domain.p) := montgomery_external memory23 value22
  have reg23_3 : t23.regValue .rbx = s.regValue .rdi := (effect23.agrees.read (n := 64) (r := 3) (by simp [xyXXMinusSetupEffect, Effect.components])).trans reg22_3
  have reg23_14 : t23.regValue .r14 = stackPtr s - 592 := (effect23.agrees.read (n := 64) (r := 14) (by simp [xyXXMinusSetupEffect, Effect.components])).trans reg22_14
  obtain ⟨fuel24, t24, run24, state24, rip24, value24, saved24, kept24, frame24⟩ :=
    Call.binary_call (x := (values left right).xy) (y := (values left right).xxMinus) (op := fun x y => x * y % P256.Spec.Operations.domain.p) pre state23 Call.Sites.call_1039d5
      (fun _ cp hx hy => P256.Proofs.Field.field_mul_correct cp hx hy)
      rip23 reg23_6 reg23_2 reg23_7 mem23_stack400 mem23_stack432
  have mem24_output0 : MontgomeryAt t24 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := preserve_output_work pre frame24 (by decide) mem23_output0
  have mem24_output32 : MontgomeryAt t24 (s.regValue .rdi + 32) ((((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) + ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) := preserve_output_work pre frame24 (by decide) mem23_output32
  have mem24_stack592 : MontgomeryAt t24 (stackPtr s - 592) ((values left right).yyMinus * (values left right).yz % P256.Spec.Operations.domain.p) := mem23_stack592.of_bytes_eq (fun i hi => (kept24 592 32 (by decide) (by decide) (by decide) i hi))
  have reg24_3 : t24.regValue .rbx = s.regValue .rdi := (saved24 .rbx (by simp)).trans reg23_3
  have reg24_14 : t24.regValue .r14 = stackPtr s - 592 := (saved24 .r14 (by simp)).trans reg23_14
  have reg24_15 : t24.regValue .r15 = stackPtr s - 624 := (saved24 .r15 (by simp)).trans reg23_15
  obtain ⟨fuel25, t25, run25, state25, effect25, memory25⟩ :=
    execute_registers (offset := 0x5d2a) state24 (z_setup_block boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip24
      (by simp [zSetupEffect, Effect.components, Component.Covers])
      (by simp [zSetupEffect, Effect.components])
  have rip25 : t25.RIP = 0x105d38 := effect25.rip
  have reg25_2 : t25.regValue .rdx = stackPtr s - 624 := by
    have h := effect25.writes.1
    change t25.regValue .rdx = _ at h
    rw [h]
    exact reg24_15
  have reg25_6 : t25.regValue .rsi = stackPtr s - 592 := by
    have h := effect25.writes.2.1
    change t25.regValue .rsi = _ at h
    rw [h]
    exact reg24_14
  have reg25_7 : t25.regValue .rdi = stackPtr s - 496 := by
    have h := effect25.writes.2.2
    change t25.regValue .rdi = _ at h
    rw [h]
    exact scalar_stack_address (frameOffset := 632) state24.rsp (by decide) (by decide)
  have mem25_output0 : MontgomeryAt t25 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := montgomery_external memory25 mem24_output0
  have mem25_output32 : MontgomeryAt t25 (s.regValue .rdi + 32) ((((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) + ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) := montgomery_external memory25 mem24_output32
  have mem25_stack592 : MontgomeryAt t25 (stackPtr s - 592) ((values left right).yyMinus * (values left right).yz % P256.Spec.Operations.domain.p) := montgomery_external memory25 mem24_stack592
  have mem25_stack624 : MontgomeryAt t25 (stackPtr s - 624) ((values left right).xy * (values left right).xxMinus % P256.Spec.Operations.domain.p) := montgomery_external memory25 value24
  have reg25_3 : t25.regValue .rbx = s.regValue .rdi := (effect25.agrees.read (n := 64) (r := 3) (by simp [zSetupEffect, Effect.components])).trans reg24_3
  obtain ⟨fuel26, t26, run26, state26, rip26, value26, saved26, kept26, frame26⟩ :=
    Call.binary_call (x := ((values left right).yyMinus * (values left right).yz % P256.Spec.Operations.domain.p)) (y := ((values left right).xy * (values left right).xxMinus % P256.Spec.Operations.domain.p)) (op := fun x y => (x+y) % P256.Spec.Operations.domain.p) pre state25 Call.Sites.call_1039e8
      (fun _ cp hx hy => P256.Proofs.Field.field_add_correct cp hx hy)
      rip25 reg25_6 reg25_2 reg25_7 mem25_stack592 mem25_stack624
  have mem26_output0 : MontgomeryAt t26 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := preserve_output_work pre frame26 (by decide) mem25_output0
  have mem26_output32 : MontgomeryAt t26 (s.regValue .rdi + 32) ((((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) + ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) := preserve_output_work pre frame26 (by decide) mem25_output32
  have reg26_3 : t26.regValue .rbx = s.regValue .rdi := (saved26 .rbx (by simp)).trans reg25_3
  obtain ⟨fuel27, t27, run27, state27, rip27, value27, agrees27⟩ :=
    execute_output (entryOffset := 0x5d3d) pre state26
      (copy_z_block boundary pre.outerBoundary) (by decide) (by decide +kernel)
      (off := 64) (srcOff := 136) (by decide) (by decide) rfl
      (by change t26.regValue .rbx + 64 = _; rw [reg26_3]; rfl) rip26
      (by change MontgomeryAt t26 (stackPtr t26 + BitVec.ofNat 64 136) _
          rw [scalar_stack_address (frameOffset := 632) state26.rsp (by decide) (offset := 136) (by decide)]
          exact value26)
  have dest27 : (Operand.reg 3 : Operand 64).read t26 + 64 = s.regValue .rdi + 64 :=
    congrArg (· + 64) reg26_3
  rw [dest27] at value27 agrees27
  have mem27_output0 : MontgomeryAt t27 (s.regValue .rdi + 0) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p ((values left right).yyPlus * (values left right).xy % P256.Spec.Operations.domain.p) ((values left right).yz * (values left right).bxz3 % P256.Spec.Operations.domain.p)) := copy_output_output pre agrees27 (by decide) (by decide) (by decide) mem26_output0
  have mem27_output32 : MontgomeryAt t27 (s.regValue .rdi + 32) ((((values left right).yyPlus * (values left right).yyMinus % P256.Spec.Operations.domain.p) + ((values left right).xxMinus * (values left right).bxz3 % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) := copy_output_output pre agrees27 (by decide) (by decide) (by decide) mem26_output32
  refine ⟨_, t27, ((((((((((((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17).trans run18).trans run19).trans run20).trans run21).trans run22).trans run23).trans run24).trans run25).trans run26).trans run27), state27, rip27, ?_⟩
  rw [← values_output]
  exact ⟨by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Values.output] using mem27_output0, mem27_output32, value27⟩

end P256.Proofs.Projective.Add
