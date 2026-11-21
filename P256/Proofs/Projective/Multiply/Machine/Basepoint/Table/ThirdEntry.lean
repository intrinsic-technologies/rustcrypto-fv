import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.Memory
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame TableSteps Blocks

theorem third_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e76d)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 1584), (.r12, stackPtr s -
      1488), (.r13, stackPtr s - 144), (.r14, stackPtr s - 1392), (.r15, s.regValue .rsi)]
      [(144, Projective.tableEntry basePoint 1), (1584, Projective.tableEntry basePoint 1), (1680,
        Projective.tableEntry basePoint 0)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = 0x10e7ae ∧ Facts s u [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12,
        stackPtr s - 1488), (.r13, stackPtr s - 144), (.r14, stackPtr s - 1392), (.r15, s.regValue
        .rsi)]
        [(144, Projective.tableEntry basePoint 2), (912, Projective.tableEntry basePoint 2), (1488,
          Projective.tableEntry basePoint 2), (1584, Projective.tableEntry basePoint 1), (1680,
          Projective.tableEntry basePoint 0)] := by
  rcases facts.regs with ⟨r3_in, r5_in, r12_in, r13_in, r14_in, r15_in, trivial⟩
  rcases facts.points with ⟨p144_in, p1584_in, p1680_in, trivial⟩
  obtain ⟨n9, t9, run9, st9, eff9, mem9⟩ :=
    register_block (offset := 0xe76d) state (b1164dd_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b1164ddEffect, Effect.components, Component.Covers])
      (by simp [b1164ddEffect, Effect.components])
      (by simp [b1164ddEffect, Effect.components])
      (by simp [b1164ddEffect, Effect.components])
      (by simp [b1164ddEffect, Effect.components])
  have r5_9 : t9.regValue .rbp = stackPtr s - 912 := by
    have h : t9.regValue .rbp = stackPtr t + 1032 := eff9.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_9 : t9.regValue .rcx = 12 := eff9.writes.2.1
  have r7_9 : t9.regValue .rdi = stackPtr s - 912 := by
    have h : t9.regValue .rdi = stackPtr t + 1032 := eff9.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_9 : t9.regValue .rsi = 2108104 := eff9.writes.2.2.2
  have r15_9 : t9.regValue .r15 = s.regValue .rsi :=
    (eff9.agrees.read (n := 64) (r := 15)
      (by simp [b1164ddEffect, Effect.components])).trans r15_in
  have r3_9 : t9.regValue .rbx = s.regValue .rdi :=
    (eff9.agrees.read (n := 64) (r := 3)
      (by simp [b1164ddEffect, Effect.components])).trans r3_in
  have r12_9 : t9.regValue .r12 = stackPtr s - 1488 :=
    (eff9.agrees.read (n := 64) (r := 12)
      (by simp [b1164ddEffect, Effect.components])).trans r12_in
  have r14_9 : t9.regValue .r14 = stackPtr s - 1392 :=
    (eff9.agrees.read (n := 64) (r := 14)
      (by simp [b1164ddEffect, Effect.components])).trans r14_in
  have r13_9 : t9.regValue .r13 = stackPtr s - 144 :=
    (eff9.agrees.read (n := 64) (r := 13)
      (by simp [b1164ddEffect, Effect.components])).trans r13_in
  have p1680_9 := point_of_external p1680_in mem9
  have p144_9 := point_of_external p144_in mem9
  have p1584_9 := point_of_external p1584_in mem9
  obtain ⟨t10, run10, st10, rip10, value10, eff10, _⟩ :=
    copy_generator pre st9 0xe784 (by decide) (by decide +kernel)
      eff9.rip 912 (by decide) (by decide) r7_9 r1_9
      r6_9
  have r15_10 : t10.regValue .r15 = s.regValue .rsi :=
    (eff10.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_9
  have r3_10 : t10.regValue .rbx = s.regValue .rdi :=
    (eff10.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_9
  have r5_10 : t10.regValue .rbp = stackPtr s - 912 :=
    (eff10.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_9
  have r12_10 : t10.regValue .r12 = stackPtr s - 1488 :=
    (eff10.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_9
  have r14_10 : t10.regValue .r14 = stackPtr s - 1392 :=
    (eff10.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_9
  have r13_10 : t10.regValue .r13 = stackPtr s - 144 :=
    (eff10.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_9
  have p1680_10 := copy_point (offset := 1680) pre eff10 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_9
  have p144_10 := copy_point (offset := 144) pre eff10 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_9
  have p1584_10 := copy_point (offset := 1584) pre eff10 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_9
  obtain ⟨n11, t11, run11, st11, eff11, mem11⟩ :=
    register_block (offset := 0xe787) st10 (b1164f7_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip10
      (by simp [b1164f7Effect, Effect.components, Component.Covers])
      (by simp [b1164f7Effect, Effect.components])
      (by simp [b1164f7Effect, Effect.components])
      (by simp [b1164f7Effect, Effect.components])
      (by simp [b1164f7Effect, Effect.components])
  have r7_11 : t11.regValue .rdi = stackPtr s - 912 :=
    eff11.writes.1.trans r5_10
  have r6_11 : t11.regValue .rsi = stackPtr s - 144 :=
    eff11.writes.2.trans r13_10
  have r15_11 : t11.regValue .r15 = s.regValue .rsi :=
    (eff11.agrees.read (n := 64) (r := 15)
      (by simp [b1164f7Effect, Effect.components])).trans r15_10
  have r3_11 : t11.regValue .rbx = s.regValue .rdi :=
    (eff11.agrees.read (n := 64) (r := 3)
      (by simp [b1164f7Effect, Effect.components])).trans r3_10
  have r5_11 : t11.regValue .rbp = stackPtr s - 912 :=
    (eff11.agrees.read (n := 64) (r := 5)
      (by simp [b1164f7Effect, Effect.components])).trans r5_10
  have r12_11 : t11.regValue .r12 = stackPtr s - 1488 :=
    (eff11.agrees.read (n := 64) (r := 12)
      (by simp [b1164f7Effect, Effect.components])).trans r12_10
  have r14_11 : t11.regValue .r14 = stackPtr s - 1392 :=
    (eff11.agrees.read (n := 64) (r := 14)
      (by simp [b1164f7Effect, Effect.components])).trans r14_10
  have r13_11 : t11.regValue .r13 = stackPtr s - 144 :=
    (eff11.agrees.read (n := 64) (r := 13)
      (by simp [b1164f7Effect, Effect.components])).trans r13_10
  have p1680_11 := point_of_external p1680_10 mem11
  have p144_11 := point_of_external p144_10 mem11
  have p1584_11 := point_of_external p1584_10 mem11
  have p912_11 := point_of_external value10 mem11
  obtain ⟨t12, result12⟩ :=
    add_call pre st11 add1164fd eff11.rip
      r7_11 r6_11 p912_11 p144_11
  obtain ⟨n12, run12⟩ := result12.execution
  have st12 := result12.toFrameState
  have value12 : ProjectiveAt t12 (stackPtr s - 912)
      (Projective.tableEntry basePoint 2) := result12.value
  have r15_12 : t12.regValue .r15 = s.regValue .rsi :=
    (result12.registers .r15 (by simp)).trans r15_11
  have r3_12 : t12.regValue .rbx = s.regValue .rdi :=
    (result12.registers .rbx (by simp)).trans r3_11
  have r5_12 : t12.regValue .rbp = stackPtr s - 912 :=
    (result12.registers .rbp (by simp)).trans r5_11
  have r12_12 : t12.regValue .r12 = stackPtr s - 1488 :=
    (result12.registers .r12 (by simp)).trans r12_11
  have r14_12 : t12.regValue .r14 = stackPtr s - 1392 :=
    (result12.registers .r14 (by simp)).trans r14_11
  have r13_12 : t12.regValue .r13 = stackPtr s - 144 :=
    (result12.registers .r13 (by simp)).trans r13_11
  have p1680_12 := call_point (offset := 1680) result12 (by decide) (by decide) (by decide) p1680_11
  have p144_12 := call_point (offset := 144) result12 (by decide) (by decide) (by decide) p144_11
  have p1584_12 := call_point (offset := 1584) result12 (by decide) (by decide) (by decide) p1584_11
  obtain ⟨n13, t13, run13, st13, eff13, mem13⟩ :=
    register_block (offset := 0xe792) st12 (b116502_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result12.rip
      (by simp [b116502Effect, Effect.components, Component.Covers])
      (by simp [b116502Effect, Effect.components])
      (by simp [b116502Effect, Effect.components])
      (by simp [b116502Effect, Effect.components])
      (by simp [b116502Effect, Effect.components])
  have r1_13 : t13.regValue .rcx = 12 := eff13.writes.1
  have r7_13 : t13.regValue .rdi = stackPtr s - 144 :=
    eff13.writes.2.1.trans r13_12
  have r6_13 : t13.regValue .rsi = stackPtr s - 912 :=
    eff13.writes.2.2.trans r5_12
  have r15_13 : t13.regValue .r15 = s.regValue .rsi :=
    (eff13.agrees.read (n := 64) (r := 15)
      (by simp [b116502Effect, Effect.components])).trans r15_12
  have r3_13 : t13.regValue .rbx = s.regValue .rdi :=
    (eff13.agrees.read (n := 64) (r := 3)
      (by simp [b116502Effect, Effect.components])).trans r3_12
  have r5_13 : t13.regValue .rbp = stackPtr s - 912 :=
    (eff13.agrees.read (n := 64) (r := 5)
      (by simp [b116502Effect, Effect.components])).trans r5_12
  have r12_13 : t13.regValue .r12 = stackPtr s - 1488 :=
    (eff13.agrees.read (n := 64) (r := 12)
      (by simp [b116502Effect, Effect.components])).trans r12_12
  have r14_13 : t13.regValue .r14 = stackPtr s - 1392 :=
    (eff13.agrees.read (n := 64) (r := 14)
      (by simp [b116502Effect, Effect.components])).trans r14_12
  have r13_13 : t13.regValue .r13 = stackPtr s - 144 :=
    (eff13.agrees.read (n := 64) (r := 13)
      (by simp [b116502Effect, Effect.components])).trans r13_12
  have p1680_13 := point_of_external p1680_12 mem13
  have p144_13 := point_of_external p144_12 mem13
  have p1584_13 := point_of_external p1584_12 mem13
  have p912_13 := point_of_external value12 mem13
  obtain ⟨t14, run14, st14, rip14, value14, eff14, _⟩ :=
    copy_stack (sourceOffset := 912) pre st13 0xe79d (by decide) (by decide +kernel)
      eff13.rip 144 (by decide) (by decide) r7_13 r1_13
      (by decide) (by decide) (by decide) r6_13 p912_13
  have r15_14 : t14.regValue .r15 = s.regValue .rsi :=
    (eff14.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_13
  have r3_14 : t14.regValue .rbx = s.regValue .rdi :=
    (eff14.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_13
  have r5_14 : t14.regValue .rbp = stackPtr s - 912 :=
    (eff14.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_13
  have r12_14 : t14.regValue .r12 = stackPtr s - 1488 :=
    (eff14.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_13
  have r14_14 : t14.regValue .r14 = stackPtr s - 1392 :=
    (eff14.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_13
  have r13_14 : t14.regValue .r13 = stackPtr s - 144 :=
    (eff14.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_13
  have p1680_14 := copy_point (offset := 1680) pre eff14 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_13
  have p1584_14 := copy_point (offset := 1584) pre eff14 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_13
  have p912_14 := copy_point (offset := 912) pre eff14 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_13
  obtain ⟨n15, t15, run15, st15, eff15, mem15⟩ :=
    register_block (offset := 0xe7a0) st14 (b116510_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip14
      (by simp [b116510Effect, Effect.components, Component.Covers])
      (by simp [b116510Effect, Effect.components])
      (by simp [b116510Effect, Effect.components])
      (by simp [b116510Effect, Effect.components])
      (by simp [b116510Effect, Effect.components])
  have r1_15 : t15.regValue .rcx = 12 := eff15.writes.1
  have r7_15 : t15.regValue .rdi = stackPtr s - 1488 :=
    eff15.writes.2.1.trans r12_14
  have r6_15 : t15.regValue .rsi = stackPtr s - 144 :=
    eff15.writes.2.2.trans r13_14
  have r15_15 : t15.regValue .r15 = s.regValue .rsi :=
    (eff15.agrees.read (n := 64) (r := 15)
      (by simp [b116510Effect, Effect.components])).trans r15_14
  have r3_15 : t15.regValue .rbx = s.regValue .rdi :=
    (eff15.agrees.read (n := 64) (r := 3)
      (by simp [b116510Effect, Effect.components])).trans r3_14
  have r5_15 : t15.regValue .rbp = stackPtr s - 912 :=
    (eff15.agrees.read (n := 64) (r := 5)
      (by simp [b116510Effect, Effect.components])).trans r5_14
  have r12_15 : t15.regValue .r12 = stackPtr s - 1488 :=
    (eff15.agrees.read (n := 64) (r := 12)
      (by simp [b116510Effect, Effect.components])).trans r12_14
  have r14_15 : t15.regValue .r14 = stackPtr s - 1392 :=
    (eff15.agrees.read (n := 64) (r := 14)
      (by simp [b116510Effect, Effect.components])).trans r14_14
  have r13_15 : t15.regValue .r13 = stackPtr s - 144 :=
    (eff15.agrees.read (n := 64) (r := 13)
      (by simp [b116510Effect, Effect.components])).trans r13_14
  have p1680_15 := point_of_external p1680_14 mem15
  have p144_15 := point_of_external value14 mem15
  have p1584_15 := point_of_external p1584_14 mem15
  have p912_15 := point_of_external p912_14 mem15
  obtain ⟨t16, run16, st16, rip16, value16, eff16, _⟩ :=
    copy_stack (sourceOffset := 144) pre st15 0xe7ab (by decide) (by decide +kernel)
      eff15.rip 1488 (by decide) (by decide) r7_15 r1_15
      (by decide) (by decide) (by decide) r6_15 p144_15
  have r15_16 : t16.regValue .r15 = s.regValue .rsi :=
    (eff16.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_15
  have r3_16 : t16.regValue .rbx = s.regValue .rdi :=
    (eff16.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_15
  have r5_16 : t16.regValue .rbp = stackPtr s - 912 :=
    (eff16.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_15
  have r12_16 : t16.regValue .r12 = stackPtr s - 1488 :=
    (eff16.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_15
  have r14_16 : t16.regValue .r14 = stackPtr s - 1392 :=
    (eff16.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_15
  have r13_16 : t16.regValue .r13 = stackPtr s - 144 :=
    (eff16.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_15
  have p1680_16 := copy_point (offset := 1680) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_15
  have p144_16 := copy_point (offset := 144) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_15
  have p1584_16 := copy_point (offset := 1584) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_15
  have p912_16 := copy_point (offset := 912) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_15
  exact ⟨n9 + 12 + n11 + n12 + n13 + 12 + n15 + 12, t16, (((((((run9.trans run10).trans run11).trans
    run12).trans run13).trans run14).trans run15).trans run16), st16, rip16,
    ⟨r3_16, r5_16, r12_16, r13_16, r14_16, r15_16, trivial⟩,
    ⟨p144_16, p912_16, value16, p1584_16, p1680_16, trivial⟩⟩

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
