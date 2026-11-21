import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.Memory
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame TableSteps Blocks

theorem fifth_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e7ef)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12, stackPtr s - 912),
      (.r13, stackPtr s - 144), (.r14, stackPtr s - 1392), (.r15, s.regValue .rsi)]
      [(144, Projective.tableEntry basePoint 3), (912, Projective.tableEntry basePoint 3), (1392,
        Projective.tableEntry basePoint 3), (1488, Projective.tableEntry basePoint 2), (1584,
        Projective.tableEntry basePoint 1), (1680, Projective.tableEntry basePoint 0)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = 0x10e835 ∧ Facts s u [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12,
        stackPtr s - 912), (.r13, stackPtr s - 144), (.r14, stackPtr s - 912), (.r15, s.regValue
        .rsi)]
        [(144, Projective.tableEntry basePoint 4), (912, Projective.tableEntry basePoint 4), (1296,
          Projective.tableEntry basePoint 4), (1392, Projective.tableEntry basePoint 3), (1488,
          Projective.tableEntry basePoint 2), (1584, Projective.tableEntry basePoint 1), (1680,
          Projective.tableEntry basePoint 0)] := by
  rcases facts.regs with ⟨r3_in, r5_in, r12_in, r13_in, r14_in, r15_in, trivial⟩
  rcases facts.points with ⟨p144_in, p912_in, p1392_in, p1488_in, p1584_in, p1680_in, trivial⟩
  obtain ⟨n25, t25, run25, st25, eff25, mem25⟩ :=
    register_block (offset := 0xe7ef) state (b11655f_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b11655fEffect, Effect.components, Component.Covers])
      (by simp [b11655fEffect, Effect.components])
      (by simp [b11655fEffect, Effect.components])
      (by simp [b11655fEffect, Effect.components])
      (by simp [b11655fEffect, Effect.components])
  have r14_25 : t25.regValue .r14 = stackPtr s - 912 := by
    have h : t25.regValue .r14 = stackPtr t + 1032 := eff25.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_25 : t25.regValue .rcx = 12 := eff25.writes.2.1
  have r7_25 : t25.regValue .rdi = stackPtr s - 912 := by
    have h : t25.regValue .rdi = stackPtr t + 1032 := eff25.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_25 : t25.regValue .rsi = 2108104 := eff25.writes.2.2.2
  have r15_25 : t25.regValue .r15 = s.regValue .rsi :=
    (eff25.agrees.read (n := 64) (r := 15)
      (by simp [b11655fEffect, Effect.components])).trans r15_in
  have r3_25 : t25.regValue .rbx = s.regValue .rdi :=
    (eff25.agrees.read (n := 64) (r := 3)
      (by simp [b11655fEffect, Effect.components])).trans r3_in
  have r5_25 : t25.regValue .rbp = stackPtr s - 912 :=
    (eff25.agrees.read (n := 64) (r := 5)
      (by simp [b11655fEffect, Effect.components])).trans r5_in
  have r12_25 : t25.regValue .r12 = stackPtr s - 912 :=
    (eff25.agrees.read (n := 64) (r := 12)
      (by simp [b11655fEffect, Effect.components])).trans r12_in
  have r13_25 : t25.regValue .r13 = stackPtr s - 144 :=
    (eff25.agrees.read (n := 64) (r := 13)
      (by simp [b11655fEffect, Effect.components])).trans r13_in
  have p1680_25 := point_of_external p1680_in mem25
  have p144_25 := point_of_external p144_in mem25
  have p1584_25 := point_of_external p1584_in mem25
  have p912_25 := point_of_external p912_in mem25
  have p1488_25 := point_of_external p1488_in mem25
  have p1392_25 := point_of_external p1392_in mem25
  obtain ⟨t26, run26, st26, rip26, value26, eff26, _⟩ :=
    copy_generator pre st25 0xe806 (by decide) (by decide +kernel)
      eff25.rip 912 (by decide) (by decide) r7_25 r1_25
      r6_25
  have r15_26 : t26.regValue .r15 = s.regValue .rsi :=
    (eff26.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_25
  have r3_26 : t26.regValue .rbx = s.regValue .rdi :=
    (eff26.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_25
  have r5_26 : t26.regValue .rbp = stackPtr s - 912 :=
    (eff26.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_25
  have r12_26 : t26.regValue .r12 = stackPtr s - 912 :=
    (eff26.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_25
  have r14_26 : t26.regValue .r14 = stackPtr s - 912 :=
    (eff26.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_25
  have r13_26 : t26.regValue .r13 = stackPtr s - 144 :=
    (eff26.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_25
  have p1680_26 := copy_point (offset := 1680) pre eff26 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_25
  have p144_26 := copy_point (offset := 144) pre eff26 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_25
  have p1584_26 := copy_point (offset := 1584) pre eff26 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_25
  have p1488_26 := copy_point (offset := 1488) pre eff26 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_25
  have p1392_26 := copy_point (offset := 1392) pre eff26 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_25
  obtain ⟨n27, t27, run27, st27, eff27, mem27⟩ :=
    register_block (offset := 0xe809) st26 (b116579_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip26
      (by simp [b116579Effect, Effect.components, Component.Covers])
      (by simp [b116579Effect, Effect.components])
      (by simp [b116579Effect, Effect.components])
      (by simp [b116579Effect, Effect.components])
      (by simp [b116579Effect, Effect.components])
  have r7_27 : t27.regValue .rdi = stackPtr s - 912 :=
    eff27.writes.1.trans r14_26
  have r6_27 : t27.regValue .rsi = stackPtr s - 144 :=
    eff27.writes.2.trans r13_26
  have r15_27 : t27.regValue .r15 = s.regValue .rsi :=
    (eff27.agrees.read (n := 64) (r := 15)
      (by simp [b116579Effect, Effect.components])).trans r15_26
  have r3_27 : t27.regValue .rbx = s.regValue .rdi :=
    (eff27.agrees.read (n := 64) (r := 3)
      (by simp [b116579Effect, Effect.components])).trans r3_26
  have r5_27 : t27.regValue .rbp = stackPtr s - 912 :=
    (eff27.agrees.read (n := 64) (r := 5)
      (by simp [b116579Effect, Effect.components])).trans r5_26
  have r12_27 : t27.regValue .r12 = stackPtr s - 912 :=
    (eff27.agrees.read (n := 64) (r := 12)
      (by simp [b116579Effect, Effect.components])).trans r12_26
  have r14_27 : t27.regValue .r14 = stackPtr s - 912 :=
    (eff27.agrees.read (n := 64) (r := 14)
      (by simp [b116579Effect, Effect.components])).trans r14_26
  have r13_27 : t27.regValue .r13 = stackPtr s - 144 :=
    (eff27.agrees.read (n := 64) (r := 13)
      (by simp [b116579Effect, Effect.components])).trans r13_26
  have p1680_27 := point_of_external p1680_26 mem27
  have p144_27 := point_of_external p144_26 mem27
  have p1584_27 := point_of_external p1584_26 mem27
  have p912_27 := point_of_external value26 mem27
  have p1488_27 := point_of_external p1488_26 mem27
  have p1392_27 := point_of_external p1392_26 mem27
  obtain ⟨t28, result28⟩ :=
    add_call pre st27 add11657f eff27.rip
      r7_27 r6_27 p912_27 p144_27
  obtain ⟨n28, run28⟩ := result28.execution
  have st28 := result28.toFrameState
  have value28 : ProjectiveAt t28 (stackPtr s - 912)
      (Projective.tableEntry basePoint 4) := result28.value
  have r15_28 : t28.regValue .r15 = s.regValue .rsi :=
    (result28.registers .r15 (by simp)).trans r15_27
  have r3_28 : t28.regValue .rbx = s.regValue .rdi :=
    (result28.registers .rbx (by simp)).trans r3_27
  have r5_28 : t28.regValue .rbp = stackPtr s - 912 :=
    (result28.registers .rbp (by simp)).trans r5_27
  have r12_28 : t28.regValue .r12 = stackPtr s - 912 :=
    (result28.registers .r12 (by simp)).trans r12_27
  have r14_28 : t28.regValue .r14 = stackPtr s - 912 :=
    (result28.registers .r14 (by simp)).trans r14_27
  have r13_28 : t28.regValue .r13 = stackPtr s - 144 :=
    (result28.registers .r13 (by simp)).trans r13_27
  have p1680_28 := call_point (offset := 1680) result28 (by decide) (by decide) (by decide) p1680_27
  have p144_28 := call_point (offset := 144) result28 (by decide) (by decide) (by decide) p144_27
  have p1584_28 := call_point (offset := 1584) result28 (by decide) (by decide) (by decide) p1584_27
  have p1488_28 := call_point (offset := 1488) result28 (by decide) (by decide) (by decide) p1488_27
  have p1392_28 := call_point (offset := 1392) result28 (by decide) (by decide) (by decide) p1392_27
  obtain ⟨n29, t29, run29, st29, eff29, mem29⟩ :=
    register_block (offset := 0xe814) st28 (b116584_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result28.rip
      (by simp [b116584Effect, Effect.components, Component.Covers])
      (by simp [b116584Effect, Effect.components])
      (by simp [b116584Effect, Effect.components])
      (by simp [b116584Effect, Effect.components])
      (by simp [b116584Effect, Effect.components])
  have r1_29 : t29.regValue .rcx = 12 := eff29.writes.1
  have r7_29 : t29.regValue .rdi = stackPtr s - 144 :=
    eff29.writes.2.1.trans r13_28
  have r6_29 : t29.regValue .rsi = stackPtr s - 912 :=
    eff29.writes.2.2.trans r14_28
  have r15_29 : t29.regValue .r15 = s.regValue .rsi :=
    (eff29.agrees.read (n := 64) (r := 15)
      (by simp [b116584Effect, Effect.components])).trans r15_28
  have r3_29 : t29.regValue .rbx = s.regValue .rdi :=
    (eff29.agrees.read (n := 64) (r := 3)
      (by simp [b116584Effect, Effect.components])).trans r3_28
  have r5_29 : t29.regValue .rbp = stackPtr s - 912 :=
    (eff29.agrees.read (n := 64) (r := 5)
      (by simp [b116584Effect, Effect.components])).trans r5_28
  have r12_29 : t29.regValue .r12 = stackPtr s - 912 :=
    (eff29.agrees.read (n := 64) (r := 12)
      (by simp [b116584Effect, Effect.components])).trans r12_28
  have r14_29 : t29.regValue .r14 = stackPtr s - 912 :=
    (eff29.agrees.read (n := 64) (r := 14)
      (by simp [b116584Effect, Effect.components])).trans r14_28
  have r13_29 : t29.regValue .r13 = stackPtr s - 144 :=
    (eff29.agrees.read (n := 64) (r := 13)
      (by simp [b116584Effect, Effect.components])).trans r13_28
  have p1680_29 := point_of_external p1680_28 mem29
  have p144_29 := point_of_external p144_28 mem29
  have p1584_29 := point_of_external p1584_28 mem29
  have p912_29 := point_of_external value28 mem29
  have p1488_29 := point_of_external p1488_28 mem29
  have p1392_29 := point_of_external p1392_28 mem29
  obtain ⟨t30, run30, st30, rip30, value30, eff30, _⟩ :=
    copy_stack (sourceOffset := 912) pre st29 0xe81f (by decide) (by decide +kernel)
      eff29.rip 144 (by decide) (by decide) r7_29 r1_29
      (by decide) (by decide) (by decide) r6_29 p912_29
  have r15_30 : t30.regValue .r15 = s.regValue .rsi :=
    (eff30.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_29
  have r3_30 : t30.regValue .rbx = s.regValue .rdi :=
    (eff30.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_29
  have r5_30 : t30.regValue .rbp = stackPtr s - 912 :=
    (eff30.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_29
  have r12_30 : t30.regValue .r12 = stackPtr s - 912 :=
    (eff30.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_29
  have r14_30 : t30.regValue .r14 = stackPtr s - 912 :=
    (eff30.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_29
  have r13_30 : t30.regValue .r13 = stackPtr s - 144 :=
    (eff30.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_29
  have p1680_30 := copy_point (offset := 1680) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_29
  have p1584_30 := copy_point (offset := 1584) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_29
  have p912_30 := copy_point (offset := 912) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_29
  have p1488_30 := copy_point (offset := 1488) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_29
  have p1392_30 := copy_point (offset := 1392) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_29
  obtain ⟨n31, t31, run31, st31, eff31, mem31⟩ :=
    register_block (offset := 0xe822) st30 (b116592_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip30
      (by simp [b116592Effect, Effect.components, Component.Covers])
      (by simp [b116592Effect, Effect.components])
      (by simp [b116592Effect, Effect.components])
      (by simp [b116592Effect, Effect.components])
      (by simp [b116592Effect, Effect.components])
  have r1_31 : t31.regValue .rcx = 12 := eff31.writes.1
  have r7_31 : t31.regValue .rdi = stackPtr s - 1296 := by
    have h : t31.regValue .rdi = stackPtr t30 + 648 := eff31.writes.2.1
    exact h.trans (scalar_stack_address st30.rsp (by decide) (by decide))
  have r6_31 : t31.regValue .rsi = stackPtr s - 144 :=
    eff31.writes.2.2.trans r13_30
  have r15_31 : t31.regValue .r15 = s.regValue .rsi :=
    (eff31.agrees.read (n := 64) (r := 15)
      (by simp [b116592Effect, Effect.components])).trans r15_30
  have r3_31 : t31.regValue .rbx = s.regValue .rdi :=
    (eff31.agrees.read (n := 64) (r := 3)
      (by simp [b116592Effect, Effect.components])).trans r3_30
  have r5_31 : t31.regValue .rbp = stackPtr s - 912 :=
    (eff31.agrees.read (n := 64) (r := 5)
      (by simp [b116592Effect, Effect.components])).trans r5_30
  have r12_31 : t31.regValue .r12 = stackPtr s - 912 :=
    (eff31.agrees.read (n := 64) (r := 12)
      (by simp [b116592Effect, Effect.components])).trans r12_30
  have r14_31 : t31.regValue .r14 = stackPtr s - 912 :=
    (eff31.agrees.read (n := 64) (r := 14)
      (by simp [b116592Effect, Effect.components])).trans r14_30
  have r13_31 : t31.regValue .r13 = stackPtr s - 144 :=
    (eff31.agrees.read (n := 64) (r := 13)
      (by simp [b116592Effect, Effect.components])).trans r13_30
  have p1680_31 := point_of_external p1680_30 mem31
  have p144_31 := point_of_external value30 mem31
  have p1584_31 := point_of_external p1584_30 mem31
  have p912_31 := point_of_external p912_30 mem31
  have p1488_31 := point_of_external p1488_30 mem31
  have p1392_31 := point_of_external p1392_30 mem31
  obtain ⟨t32, run32, st32, rip32, value32, eff32, _⟩ :=
    copy_stack (sourceOffset := 144) pre st31 0xe832 (by decide) (by decide +kernel)
      eff31.rip 1296 (by decide) (by decide) r7_31 r1_31
      (by decide) (by decide) (by decide) r6_31 p144_31
  have r15_32 : t32.regValue .r15 = s.regValue .rsi :=
    (eff32.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_31
  have r3_32 : t32.regValue .rbx = s.regValue .rdi :=
    (eff32.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_31
  have r5_32 : t32.regValue .rbp = stackPtr s - 912 :=
    (eff32.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_31
  have r12_32 : t32.regValue .r12 = stackPtr s - 912 :=
    (eff32.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_31
  have r14_32 : t32.regValue .r14 = stackPtr s - 912 :=
    (eff32.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_31
  have r13_32 : t32.regValue .r13 = stackPtr s - 144 :=
    (eff32.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_31
  have p1680_32 := copy_point (offset := 1680) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_31
  have p144_32 := copy_point (offset := 144) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_31
  have p1584_32 := copy_point (offset := 1584) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_31
  have p912_32 := copy_point (offset := 912) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_31
  have p1488_32 := copy_point (offset := 1488) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_31
  have p1392_32 := copy_point (offset := 1392) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_31
  exact ⟨n25 + 12 + n27 + n28 + n29 + 12 + n31 + 12, t32, (((((((run25.trans run26).trans
    run27).trans run28).trans run29).trans run30).trans run31).trans run32), st32, rip32,
    ⟨r3_32, r5_32, r12_32, r13_32, r14_32, r15_32, trivial⟩,
    ⟨p144_32, p912_32, value32, p1392_32, p1488_32, p1584_32, p1680_32, trivial⟩⟩

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
