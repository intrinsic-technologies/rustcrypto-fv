import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.Memory
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame TableSteps Blocks

theorem first_entries [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e701)
    (facts : Facts s t [(.rsi, s.regValue .rsi), (.rdi, s.regValue .rdi)]
      []) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = 0x10e76d ∧ Facts s u [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 1584), (.r12,
        stackPtr s - 1488), (.r13, stackPtr s - 144), (.r14, stackPtr s - 1392), (.r15, s.regValue
        .rsi)]
        [(144, Projective.tableEntry basePoint 1), (1584, Projective.tableEntry basePoint 1), (1680,
          Projective.tableEntry basePoint 0)] := by
  rcases facts.regs with ⟨r6_in, r7_in, trivial⟩
  obtain ⟨n1, t1, run1, st1, eff1, mem1⟩ :=
    register_block (offset := 0xe701) state (b116471_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b116471Effect, Effect.components, Component.Covers])
      (by simp [b116471Effect, Effect.components])
      (by simp [b116471Effect, Effect.components])
      (by simp [b116471Effect, Effect.components])
      (by simp [b116471Effect, Effect.components])
  have r15_1 : t1.regValue .r15 = s.regValue .rsi :=
    eff1.writes.1.trans r6_in
  have r3_1 : t1.regValue .rbx = s.regValue .rdi :=
    eff1.writes.2.1.trans r7_in
  have r7_1 : t1.regValue .rdi = stackPtr s - 1680 := by
    have h : t1.regValue .rdi = stackPtr t + 264 := eff1.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_1 : t1.regValue .rcx = 12 := eff1.writes.2.2.2.1
  have r6_1 : t1.regValue .rsi = 2108104 := eff1.writes.2.2.2.2
  obtain ⟨t2, run2, st2, rip2, value2, eff2, _⟩ :=
    copy_generator pre st1 0xe71b (by decide) (by decide +kernel)
      eff1.rip 1680 (by decide) (by decide) r7_1 r1_1
      r6_1
  have r15_2 : t2.regValue .r15 = s.regValue .rsi :=
    (eff2.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_1
  have r3_2 : t2.regValue .rbx = s.regValue .rdi :=
    (eff2.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_1
  obtain ⟨n3, t3, run3, st3, eff3, mem3⟩ :=
    register_block (offset := 0xe71e) st2 (b11648e_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip2
      (by simp [b11648eEffect, Effect.components, Component.Covers])
      (by simp [b11648eEffect, Effect.components])
      (by simp [b11648eEffect, Effect.components])
      (by simp [b11648eEffect, Effect.components])
      (by simp [b11648eEffect, Effect.components])
  have r5_3 : t3.regValue .rbp = stackPtr s - 1584 := by
    have h : t3.regValue .rbp = stackPtr t2 + 360 := eff3.writes.1
    exact h.trans (scalar_stack_address st2.rsp (by decide) (by decide))
  have r12_3 : t3.regValue .r12 = stackPtr s - 1488 := by
    have h : t3.regValue .r12 = stackPtr t2 + 456 := eff3.writes.2.1
    exact h.trans (scalar_stack_address st2.rsp (by decide) (by decide))
  have r14_3 : t3.regValue .r14 = stackPtr s - 1392 := by
    have h : t3.regValue .r14 = stackPtr t2 + 552 := eff3.writes.2.2.1
    exact h.trans (scalar_stack_address st2.rsp (by decide) (by decide))
  have r13_3 : t3.regValue .r13 = stackPtr s - 144 := by
    have h : t3.regValue .r13 = stackPtr t2 + 1800 := eff3.writes.2.2.2.1
    exact h.trans (scalar_stack_address st2.rsp (by decide) (by decide))
  have r1_3 : t3.regValue .rcx = 12 := eff3.writes.2.2.2.2.1
  have r7_3 : t3.regValue .rdi = stackPtr s - 144 := by
    have h : t3.regValue .rdi = stackPtr t2 + 1800 := eff3.writes.2.2.2.2.2.1
    exact h.trans (scalar_stack_address st2.rsp (by decide) (by decide))
  have r6_3 : t3.regValue .rsi = 2108104 := eff3.writes.2.2.2.2.2.2
  have r15_3 : t3.regValue .r15 = s.regValue .rsi :=
    (eff3.agrees.read (n := 64) (r := 15)
      (by simp [b11648eEffect, Effect.components])).trans r15_2
  have r3_3 : t3.regValue .rbx = s.regValue .rdi :=
    (eff3.agrees.read (n := 64) (r := 3)
      (by simp [b11648eEffect, Effect.components])).trans r3_2
  have p1680_3 := point_of_external value2 mem3
  obtain ⟨t4, run4, st4, rip4, value4, eff4, _⟩ :=
    copy_generator pre st3 0xe74d (by decide) (by decide +kernel)
      eff3.rip 144 (by decide) (by decide) r7_3 r1_3
      r6_3
  have r15_4 : t4.regValue .r15 = s.regValue .rsi :=
    (eff4.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_3
  have r3_4 : t4.regValue .rbx = s.regValue .rdi :=
    (eff4.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_3
  have r5_4 : t4.regValue .rbp = stackPtr s - 1584 :=
    (eff4.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_3
  have r12_4 : t4.regValue .r12 = stackPtr s - 1488 :=
    (eff4.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_3
  have r14_4 : t4.regValue .r14 = stackPtr s - 1392 :=
    (eff4.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_3
  have r13_4 : t4.regValue .r13 = stackPtr s - 144 :=
    (eff4.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_3
  have p1680_4 := copy_point (offset := 1680) pre eff4 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_3
  obtain ⟨n5, t5, run5, st5, eff5, mem5⟩ :=
    register_block (offset := 0xe750) st4 (b1164c0_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip4
      (by simp [b1164c0Effect, Effect.components, Component.Covers])
      (by simp [b1164c0Effect, Effect.components])
      (by simp [b1164c0Effect, Effect.components])
      (by simp [b1164c0Effect, Effect.components])
      (by simp [b1164c0Effect, Effect.components])
  have r7_5 : t5.regValue .rdi = stackPtr s - 144 :=
    eff5.writes.1.trans r13_4
  have r6_5 : t5.regValue .rsi = 2108104 := eff5.writes.2
  have r15_5 : t5.regValue .r15 = s.regValue .rsi :=
    (eff5.agrees.read (n := 64) (r := 15)
      (by simp [b1164c0Effect, Effect.components])).trans r15_4
  have r3_5 : t5.regValue .rbx = s.regValue .rdi :=
    (eff5.agrees.read (n := 64) (r := 3)
      (by simp [b1164c0Effect, Effect.components])).trans r3_4
  have r5_5 : t5.regValue .rbp = stackPtr s - 1584 :=
    (eff5.agrees.read (n := 64) (r := 5)
      (by simp [b1164c0Effect, Effect.components])).trans r5_4
  have r12_5 : t5.regValue .r12 = stackPtr s - 1488 :=
    (eff5.agrees.read (n := 64) (r := 12)
      (by simp [b1164c0Effect, Effect.components])).trans r12_4
  have r14_5 : t5.regValue .r14 = stackPtr s - 1392 :=
    (eff5.agrees.read (n := 64) (r := 14)
      (by simp [b1164c0Effect, Effect.components])).trans r14_4
  have r13_5 : t5.regValue .r13 = stackPtr s - 144 :=
    (eff5.agrees.read (n := 64) (r := 13)
      (by simp [b1164c0Effect, Effect.components])).trans r13_4
  have p1680_5 := point_of_external p1680_4 mem5
  have p144_5 := point_of_external value4 mem5
  obtain ⟨t6, result6⟩ :=
    add_generator_call pre st5 add1164ca eff5.rip
      r7_5 r6_5 p144_5
  obtain ⟨n6, run6⟩ := result6.execution
  have st6 := result6.toFrameState
  have value6 : ProjectiveAt t6 (stackPtr s - 144)
      (Projective.tableEntry basePoint 1) := result6.value
  have r15_6 : t6.regValue .r15 = s.regValue .rsi :=
    (result6.registers .r15 (by simp)).trans r15_5
  have r3_6 : t6.regValue .rbx = s.regValue .rdi :=
    (result6.registers .rbx (by simp)).trans r3_5
  have r5_6 : t6.regValue .rbp = stackPtr s - 1584 :=
    (result6.registers .rbp (by simp)).trans r5_5
  have r12_6 : t6.regValue .r12 = stackPtr s - 1488 :=
    (result6.registers .r12 (by simp)).trans r12_5
  have r14_6 : t6.regValue .r14 = stackPtr s - 1392 :=
    (result6.registers .r14 (by simp)).trans r14_5
  have r13_6 : t6.regValue .r13 = stackPtr s - 144 :=
    (result6.registers .r13 (by simp)).trans r13_5
  have p1680_6 := call_point (offset := 1680) result6 (by decide) (by decide) (by decide) p1680_5
  obtain ⟨n7, t7, run7, st7, eff7, mem7⟩ :=
    register_block (offset := 0xe75f) st6 (b1164cf_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result6.rip
      (by simp [b1164cfEffect, Effect.components, Component.Covers])
      (by simp [b1164cfEffect, Effect.components])
      (by simp [b1164cfEffect, Effect.components])
      (by simp [b1164cfEffect, Effect.components])
      (by simp [b1164cfEffect, Effect.components])
  have r1_7 : t7.regValue .rcx = 12 := eff7.writes.1
  have r7_7 : t7.regValue .rdi = stackPtr s - 1584 :=
    eff7.writes.2.1.trans r5_6
  have r6_7 : t7.regValue .rsi = stackPtr s - 144 :=
    eff7.writes.2.2.trans r13_6
  have r15_7 : t7.regValue .r15 = s.regValue .rsi :=
    (eff7.agrees.read (n := 64) (r := 15)
      (by simp [b1164cfEffect, Effect.components])).trans r15_6
  have r3_7 : t7.regValue .rbx = s.regValue .rdi :=
    (eff7.agrees.read (n := 64) (r := 3)
      (by simp [b1164cfEffect, Effect.components])).trans r3_6
  have r5_7 : t7.regValue .rbp = stackPtr s - 1584 :=
    (eff7.agrees.read (n := 64) (r := 5)
      (by simp [b1164cfEffect, Effect.components])).trans r5_6
  have r12_7 : t7.regValue .r12 = stackPtr s - 1488 :=
    (eff7.agrees.read (n := 64) (r := 12)
      (by simp [b1164cfEffect, Effect.components])).trans r12_6
  have r14_7 : t7.regValue .r14 = stackPtr s - 1392 :=
    (eff7.agrees.read (n := 64) (r := 14)
      (by simp [b1164cfEffect, Effect.components])).trans r14_6
  have r13_7 : t7.regValue .r13 = stackPtr s - 144 :=
    (eff7.agrees.read (n := 64) (r := 13)
      (by simp [b1164cfEffect, Effect.components])).trans r13_6
  have p1680_7 := point_of_external p1680_6 mem7
  have p144_7 := point_of_external value6 mem7
  obtain ⟨t8, run8, st8, rip8, value8, eff8, _⟩ :=
    copy_stack (sourceOffset := 144) pre st7 0xe76a (by decide) (by decide +kernel)
      eff7.rip 1584 (by decide) (by decide) r7_7 r1_7
      (by decide) (by decide) (by decide) r6_7 p144_7
  have r15_8 : t8.regValue .r15 = s.regValue .rsi :=
    (eff8.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_7
  have r3_8 : t8.regValue .rbx = s.regValue .rdi :=
    (eff8.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_7
  have r5_8 : t8.regValue .rbp = stackPtr s - 1584 :=
    (eff8.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_7
  have r12_8 : t8.regValue .r12 = stackPtr s - 1488 :=
    (eff8.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_7
  have r14_8 : t8.regValue .r14 = stackPtr s - 1392 :=
    (eff8.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_7
  have r13_8 : t8.regValue .r13 = stackPtr s - 144 :=
    (eff8.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_7
  have p1680_8 := copy_point (offset := 1680) pre eff8 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_7
  have p144_8 := copy_point (offset := 144) pre eff8 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_7
  exact ⟨n1 + 12 + n3 + 12 + n5 + n6 + n7 + 12, t8, (((((((run1.trans run2).trans run3).trans
    run4).trans run5).trans run6).trans run7).trans run8), st8, rip8,
    ⟨r3_8, r5_8, r12_8, r13_8, r14_8, r15_8, trivial⟩,
    ⟨p144_8, value8, p1680_8, trivial⟩⟩

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
