import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.Memory
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame TableSteps Blocks

theorem fourth_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e7ae)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12, stackPtr s -
      1488), (.r13, stackPtr s - 144), (.r14, stackPtr s - 1392), (.r15, s.regValue .rsi)]
      [(144, Projective.tableEntry basePoint 2), (912, Projective.tableEntry basePoint 2), (1488,
        Projective.tableEntry basePoint 2), (1584, Projective.tableEntry basePoint 1), (1680,
        Projective.tableEntry basePoint 0)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = 0x10e7ef ∧ Facts s u [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12,
        stackPtr s - 912), (.r13, stackPtr s - 144), (.r14, stackPtr s - 1392), (.r15, s.regValue
        .rsi)]
        [(144, Projective.tableEntry basePoint 3), (912, Projective.tableEntry basePoint 3), (1392,
          Projective.tableEntry basePoint 3), (1488, Projective.tableEntry basePoint 2), (1584,
          Projective.tableEntry basePoint 1), (1680, Projective.tableEntry basePoint 0)] := by
  rcases facts.regs with ⟨r3_in, r5_in, r12_in, r13_in, r14_in, r15_in, trivial⟩
  rcases facts.points with ⟨p144_in, p912_in, p1488_in, p1584_in, p1680_in, trivial⟩
  obtain ⟨n17, t17, run17, st17, eff17, mem17⟩ :=
    register_block (offset := 0xe7ae) state (b11651e_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b11651eEffect, Effect.components, Component.Covers])
      (by simp [b11651eEffect, Effect.components])
      (by simp [b11651eEffect, Effect.components])
      (by simp [b11651eEffect, Effect.components])
      (by simp [b11651eEffect, Effect.components])
  have r12_17 : t17.regValue .r12 = stackPtr s - 912 := by
    have h : t17.regValue .r12 = stackPtr t + 1032 := eff17.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_17 : t17.regValue .rcx = 12 := eff17.writes.2.1
  have r7_17 : t17.regValue .rdi = stackPtr s - 912 := by
    have h : t17.regValue .rdi = stackPtr t + 1032 := eff17.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_17 : t17.regValue .rsi = 2108104 := eff17.writes.2.2.2
  have r15_17 : t17.regValue .r15 = s.regValue .rsi :=
    (eff17.agrees.read (n := 64) (r := 15)
      (by simp [b11651eEffect, Effect.components])).trans r15_in
  have r3_17 : t17.regValue .rbx = s.regValue .rdi :=
    (eff17.agrees.read (n := 64) (r := 3)
      (by simp [b11651eEffect, Effect.components])).trans r3_in
  have r5_17 : t17.regValue .rbp = stackPtr s - 912 :=
    (eff17.agrees.read (n := 64) (r := 5)
      (by simp [b11651eEffect, Effect.components])).trans r5_in
  have r14_17 : t17.regValue .r14 = stackPtr s - 1392 :=
    (eff17.agrees.read (n := 64) (r := 14)
      (by simp [b11651eEffect, Effect.components])).trans r14_in
  have r13_17 : t17.regValue .r13 = stackPtr s - 144 :=
    (eff17.agrees.read (n := 64) (r := 13)
      (by simp [b11651eEffect, Effect.components])).trans r13_in
  have p1680_17 := point_of_external p1680_in mem17
  have p144_17 := point_of_external p144_in mem17
  have p1584_17 := point_of_external p1584_in mem17
  have p912_17 := point_of_external p912_in mem17
  have p1488_17 := point_of_external p1488_in mem17
  obtain ⟨t18, run18, st18, rip18, value18, eff18, _⟩ :=
    copy_generator pre st17 0xe7c5 (by decide) (by decide +kernel)
      eff17.rip 912 (by decide) (by decide) r7_17 r1_17
      r6_17
  have r15_18 : t18.regValue .r15 = s.regValue .rsi :=
    (eff18.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_17
  have r3_18 : t18.regValue .rbx = s.regValue .rdi :=
    (eff18.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_17
  have r5_18 : t18.regValue .rbp = stackPtr s - 912 :=
    (eff18.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_17
  have r12_18 : t18.regValue .r12 = stackPtr s - 912 :=
    (eff18.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_17
  have r14_18 : t18.regValue .r14 = stackPtr s - 1392 :=
    (eff18.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_17
  have r13_18 : t18.regValue .r13 = stackPtr s - 144 :=
    (eff18.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_17
  have p1680_18 := copy_point (offset := 1680) pre eff18 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_17
  have p144_18 := copy_point (offset := 144) pre eff18 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_17
  have p1584_18 := copy_point (offset := 1584) pre eff18 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_17
  have p1488_18 := copy_point (offset := 1488) pre eff18 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_17
  obtain ⟨n19, t19, run19, st19, eff19, mem19⟩ :=
    register_block (offset := 0xe7c8) st18 (b116538_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip18
      (by simp [b116538Effect, Effect.components, Component.Covers])
      (by simp [b116538Effect, Effect.components])
      (by simp [b116538Effect, Effect.components])
      (by simp [b116538Effect, Effect.components])
      (by simp [b116538Effect, Effect.components])
  have r7_19 : t19.regValue .rdi = stackPtr s - 912 :=
    eff19.writes.1.trans r12_18
  have r6_19 : t19.regValue .rsi = stackPtr s - 144 :=
    eff19.writes.2.trans r13_18
  have r15_19 : t19.regValue .r15 = s.regValue .rsi :=
    (eff19.agrees.read (n := 64) (r := 15)
      (by simp [b116538Effect, Effect.components])).trans r15_18
  have r3_19 : t19.regValue .rbx = s.regValue .rdi :=
    (eff19.agrees.read (n := 64) (r := 3)
      (by simp [b116538Effect, Effect.components])).trans r3_18
  have r5_19 : t19.regValue .rbp = stackPtr s - 912 :=
    (eff19.agrees.read (n := 64) (r := 5)
      (by simp [b116538Effect, Effect.components])).trans r5_18
  have r12_19 : t19.regValue .r12 = stackPtr s - 912 :=
    (eff19.agrees.read (n := 64) (r := 12)
      (by simp [b116538Effect, Effect.components])).trans r12_18
  have r14_19 : t19.regValue .r14 = stackPtr s - 1392 :=
    (eff19.agrees.read (n := 64) (r := 14)
      (by simp [b116538Effect, Effect.components])).trans r14_18
  have r13_19 : t19.regValue .r13 = stackPtr s - 144 :=
    (eff19.agrees.read (n := 64) (r := 13)
      (by simp [b116538Effect, Effect.components])).trans r13_18
  have p1680_19 := point_of_external p1680_18 mem19
  have p144_19 := point_of_external p144_18 mem19
  have p1584_19 := point_of_external p1584_18 mem19
  have p912_19 := point_of_external value18 mem19
  have p1488_19 := point_of_external p1488_18 mem19
  obtain ⟨t20, result20⟩ :=
    add_call pre st19 add11653e eff19.rip
      r7_19 r6_19 p912_19 p144_19
  obtain ⟨n20, run20⟩ := result20.execution
  have st20 := result20.toFrameState
  have value20 : ProjectiveAt t20 (stackPtr s - 912)
      (Projective.tableEntry basePoint 3) := result20.value
  have r15_20 : t20.regValue .r15 = s.regValue .rsi :=
    (result20.registers .r15 (by simp)).trans r15_19
  have r3_20 : t20.regValue .rbx = s.regValue .rdi :=
    (result20.registers .rbx (by simp)).trans r3_19
  have r5_20 : t20.regValue .rbp = stackPtr s - 912 :=
    (result20.registers .rbp (by simp)).trans r5_19
  have r12_20 : t20.regValue .r12 = stackPtr s - 912 :=
    (result20.registers .r12 (by simp)).trans r12_19
  have r14_20 : t20.regValue .r14 = stackPtr s - 1392 :=
    (result20.registers .r14 (by simp)).trans r14_19
  have r13_20 : t20.regValue .r13 = stackPtr s - 144 :=
    (result20.registers .r13 (by simp)).trans r13_19
  have p1680_20 := call_point (offset := 1680) result20 (by decide) (by decide) (by decide) p1680_19
  have p144_20 := call_point (offset := 144) result20 (by decide) (by decide) (by decide) p144_19
  have p1584_20 := call_point (offset := 1584) result20 (by decide) (by decide) (by decide) p1584_19
  have p1488_20 := call_point (offset := 1488) result20 (by decide) (by decide) (by decide) p1488_19
  obtain ⟨n21, t21, run21, st21, eff21, mem21⟩ :=
    register_block (offset := 0xe7d3) st20 (b116543_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result20.rip
      (by simp [b116543Effect, Effect.components, Component.Covers])
      (by simp [b116543Effect, Effect.components])
      (by simp [b116543Effect, Effect.components])
      (by simp [b116543Effect, Effect.components])
      (by simp [b116543Effect, Effect.components])
  have r1_21 : t21.regValue .rcx = 12 := eff21.writes.1
  have r7_21 : t21.regValue .rdi = stackPtr s - 144 :=
    eff21.writes.2.1.trans r13_20
  have r6_21 : t21.regValue .rsi = stackPtr s - 912 :=
    eff21.writes.2.2.trans r12_20
  have r15_21 : t21.regValue .r15 = s.regValue .rsi :=
    (eff21.agrees.read (n := 64) (r := 15)
      (by simp [b116543Effect, Effect.components])).trans r15_20
  have r3_21 : t21.regValue .rbx = s.regValue .rdi :=
    (eff21.agrees.read (n := 64) (r := 3)
      (by simp [b116543Effect, Effect.components])).trans r3_20
  have r5_21 : t21.regValue .rbp = stackPtr s - 912 :=
    (eff21.agrees.read (n := 64) (r := 5)
      (by simp [b116543Effect, Effect.components])).trans r5_20
  have r12_21 : t21.regValue .r12 = stackPtr s - 912 :=
    (eff21.agrees.read (n := 64) (r := 12)
      (by simp [b116543Effect, Effect.components])).trans r12_20
  have r14_21 : t21.regValue .r14 = stackPtr s - 1392 :=
    (eff21.agrees.read (n := 64) (r := 14)
      (by simp [b116543Effect, Effect.components])).trans r14_20
  have r13_21 : t21.regValue .r13 = stackPtr s - 144 :=
    (eff21.agrees.read (n := 64) (r := 13)
      (by simp [b116543Effect, Effect.components])).trans r13_20
  have p1680_21 := point_of_external p1680_20 mem21
  have p144_21 := point_of_external p144_20 mem21
  have p1584_21 := point_of_external p1584_20 mem21
  have p912_21 := point_of_external value20 mem21
  have p1488_21 := point_of_external p1488_20 mem21
  obtain ⟨t22, run22, st22, rip22, value22, eff22, _⟩ :=
    copy_stack (sourceOffset := 912) pre st21 0xe7de (by decide) (by decide +kernel)
      eff21.rip 144 (by decide) (by decide) r7_21 r1_21
      (by decide) (by decide) (by decide) r6_21 p912_21
  have r15_22 : t22.regValue .r15 = s.regValue .rsi :=
    (eff22.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_21
  have r3_22 : t22.regValue .rbx = s.regValue .rdi :=
    (eff22.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_21
  have r5_22 : t22.regValue .rbp = stackPtr s - 912 :=
    (eff22.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_21
  have r12_22 : t22.regValue .r12 = stackPtr s - 912 :=
    (eff22.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_21
  have r14_22 : t22.regValue .r14 = stackPtr s - 1392 :=
    (eff22.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_21
  have r13_22 : t22.regValue .r13 = stackPtr s - 144 :=
    (eff22.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_21
  have p1680_22 := copy_point (offset := 1680) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_21
  have p1584_22 := copy_point (offset := 1584) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_21
  have p912_22 := copy_point (offset := 912) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_21
  have p1488_22 := copy_point (offset := 1488) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_21
  obtain ⟨n23, t23, run23, st23, eff23, mem23⟩ :=
    register_block (offset := 0xe7e1) st22 (b116551_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip22
      (by simp [b116551Effect, Effect.components, Component.Covers])
      (by simp [b116551Effect, Effect.components])
      (by simp [b116551Effect, Effect.components])
      (by simp [b116551Effect, Effect.components])
      (by simp [b116551Effect, Effect.components])
  have r1_23 : t23.regValue .rcx = 12 := eff23.writes.1
  have r7_23 : t23.regValue .rdi = stackPtr s - 1392 :=
    eff23.writes.2.1.trans r14_22
  have r6_23 : t23.regValue .rsi = stackPtr s - 144 :=
    eff23.writes.2.2.trans r13_22
  have r15_23 : t23.regValue .r15 = s.regValue .rsi :=
    (eff23.agrees.read (n := 64) (r := 15)
      (by simp [b116551Effect, Effect.components])).trans r15_22
  have r3_23 : t23.regValue .rbx = s.regValue .rdi :=
    (eff23.agrees.read (n := 64) (r := 3)
      (by simp [b116551Effect, Effect.components])).trans r3_22
  have r5_23 : t23.regValue .rbp = stackPtr s - 912 :=
    (eff23.agrees.read (n := 64) (r := 5)
      (by simp [b116551Effect, Effect.components])).trans r5_22
  have r12_23 : t23.regValue .r12 = stackPtr s - 912 :=
    (eff23.agrees.read (n := 64) (r := 12)
      (by simp [b116551Effect, Effect.components])).trans r12_22
  have r14_23 : t23.regValue .r14 = stackPtr s - 1392 :=
    (eff23.agrees.read (n := 64) (r := 14)
      (by simp [b116551Effect, Effect.components])).trans r14_22
  have r13_23 : t23.regValue .r13 = stackPtr s - 144 :=
    (eff23.agrees.read (n := 64) (r := 13)
      (by simp [b116551Effect, Effect.components])).trans r13_22
  have p1680_23 := point_of_external p1680_22 mem23
  have p144_23 := point_of_external value22 mem23
  have p1584_23 := point_of_external p1584_22 mem23
  have p912_23 := point_of_external p912_22 mem23
  have p1488_23 := point_of_external p1488_22 mem23
  obtain ⟨t24, run24, st24, rip24, value24, eff24, _⟩ :=
    copy_stack (sourceOffset := 144) pre st23 0xe7ec (by decide) (by decide +kernel)
      eff23.rip 1392 (by decide) (by decide) r7_23 r1_23
      (by decide) (by decide) (by decide) r6_23 p144_23
  have r15_24 : t24.regValue .r15 = s.regValue .rsi :=
    (eff24.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_23
  have r3_24 : t24.regValue .rbx = s.regValue .rdi :=
    (eff24.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_23
  have r5_24 : t24.regValue .rbp = stackPtr s - 912 :=
    (eff24.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_23
  have r12_24 : t24.regValue .r12 = stackPtr s - 912 :=
    (eff24.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_23
  have r14_24 : t24.regValue .r14 = stackPtr s - 1392 :=
    (eff24.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_23
  have r13_24 : t24.regValue .r13 = stackPtr s - 144 :=
    (eff24.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_23
  have p1680_24 := copy_point (offset := 1680) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_23
  have p144_24 := copy_point (offset := 144) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_23
  have p1584_24 := copy_point (offset := 1584) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_23
  have p912_24 := copy_point (offset := 912) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_23
  have p1488_24 := copy_point (offset := 1488) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_23
  exact ⟨n17 + 12 + n19 + n20 + n21 + 12 + n23 + 12, t24, (((((((run17.trans run18).trans
    run19).trans run20).trans run21).trans run22).trans run23).trans run24), st24, rip24,
    ⟨r3_24, r5_24, r12_24, r13_24, r14_24, r15_24, trivial⟩,
    ⟨p144_24, p912_24, value24, p1488_24, p1584_24, p1680_24, trivial⟩⟩

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
