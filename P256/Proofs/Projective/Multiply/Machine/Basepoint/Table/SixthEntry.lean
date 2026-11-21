import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.Memory
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame TableSteps Blocks

theorem sixth_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e835)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12, stackPtr s - 912),
      (.r13, stackPtr s - 144), (.r14, stackPtr s - 912), (.r15, s.regValue .rsi)]
      [(144, Projective.tableEntry basePoint 4), (912, Projective.tableEntry basePoint 4), (1296,
        Projective.tableEntry basePoint 4), (1392, Projective.tableEntry basePoint 3), (1488,
        Projective.tableEntry basePoint 2), (1584, Projective.tableEntry basePoint 1), (1680,
        Projective.tableEntry basePoint 0)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = 0x10e87b ∧ Facts s u [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12,
        stackPtr s - 912), (.r13, stackPtr s - 144), (.r14, stackPtr s - 912), (.r15, s.regValue
        .rsi)]
        [(144, Projective.tableEntry basePoint 5), (912, Projective.tableEntry basePoint 5), (1200,
          Projective.tableEntry basePoint 5), (1296, Projective.tableEntry basePoint 4), (1392,
          Projective.tableEntry basePoint 3), (1488, Projective.tableEntry basePoint 2), (1584,
          Projective.tableEntry basePoint 1), (1680, Projective.tableEntry basePoint 0)] := by
  rcases facts.regs with ⟨r3_in, r5_in, r12_in, r13_in, r14_in, r15_in, trivial⟩
  rcases facts.points with ⟨p144_in, p912_in, p1296_in, p1392_in, p1488_in, p1584_in, p1680_in,
    trivial⟩
  obtain ⟨n33, t33, run33, st33, eff33, mem33⟩ :=
    register_block (offset := 0xe835) state (b1165a5_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b1165a5Effect, Effect.components, Component.Covers])
      (by simp [b1165a5Effect, Effect.components])
      (by simp [b1165a5Effect, Effect.components])
      (by simp [b1165a5Effect, Effect.components])
      (by simp [b1165a5Effect, Effect.components])
  have r14_33 : t33.regValue .r14 = stackPtr s - 912 := by
    have h : t33.regValue .r14 = stackPtr t + 1032 := eff33.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_33 : t33.regValue .rcx = 12 := eff33.writes.2.1
  have r7_33 : t33.regValue .rdi = stackPtr s - 912 := by
    have h : t33.regValue .rdi = stackPtr t + 1032 := eff33.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_33 : t33.regValue .rsi = 2108104 := eff33.writes.2.2.2
  have r15_33 : t33.regValue .r15 = s.regValue .rsi :=
    (eff33.agrees.read (n := 64) (r := 15)
      (by simp [b1165a5Effect, Effect.components])).trans r15_in
  have r3_33 : t33.regValue .rbx = s.regValue .rdi :=
    (eff33.agrees.read (n := 64) (r := 3)
      (by simp [b1165a5Effect, Effect.components])).trans r3_in
  have r5_33 : t33.regValue .rbp = stackPtr s - 912 :=
    (eff33.agrees.read (n := 64) (r := 5)
      (by simp [b1165a5Effect, Effect.components])).trans r5_in
  have r12_33 : t33.regValue .r12 = stackPtr s - 912 :=
    (eff33.agrees.read (n := 64) (r := 12)
      (by simp [b1165a5Effect, Effect.components])).trans r12_in
  have r13_33 : t33.regValue .r13 = stackPtr s - 144 :=
    (eff33.agrees.read (n := 64) (r := 13)
      (by simp [b1165a5Effect, Effect.components])).trans r13_in
  have p1680_33 := point_of_external p1680_in mem33
  have p144_33 := point_of_external p144_in mem33
  have p1584_33 := point_of_external p1584_in mem33
  have p912_33 := point_of_external p912_in mem33
  have p1488_33 := point_of_external p1488_in mem33
  have p1392_33 := point_of_external p1392_in mem33
  have p1296_33 := point_of_external p1296_in mem33
  obtain ⟨t34, run34, st34, rip34, value34, eff34, _⟩ :=
    copy_generator pre st33 0xe84c (by decide) (by decide +kernel)
      eff33.rip 912 (by decide) (by decide) r7_33 r1_33
      r6_33
  have r15_34 : t34.regValue .r15 = s.regValue .rsi :=
    (eff34.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_33
  have r3_34 : t34.regValue .rbx = s.regValue .rdi :=
    (eff34.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_33
  have r5_34 : t34.regValue .rbp = stackPtr s - 912 :=
    (eff34.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_33
  have r12_34 : t34.regValue .r12 = stackPtr s - 912 :=
    (eff34.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_33
  have r14_34 : t34.regValue .r14 = stackPtr s - 912 :=
    (eff34.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_33
  have r13_34 : t34.regValue .r13 = stackPtr s - 144 :=
    (eff34.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_33
  have p1680_34 := copy_point (offset := 1680) pre eff34 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_33
  have p144_34 := copy_point (offset := 144) pre eff34 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_33
  have p1584_34 := copy_point (offset := 1584) pre eff34 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_33
  have p1488_34 := copy_point (offset := 1488) pre eff34 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_33
  have p1392_34 := copy_point (offset := 1392) pre eff34 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_33
  have p1296_34 := copy_point (offset := 1296) pre eff34 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_33
  obtain ⟨n35, t35, run35, st35, eff35, mem35⟩ :=
    register_block (offset := 0xe84f) st34 (b1165bf_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip34
      (by simp [b1165bfEffect, Effect.components, Component.Covers])
      (by simp [b1165bfEffect, Effect.components])
      (by simp [b1165bfEffect, Effect.components])
      (by simp [b1165bfEffect, Effect.components])
      (by simp [b1165bfEffect, Effect.components])
  have r7_35 : t35.regValue .rdi = stackPtr s - 912 :=
    eff35.writes.1.trans r14_34
  have r6_35 : t35.regValue .rsi = stackPtr s - 144 :=
    eff35.writes.2.trans r13_34
  have r15_35 : t35.regValue .r15 = s.regValue .rsi :=
    (eff35.agrees.read (n := 64) (r := 15)
      (by simp [b1165bfEffect, Effect.components])).trans r15_34
  have r3_35 : t35.regValue .rbx = s.regValue .rdi :=
    (eff35.agrees.read (n := 64) (r := 3)
      (by simp [b1165bfEffect, Effect.components])).trans r3_34
  have r5_35 : t35.regValue .rbp = stackPtr s - 912 :=
    (eff35.agrees.read (n := 64) (r := 5)
      (by simp [b1165bfEffect, Effect.components])).trans r5_34
  have r12_35 : t35.regValue .r12 = stackPtr s - 912 :=
    (eff35.agrees.read (n := 64) (r := 12)
      (by simp [b1165bfEffect, Effect.components])).trans r12_34
  have r14_35 : t35.regValue .r14 = stackPtr s - 912 :=
    (eff35.agrees.read (n := 64) (r := 14)
      (by simp [b1165bfEffect, Effect.components])).trans r14_34
  have r13_35 : t35.regValue .r13 = stackPtr s - 144 :=
    (eff35.agrees.read (n := 64) (r := 13)
      (by simp [b1165bfEffect, Effect.components])).trans r13_34
  have p1680_35 := point_of_external p1680_34 mem35
  have p144_35 := point_of_external p144_34 mem35
  have p1584_35 := point_of_external p1584_34 mem35
  have p912_35 := point_of_external value34 mem35
  have p1488_35 := point_of_external p1488_34 mem35
  have p1392_35 := point_of_external p1392_34 mem35
  have p1296_35 := point_of_external p1296_34 mem35
  obtain ⟨t36, result36⟩ :=
    add_call pre st35 add1165c5 eff35.rip
      r7_35 r6_35 p912_35 p144_35
  obtain ⟨n36, run36⟩ := result36.execution
  have st36 := result36.toFrameState
  have value36 : ProjectiveAt t36 (stackPtr s - 912)
      (Projective.tableEntry basePoint 5) := result36.value
  have r15_36 : t36.regValue .r15 = s.regValue .rsi :=
    (result36.registers .r15 (by simp)).trans r15_35
  have r3_36 : t36.regValue .rbx = s.regValue .rdi :=
    (result36.registers .rbx (by simp)).trans r3_35
  have r5_36 : t36.regValue .rbp = stackPtr s - 912 :=
    (result36.registers .rbp (by simp)).trans r5_35
  have r12_36 : t36.regValue .r12 = stackPtr s - 912 :=
    (result36.registers .r12 (by simp)).trans r12_35
  have r14_36 : t36.regValue .r14 = stackPtr s - 912 :=
    (result36.registers .r14 (by simp)).trans r14_35
  have r13_36 : t36.regValue .r13 = stackPtr s - 144 :=
    (result36.registers .r13 (by simp)).trans r13_35
  have p1680_36 := call_point (offset := 1680) result36 (by decide) (by decide) (by decide) p1680_35
  have p144_36 := call_point (offset := 144) result36 (by decide) (by decide) (by decide) p144_35
  have p1584_36 := call_point (offset := 1584) result36 (by decide) (by decide) (by decide) p1584_35
  have p1488_36 := call_point (offset := 1488) result36 (by decide) (by decide) (by decide) p1488_35
  have p1392_36 := call_point (offset := 1392) result36 (by decide) (by decide) (by decide) p1392_35
  have p1296_36 := call_point (offset := 1296) result36 (by decide) (by decide) (by decide) p1296_35
  obtain ⟨n37, t37, run37, st37, eff37, mem37⟩ :=
    register_block (offset := 0xe85a) st36 (b1165ca_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result36.rip
      (by simp [b1165caEffect, Effect.components, Component.Covers])
      (by simp [b1165caEffect, Effect.components])
      (by simp [b1165caEffect, Effect.components])
      (by simp [b1165caEffect, Effect.components])
      (by simp [b1165caEffect, Effect.components])
  have r1_37 : t37.regValue .rcx = 12 := eff37.writes.1
  have r7_37 : t37.regValue .rdi = stackPtr s - 144 :=
    eff37.writes.2.1.trans r13_36
  have r6_37 : t37.regValue .rsi = stackPtr s - 912 :=
    eff37.writes.2.2.trans r14_36
  have r15_37 : t37.regValue .r15 = s.regValue .rsi :=
    (eff37.agrees.read (n := 64) (r := 15)
      (by simp [b1165caEffect, Effect.components])).trans r15_36
  have r3_37 : t37.regValue .rbx = s.regValue .rdi :=
    (eff37.agrees.read (n := 64) (r := 3)
      (by simp [b1165caEffect, Effect.components])).trans r3_36
  have r5_37 : t37.regValue .rbp = stackPtr s - 912 :=
    (eff37.agrees.read (n := 64) (r := 5)
      (by simp [b1165caEffect, Effect.components])).trans r5_36
  have r12_37 : t37.regValue .r12 = stackPtr s - 912 :=
    (eff37.agrees.read (n := 64) (r := 12)
      (by simp [b1165caEffect, Effect.components])).trans r12_36
  have r14_37 : t37.regValue .r14 = stackPtr s - 912 :=
    (eff37.agrees.read (n := 64) (r := 14)
      (by simp [b1165caEffect, Effect.components])).trans r14_36
  have r13_37 : t37.regValue .r13 = stackPtr s - 144 :=
    (eff37.agrees.read (n := 64) (r := 13)
      (by simp [b1165caEffect, Effect.components])).trans r13_36
  have p1680_37 := point_of_external p1680_36 mem37
  have p144_37 := point_of_external p144_36 mem37
  have p1584_37 := point_of_external p1584_36 mem37
  have p912_37 := point_of_external value36 mem37
  have p1488_37 := point_of_external p1488_36 mem37
  have p1392_37 := point_of_external p1392_36 mem37
  have p1296_37 := point_of_external p1296_36 mem37
  obtain ⟨t38, run38, st38, rip38, value38, eff38, _⟩ :=
    copy_stack (sourceOffset := 912) pre st37 0xe865 (by decide) (by decide +kernel)
      eff37.rip 144 (by decide) (by decide) r7_37 r1_37
      (by decide) (by decide) (by decide) r6_37 p912_37
  have r15_38 : t38.regValue .r15 = s.regValue .rsi :=
    (eff38.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_37
  have r3_38 : t38.regValue .rbx = s.regValue .rdi :=
    (eff38.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_37
  have r5_38 : t38.regValue .rbp = stackPtr s - 912 :=
    (eff38.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_37
  have r12_38 : t38.regValue .r12 = stackPtr s - 912 :=
    (eff38.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_37
  have r14_38 : t38.regValue .r14 = stackPtr s - 912 :=
    (eff38.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_37
  have r13_38 : t38.regValue .r13 = stackPtr s - 144 :=
    (eff38.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_37
  have p1680_38 := copy_point (offset := 1680) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_37
  have p1584_38 := copy_point (offset := 1584) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_37
  have p912_38 := copy_point (offset := 912) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_37
  have p1488_38 := copy_point (offset := 1488) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_37
  have p1392_38 := copy_point (offset := 1392) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_37
  have p1296_38 := copy_point (offset := 1296) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_37
  obtain ⟨n39, t39, run39, st39, eff39, mem39⟩ :=
    register_block (offset := 0xe868) st38 (b1165d8_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip38
      (by simp [b1165d8Effect, Effect.components, Component.Covers])
      (by simp [b1165d8Effect, Effect.components])
      (by simp [b1165d8Effect, Effect.components])
      (by simp [b1165d8Effect, Effect.components])
      (by simp [b1165d8Effect, Effect.components])
  have r1_39 : t39.regValue .rcx = 12 := eff39.writes.1
  have r7_39 : t39.regValue .rdi = stackPtr s - 1200 := by
    have h : t39.regValue .rdi = stackPtr t38 + 744 := eff39.writes.2.1
    exact h.trans (scalar_stack_address st38.rsp (by decide) (by decide))
  have r6_39 : t39.regValue .rsi = stackPtr s - 144 :=
    eff39.writes.2.2.trans r13_38
  have r15_39 : t39.regValue .r15 = s.regValue .rsi :=
    (eff39.agrees.read (n := 64) (r := 15)
      (by simp [b1165d8Effect, Effect.components])).trans r15_38
  have r3_39 : t39.regValue .rbx = s.regValue .rdi :=
    (eff39.agrees.read (n := 64) (r := 3)
      (by simp [b1165d8Effect, Effect.components])).trans r3_38
  have r5_39 : t39.regValue .rbp = stackPtr s - 912 :=
    (eff39.agrees.read (n := 64) (r := 5)
      (by simp [b1165d8Effect, Effect.components])).trans r5_38
  have r12_39 : t39.regValue .r12 = stackPtr s - 912 :=
    (eff39.agrees.read (n := 64) (r := 12)
      (by simp [b1165d8Effect, Effect.components])).trans r12_38
  have r14_39 : t39.regValue .r14 = stackPtr s - 912 :=
    (eff39.agrees.read (n := 64) (r := 14)
      (by simp [b1165d8Effect, Effect.components])).trans r14_38
  have r13_39 : t39.regValue .r13 = stackPtr s - 144 :=
    (eff39.agrees.read (n := 64) (r := 13)
      (by simp [b1165d8Effect, Effect.components])).trans r13_38
  have p1680_39 := point_of_external p1680_38 mem39
  have p144_39 := point_of_external value38 mem39
  have p1584_39 := point_of_external p1584_38 mem39
  have p912_39 := point_of_external p912_38 mem39
  have p1488_39 := point_of_external p1488_38 mem39
  have p1392_39 := point_of_external p1392_38 mem39
  have p1296_39 := point_of_external p1296_38 mem39
  obtain ⟨t40, run40, st40, rip40, value40, eff40, _⟩ :=
    copy_stack (sourceOffset := 144) pre st39 0xe878 (by decide) (by decide +kernel)
      eff39.rip 1200 (by decide) (by decide) r7_39 r1_39
      (by decide) (by decide) (by decide) r6_39 p144_39
  have r15_40 : t40.regValue .r15 = s.regValue .rsi :=
    (eff40.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_39
  have r3_40 : t40.regValue .rbx = s.regValue .rdi :=
    (eff40.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_39
  have r5_40 : t40.regValue .rbp = stackPtr s - 912 :=
    (eff40.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_39
  have r12_40 : t40.regValue .r12 = stackPtr s - 912 :=
    (eff40.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_39
  have r14_40 : t40.regValue .r14 = stackPtr s - 912 :=
    (eff40.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_39
  have r13_40 : t40.regValue .r13 = stackPtr s - 144 :=
    (eff40.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_39
  have p1680_40 := copy_point (offset := 1680) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_39
  have p144_40 := copy_point (offset := 144) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_39
  have p1584_40 := copy_point (offset := 1584) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_39
  have p912_40 := copy_point (offset := 912) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_39
  have p1488_40 := copy_point (offset := 1488) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_39
  have p1392_40 := copy_point (offset := 1392) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_39
  have p1296_40 := copy_point (offset := 1296) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_39
  exact ⟨n33 + 12 + n35 + n36 + n37 + 12 + n39 + 12, t40, (((((((run33.trans run34).trans
    run35).trans run36).trans run37).trans run38).trans run39).trans run40), st40, rip40,
    ⟨r3_40, r5_40, r12_40, r13_40, r14_40, r15_40, trivial⟩,
    ⟨p144_40, p912_40, value40, p1296_40, p1392_40, p1488_40, p1584_40, p1680_40, trivial⟩⟩

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
