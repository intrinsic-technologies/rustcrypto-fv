import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.Memory
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame TableSteps Blocks

theorem eighth_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e8c1)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12, stackPtr s - 912),
      (.r13, stackPtr s - 144), (.r14, stackPtr s - 912), (.r15, s.regValue .rsi)]
      [(144, Projective.tableEntry basePoint 6), (912, Projective.tableEntry basePoint 6), (1104,
        Projective.tableEntry basePoint 6), (1200, Projective.tableEntry basePoint 5), (1296,
        Projective.tableEntry basePoint 4), (1392, Projective.tableEntry basePoint 3), (1488,
        Projective.tableEntry basePoint 2), (1584, Projective.tableEntry basePoint 1), (1680,
        Projective.tableEntry basePoint 0)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = 0x10e907 ∧ Facts s u [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12,
        stackPtr s - 912), (.r13, stackPtr s - 144), (.r14, stackPtr s - 912), (.r15, s.regValue
        .rsi)]
        [(144, Projective.tableEntry basePoint 7), (912, Projective.tableEntry basePoint 7), (1008,
          Projective.tableEntry basePoint 7), (1104, Projective.tableEntry basePoint 6), (1200,
          Projective.tableEntry basePoint 5), (1296, Projective.tableEntry basePoint 4), (1392,
          Projective.tableEntry basePoint 3), (1488, Projective.tableEntry basePoint 2), (1584,
          Projective.tableEntry basePoint 1), (1680, Projective.tableEntry basePoint 0)] := by
  rcases facts.regs with ⟨r3_in, r5_in, r12_in, r13_in, r14_in, r15_in, trivial⟩
  rcases facts.points with ⟨p144_in, p912_in, p1104_in, p1200_in, p1296_in, p1392_in, p1488_in,
    p1584_in, p1680_in, trivial⟩
  obtain ⟨n49, t49, run49, st49, eff49, mem49⟩ :=
    register_block (offset := 0xe8c1) state (b116631_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b116631Effect, Effect.components, Component.Covers])
      (by simp [b116631Effect, Effect.components])
      (by simp [b116631Effect, Effect.components])
      (by simp [b116631Effect, Effect.components])
      (by simp [b116631Effect, Effect.components])
  have r14_49 : t49.regValue .r14 = stackPtr s - 912 := by
    have h : t49.regValue .r14 = stackPtr t + 1032 := eff49.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_49 : t49.regValue .rcx = 12 := eff49.writes.2.1
  have r7_49 : t49.regValue .rdi = stackPtr s - 912 := by
    have h : t49.regValue .rdi = stackPtr t + 1032 := eff49.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_49 : t49.regValue .rsi = 2108104 := eff49.writes.2.2.2
  have r15_49 : t49.regValue .r15 = s.regValue .rsi :=
    (eff49.agrees.read (n := 64) (r := 15)
      (by simp [b116631Effect, Effect.components])).trans r15_in
  have r3_49 : t49.regValue .rbx = s.regValue .rdi :=
    (eff49.agrees.read (n := 64) (r := 3)
      (by simp [b116631Effect, Effect.components])).trans r3_in
  have r5_49 : t49.regValue .rbp = stackPtr s - 912 :=
    (eff49.agrees.read (n := 64) (r := 5)
      (by simp [b116631Effect, Effect.components])).trans r5_in
  have r12_49 : t49.regValue .r12 = stackPtr s - 912 :=
    (eff49.agrees.read (n := 64) (r := 12)
      (by simp [b116631Effect, Effect.components])).trans r12_in
  have r13_49 : t49.regValue .r13 = stackPtr s - 144 :=
    (eff49.agrees.read (n := 64) (r := 13)
      (by simp [b116631Effect, Effect.components])).trans r13_in
  have p1680_49 := point_of_external p1680_in mem49
  have p144_49 := point_of_external p144_in mem49
  have p1584_49 := point_of_external p1584_in mem49
  have p912_49 := point_of_external p912_in mem49
  have p1488_49 := point_of_external p1488_in mem49
  have p1392_49 := point_of_external p1392_in mem49
  have p1296_49 := point_of_external p1296_in mem49
  have p1200_49 := point_of_external p1200_in mem49
  have p1104_49 := point_of_external p1104_in mem49
  obtain ⟨t50, run50, st50, rip50, value50, eff50, _⟩ :=
    copy_generator pre st49 0xe8d8 (by decide) (by decide +kernel)
      eff49.rip 912 (by decide) (by decide) r7_49 r1_49
      r6_49
  have r15_50 : t50.regValue .r15 = s.regValue .rsi :=
    (eff50.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_49
  have r3_50 : t50.regValue .rbx = s.regValue .rdi :=
    (eff50.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_49
  have r5_50 : t50.regValue .rbp = stackPtr s - 912 :=
    (eff50.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_49
  have r12_50 : t50.regValue .r12 = stackPtr s - 912 :=
    (eff50.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_49
  have r14_50 : t50.regValue .r14 = stackPtr s - 912 :=
    (eff50.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_49
  have r13_50 : t50.regValue .r13 = stackPtr s - 144 :=
    (eff50.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_49
  have p1680_50 := copy_point (offset := 1680) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_49
  have p144_50 := copy_point (offset := 144) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_49
  have p1584_50 := copy_point (offset := 1584) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_49
  have p1488_50 := copy_point (offset := 1488) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_49
  have p1392_50 := copy_point (offset := 1392) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_49
  have p1296_50 := copy_point (offset := 1296) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_49
  have p1200_50 := copy_point (offset := 1200) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1200_49
  have p1104_50 := copy_point (offset := 1104) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1104_49
  obtain ⟨n51, t51, run51, st51, eff51, mem51⟩ :=
    register_block (offset := 0xe8db) st50 (b11664b_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip50
      (by simp [b11664bEffect, Effect.components, Component.Covers])
      (by simp [b11664bEffect, Effect.components])
      (by simp [b11664bEffect, Effect.components])
      (by simp [b11664bEffect, Effect.components])
      (by simp [b11664bEffect, Effect.components])
  have r7_51 : t51.regValue .rdi = stackPtr s - 912 :=
    eff51.writes.1.trans r14_50
  have r6_51 : t51.regValue .rsi = stackPtr s - 144 :=
    eff51.writes.2.trans r13_50
  have r15_51 : t51.regValue .r15 = s.regValue .rsi :=
    (eff51.agrees.read (n := 64) (r := 15)
      (by simp [b11664bEffect, Effect.components])).trans r15_50
  have r3_51 : t51.regValue .rbx = s.regValue .rdi :=
    (eff51.agrees.read (n := 64) (r := 3)
      (by simp [b11664bEffect, Effect.components])).trans r3_50
  have r5_51 : t51.regValue .rbp = stackPtr s - 912 :=
    (eff51.agrees.read (n := 64) (r := 5)
      (by simp [b11664bEffect, Effect.components])).trans r5_50
  have r12_51 : t51.regValue .r12 = stackPtr s - 912 :=
    (eff51.agrees.read (n := 64) (r := 12)
      (by simp [b11664bEffect, Effect.components])).trans r12_50
  have r14_51 : t51.regValue .r14 = stackPtr s - 912 :=
    (eff51.agrees.read (n := 64) (r := 14)
      (by simp [b11664bEffect, Effect.components])).trans r14_50
  have r13_51 : t51.regValue .r13 = stackPtr s - 144 :=
    (eff51.agrees.read (n := 64) (r := 13)
      (by simp [b11664bEffect, Effect.components])).trans r13_50
  have p1680_51 := point_of_external p1680_50 mem51
  have p144_51 := point_of_external p144_50 mem51
  have p1584_51 := point_of_external p1584_50 mem51
  have p912_51 := point_of_external value50 mem51
  have p1488_51 := point_of_external p1488_50 mem51
  have p1392_51 := point_of_external p1392_50 mem51
  have p1296_51 := point_of_external p1296_50 mem51
  have p1200_51 := point_of_external p1200_50 mem51
  have p1104_51 := point_of_external p1104_50 mem51
  obtain ⟨t52, result52⟩ :=
    add_call pre st51 add116651 eff51.rip
      r7_51 r6_51 p912_51 p144_51
  obtain ⟨n52, run52⟩ := result52.execution
  have st52 := result52.toFrameState
  have value52 : ProjectiveAt t52 (stackPtr s - 912)
      (Projective.tableEntry basePoint 7) := result52.value
  have r15_52 : t52.regValue .r15 = s.regValue .rsi :=
    (result52.registers .r15 (by simp)).trans r15_51
  have r3_52 : t52.regValue .rbx = s.regValue .rdi :=
    (result52.registers .rbx (by simp)).trans r3_51
  have r5_52 : t52.regValue .rbp = stackPtr s - 912 :=
    (result52.registers .rbp (by simp)).trans r5_51
  have r12_52 : t52.regValue .r12 = stackPtr s - 912 :=
    (result52.registers .r12 (by simp)).trans r12_51
  have r14_52 : t52.regValue .r14 = stackPtr s - 912 :=
    (result52.registers .r14 (by simp)).trans r14_51
  have r13_52 : t52.regValue .r13 = stackPtr s - 144 :=
    (result52.registers .r13 (by simp)).trans r13_51
  have p1680_52 := call_point (offset := 1680) result52 (by decide) (by decide) (by decide) p1680_51
  have p144_52 := call_point (offset := 144) result52 (by decide) (by decide) (by decide) p144_51
  have p1584_52 := call_point (offset := 1584) result52 (by decide) (by decide) (by decide) p1584_51
  have p1488_52 := call_point (offset := 1488) result52 (by decide) (by decide) (by decide) p1488_51
  have p1392_52 := call_point (offset := 1392) result52 (by decide) (by decide) (by decide) p1392_51
  have p1296_52 := call_point (offset := 1296) result52 (by decide) (by decide) (by decide) p1296_51
  have p1200_52 := call_point (offset := 1200) result52 (by decide) (by decide) (by decide) p1200_51
  have p1104_52 := call_point (offset := 1104) result52 (by decide) (by decide) (by decide) p1104_51
  obtain ⟨n53, t53, run53, st53, eff53, mem53⟩ :=
    register_block (offset := 0xe8e6) st52 (b116656_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result52.rip
      (by simp [b116656Effect, Effect.components, Component.Covers])
      (by simp [b116656Effect, Effect.components])
      (by simp [b116656Effect, Effect.components])
      (by simp [b116656Effect, Effect.components])
      (by simp [b116656Effect, Effect.components])
  have r1_53 : t53.regValue .rcx = 12 := eff53.writes.1
  have r7_53 : t53.regValue .rdi = stackPtr s - 144 :=
    eff53.writes.2.1.trans r13_52
  have r6_53 : t53.regValue .rsi = stackPtr s - 912 :=
    eff53.writes.2.2.trans r14_52
  have r15_53 : t53.regValue .r15 = s.regValue .rsi :=
    (eff53.agrees.read (n := 64) (r := 15)
      (by simp [b116656Effect, Effect.components])).trans r15_52
  have r3_53 : t53.regValue .rbx = s.regValue .rdi :=
    (eff53.agrees.read (n := 64) (r := 3)
      (by simp [b116656Effect, Effect.components])).trans r3_52
  have r5_53 : t53.regValue .rbp = stackPtr s - 912 :=
    (eff53.agrees.read (n := 64) (r := 5)
      (by simp [b116656Effect, Effect.components])).trans r5_52
  have r12_53 : t53.regValue .r12 = stackPtr s - 912 :=
    (eff53.agrees.read (n := 64) (r := 12)
      (by simp [b116656Effect, Effect.components])).trans r12_52
  have r14_53 : t53.regValue .r14 = stackPtr s - 912 :=
    (eff53.agrees.read (n := 64) (r := 14)
      (by simp [b116656Effect, Effect.components])).trans r14_52
  have r13_53 : t53.regValue .r13 = stackPtr s - 144 :=
    (eff53.agrees.read (n := 64) (r := 13)
      (by simp [b116656Effect, Effect.components])).trans r13_52
  have p1680_53 := point_of_external p1680_52 mem53
  have p144_53 := point_of_external p144_52 mem53
  have p1584_53 := point_of_external p1584_52 mem53
  have p912_53 := point_of_external value52 mem53
  have p1488_53 := point_of_external p1488_52 mem53
  have p1392_53 := point_of_external p1392_52 mem53
  have p1296_53 := point_of_external p1296_52 mem53
  have p1200_53 := point_of_external p1200_52 mem53
  have p1104_53 := point_of_external p1104_52 mem53
  obtain ⟨t54, run54, st54, rip54, value54, eff54, _⟩ :=
    copy_stack (sourceOffset := 912) pre st53 0xe8f1 (by decide) (by decide +kernel)
      eff53.rip 144 (by decide) (by decide) r7_53 r1_53
      (by decide) (by decide) (by decide) r6_53 p912_53
  have r15_54 : t54.regValue .r15 = s.regValue .rsi :=
    (eff54.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_53
  have r3_54 : t54.regValue .rbx = s.regValue .rdi :=
    (eff54.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_53
  have r5_54 : t54.regValue .rbp = stackPtr s - 912 :=
    (eff54.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_53
  have r12_54 : t54.regValue .r12 = stackPtr s - 912 :=
    (eff54.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_53
  have r14_54 : t54.regValue .r14 = stackPtr s - 912 :=
    (eff54.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_53
  have r13_54 : t54.regValue .r13 = stackPtr s - 144 :=
    (eff54.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_53
  have p1680_54 := copy_point (offset := 1680) pre eff54 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_53
  have p1584_54 := copy_point (offset := 1584) pre eff54 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_53
  have p912_54 := copy_point (offset := 912) pre eff54 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_53
  have p1488_54 := copy_point (offset := 1488) pre eff54 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_53
  have p1392_54 := copy_point (offset := 1392) pre eff54 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_53
  have p1296_54 := copy_point (offset := 1296) pre eff54 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_53
  have p1200_54 := copy_point (offset := 1200) pre eff54 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1200_53
  have p1104_54 := copy_point (offset := 1104) pre eff54 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1104_53
  obtain ⟨n55, t55, run55, st55, eff55, mem55⟩ :=
    register_block (offset := 0xe8f4) st54 (b116664_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip54
      (by simp [b116664Effect, Effect.components, Component.Covers])
      (by simp [b116664Effect, Effect.components])
      (by simp [b116664Effect, Effect.components])
      (by simp [b116664Effect, Effect.components])
      (by simp [b116664Effect, Effect.components])
  have r1_55 : t55.regValue .rcx = 12 := eff55.writes.1
  have r7_55 : t55.regValue .rdi = stackPtr s - 1008 := by
    have h : t55.regValue .rdi = stackPtr t54 + 936 := eff55.writes.2.1
    exact h.trans (scalar_stack_address st54.rsp (by decide) (by decide))
  have r6_55 : t55.regValue .rsi = stackPtr s - 144 :=
    eff55.writes.2.2.trans r13_54
  have r15_55 : t55.regValue .r15 = s.regValue .rsi :=
    (eff55.agrees.read (n := 64) (r := 15)
      (by simp [b116664Effect, Effect.components])).trans r15_54
  have r3_55 : t55.regValue .rbx = s.regValue .rdi :=
    (eff55.agrees.read (n := 64) (r := 3)
      (by simp [b116664Effect, Effect.components])).trans r3_54
  have r5_55 : t55.regValue .rbp = stackPtr s - 912 :=
    (eff55.agrees.read (n := 64) (r := 5)
      (by simp [b116664Effect, Effect.components])).trans r5_54
  have r12_55 : t55.regValue .r12 = stackPtr s - 912 :=
    (eff55.agrees.read (n := 64) (r := 12)
      (by simp [b116664Effect, Effect.components])).trans r12_54
  have r14_55 : t55.regValue .r14 = stackPtr s - 912 :=
    (eff55.agrees.read (n := 64) (r := 14)
      (by simp [b116664Effect, Effect.components])).trans r14_54
  have r13_55 : t55.regValue .r13 = stackPtr s - 144 :=
    (eff55.agrees.read (n := 64) (r := 13)
      (by simp [b116664Effect, Effect.components])).trans r13_54
  have p1680_55 := point_of_external p1680_54 mem55
  have p144_55 := point_of_external value54 mem55
  have p1584_55 := point_of_external p1584_54 mem55
  have p912_55 := point_of_external p912_54 mem55
  have p1488_55 := point_of_external p1488_54 mem55
  have p1392_55 := point_of_external p1392_54 mem55
  have p1296_55 := point_of_external p1296_54 mem55
  have p1200_55 := point_of_external p1200_54 mem55
  have p1104_55 := point_of_external p1104_54 mem55
  obtain ⟨t56, run56, st56, rip56, value56, eff56, _⟩ :=
    copy_stack (sourceOffset := 144) pre st55 0xe904 (by decide) (by decide +kernel)
      eff55.rip 1008 (by decide) (by decide) r7_55 r1_55
      (by decide) (by decide) (by decide) r6_55 p144_55
  have r15_56 : t56.regValue .r15 = s.regValue .rsi :=
    (eff56.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_55
  have r3_56 : t56.regValue .rbx = s.regValue .rdi :=
    (eff56.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_55
  have r5_56 : t56.regValue .rbp = stackPtr s - 912 :=
    (eff56.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_55
  have r12_56 : t56.regValue .r12 = stackPtr s - 912 :=
    (eff56.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_55
  have r14_56 : t56.regValue .r14 = stackPtr s - 912 :=
    (eff56.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_55
  have r13_56 : t56.regValue .r13 = stackPtr s - 144 :=
    (eff56.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_55
  have p1680_56 := copy_point (offset := 1680) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_55
  have p144_56 := copy_point (offset := 144) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_55
  have p1584_56 := copy_point (offset := 1584) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_55
  have p912_56 := copy_point (offset := 912) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_55
  have p1488_56 := copy_point (offset := 1488) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_55
  have p1392_56 := copy_point (offset := 1392) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_55
  have p1296_56 := copy_point (offset := 1296) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_55
  have p1200_56 := copy_point (offset := 1200) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1200_55
  have p1104_56 := copy_point (offset := 1104) pre eff56 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1104_55
  exact ⟨n49 + 12 + n51 + n52 + n53 + 12 + n55 + 12, t56, (((((((run49.trans run50).trans
    run51).trans run52).trans run53).trans run54).trans run55).trans run56), st56, rip56,
    ⟨r3_56, r5_56, r12_56, r13_56, r14_56, r15_56, trivial⟩,
    ⟨p144_56, p912_56, value56, p1104_56, p1200_56, p1296_56, p1392_56, p1488_56, p1584_56,
      p1680_56, trivial⟩⟩

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
