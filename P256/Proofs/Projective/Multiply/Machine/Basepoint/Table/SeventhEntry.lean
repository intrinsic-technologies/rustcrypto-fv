import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.Memory
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame TableSteps Blocks

theorem seventh_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e87b)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12, stackPtr s - 912),
      (.r13, stackPtr s - 144), (.r14, stackPtr s - 912), (.r15, s.regValue .rsi)]
      [(144, Projective.tableEntry basePoint 5), (912, Projective.tableEntry basePoint 5), (1200,
        Projective.tableEntry basePoint 5), (1296, Projective.tableEntry basePoint 4), (1392,
        Projective.tableEntry basePoint 3), (1488, Projective.tableEntry basePoint 2), (1584,
        Projective.tableEntry basePoint 1), (1680, Projective.tableEntry basePoint 0)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = 0x10e8c1 ∧ Facts s u [(.rbx, s.regValue .rdi), (.rbp, stackPtr s - 912), (.r12,
        stackPtr s - 912), (.r13, stackPtr s - 144), (.r14, stackPtr s - 912), (.r15, s.regValue
        .rsi)]
        [(144, Projective.tableEntry basePoint 6), (912, Projective.tableEntry basePoint 6), (1104,
          Projective.tableEntry basePoint 6), (1200, Projective.tableEntry basePoint 5), (1296,
          Projective.tableEntry basePoint 4), (1392, Projective.tableEntry basePoint 3), (1488,
          Projective.tableEntry basePoint 2), (1584, Projective.tableEntry basePoint 1), (1680,
          Projective.tableEntry basePoint 0)] := by
  rcases facts.regs with ⟨r3_in, r5_in, r12_in, r13_in, r14_in, r15_in, trivial⟩
  rcases facts.points with ⟨p144_in, p912_in, p1200_in, p1296_in, p1392_in, p1488_in, p1584_in,
    p1680_in, trivial⟩
  obtain ⟨n41, t41, run41, st41, eff41, mem41⟩ :=
    register_block (offset := 0xe87b) state (b1165eb_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b1165ebEffect, Effect.components, Component.Covers])
      (by simp [b1165ebEffect, Effect.components])
      (by simp [b1165ebEffect, Effect.components])
      (by simp [b1165ebEffect, Effect.components])
      (by simp [b1165ebEffect, Effect.components])
  have r14_41 : t41.regValue .r14 = stackPtr s - 912 := by
    have h : t41.regValue .r14 = stackPtr t + 1032 := eff41.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_41 : t41.regValue .rcx = 12 := eff41.writes.2.1
  have r7_41 : t41.regValue .rdi = stackPtr s - 912 := by
    have h : t41.regValue .rdi = stackPtr t + 1032 := eff41.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_41 : t41.regValue .rsi = 2108104 := eff41.writes.2.2.2
  have r15_41 : t41.regValue .r15 = s.regValue .rsi :=
    (eff41.agrees.read (n := 64) (r := 15)
      (by simp [b1165ebEffect, Effect.components])).trans r15_in
  have r3_41 : t41.regValue .rbx = s.regValue .rdi :=
    (eff41.agrees.read (n := 64) (r := 3)
      (by simp [b1165ebEffect, Effect.components])).trans r3_in
  have r5_41 : t41.regValue .rbp = stackPtr s - 912 :=
    (eff41.agrees.read (n := 64) (r := 5)
      (by simp [b1165ebEffect, Effect.components])).trans r5_in
  have r12_41 : t41.regValue .r12 = stackPtr s - 912 :=
    (eff41.agrees.read (n := 64) (r := 12)
      (by simp [b1165ebEffect, Effect.components])).trans r12_in
  have r13_41 : t41.regValue .r13 = stackPtr s - 144 :=
    (eff41.agrees.read (n := 64) (r := 13)
      (by simp [b1165ebEffect, Effect.components])).trans r13_in
  have p1680_41 := point_of_external p1680_in mem41
  have p144_41 := point_of_external p144_in mem41
  have p1584_41 := point_of_external p1584_in mem41
  have p912_41 := point_of_external p912_in mem41
  have p1488_41 := point_of_external p1488_in mem41
  have p1392_41 := point_of_external p1392_in mem41
  have p1296_41 := point_of_external p1296_in mem41
  have p1200_41 := point_of_external p1200_in mem41
  obtain ⟨t42, run42, st42, rip42, value42, eff42, _⟩ :=
    copy_generator pre st41 0xe892 (by decide) (by decide +kernel)
      eff41.rip 912 (by decide) (by decide) r7_41 r1_41
      r6_41
  have r15_42 : t42.regValue .r15 = s.regValue .rsi :=
    (eff42.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_41
  have r3_42 : t42.regValue .rbx = s.regValue .rdi :=
    (eff42.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_41
  have r5_42 : t42.regValue .rbp = stackPtr s - 912 :=
    (eff42.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_41
  have r12_42 : t42.regValue .r12 = stackPtr s - 912 :=
    (eff42.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_41
  have r14_42 : t42.regValue .r14 = stackPtr s - 912 :=
    (eff42.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_41
  have r13_42 : t42.regValue .r13 = stackPtr s - 144 :=
    (eff42.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_41
  have p1680_42 := copy_point (offset := 1680) pre eff42 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_41
  have p144_42 := copy_point (offset := 144) pre eff42 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_41
  have p1584_42 := copy_point (offset := 1584) pre eff42 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_41
  have p1488_42 := copy_point (offset := 1488) pre eff42 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_41
  have p1392_42 := copy_point (offset := 1392) pre eff42 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_41
  have p1296_42 := copy_point (offset := 1296) pre eff42 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_41
  have p1200_42 := copy_point (offset := 1200) pre eff42 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1200_41
  obtain ⟨n43, t43, run43, st43, eff43, mem43⟩ :=
    register_block (offset := 0xe895) st42 (b116605_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip42
      (by simp [b116605Effect, Effect.components, Component.Covers])
      (by simp [b116605Effect, Effect.components])
      (by simp [b116605Effect, Effect.components])
      (by simp [b116605Effect, Effect.components])
      (by simp [b116605Effect, Effect.components])
  have r7_43 : t43.regValue .rdi = stackPtr s - 912 :=
    eff43.writes.1.trans r14_42
  have r6_43 : t43.regValue .rsi = stackPtr s - 144 :=
    eff43.writes.2.trans r13_42
  have r15_43 : t43.regValue .r15 = s.regValue .rsi :=
    (eff43.agrees.read (n := 64) (r := 15)
      (by simp [b116605Effect, Effect.components])).trans r15_42
  have r3_43 : t43.regValue .rbx = s.regValue .rdi :=
    (eff43.agrees.read (n := 64) (r := 3)
      (by simp [b116605Effect, Effect.components])).trans r3_42
  have r5_43 : t43.regValue .rbp = stackPtr s - 912 :=
    (eff43.agrees.read (n := 64) (r := 5)
      (by simp [b116605Effect, Effect.components])).trans r5_42
  have r12_43 : t43.regValue .r12 = stackPtr s - 912 :=
    (eff43.agrees.read (n := 64) (r := 12)
      (by simp [b116605Effect, Effect.components])).trans r12_42
  have r14_43 : t43.regValue .r14 = stackPtr s - 912 :=
    (eff43.agrees.read (n := 64) (r := 14)
      (by simp [b116605Effect, Effect.components])).trans r14_42
  have r13_43 : t43.regValue .r13 = stackPtr s - 144 :=
    (eff43.agrees.read (n := 64) (r := 13)
      (by simp [b116605Effect, Effect.components])).trans r13_42
  have p1680_43 := point_of_external p1680_42 mem43
  have p144_43 := point_of_external p144_42 mem43
  have p1584_43 := point_of_external p1584_42 mem43
  have p912_43 := point_of_external value42 mem43
  have p1488_43 := point_of_external p1488_42 mem43
  have p1392_43 := point_of_external p1392_42 mem43
  have p1296_43 := point_of_external p1296_42 mem43
  have p1200_43 := point_of_external p1200_42 mem43
  obtain ⟨t44, result44⟩ :=
    add_call pre st43 add11660b eff43.rip
      r7_43 r6_43 p912_43 p144_43
  obtain ⟨n44, run44⟩ := result44.execution
  have st44 := result44.toFrameState
  have value44 : ProjectiveAt t44 (stackPtr s - 912)
      (Projective.tableEntry basePoint 6) := result44.value
  have r15_44 : t44.regValue .r15 = s.regValue .rsi :=
    (result44.registers .r15 (by simp)).trans r15_43
  have r3_44 : t44.regValue .rbx = s.regValue .rdi :=
    (result44.registers .rbx (by simp)).trans r3_43
  have r5_44 : t44.regValue .rbp = stackPtr s - 912 :=
    (result44.registers .rbp (by simp)).trans r5_43
  have r12_44 : t44.regValue .r12 = stackPtr s - 912 :=
    (result44.registers .r12 (by simp)).trans r12_43
  have r14_44 : t44.regValue .r14 = stackPtr s - 912 :=
    (result44.registers .r14 (by simp)).trans r14_43
  have r13_44 : t44.regValue .r13 = stackPtr s - 144 :=
    (result44.registers .r13 (by simp)).trans r13_43
  have p1680_44 := call_point (offset := 1680) result44 (by decide) (by decide) (by decide) p1680_43
  have p144_44 := call_point (offset := 144) result44 (by decide) (by decide) (by decide) p144_43
  have p1584_44 := call_point (offset := 1584) result44 (by decide) (by decide) (by decide) p1584_43
  have p1488_44 := call_point (offset := 1488) result44 (by decide) (by decide) (by decide) p1488_43
  have p1392_44 := call_point (offset := 1392) result44 (by decide) (by decide) (by decide) p1392_43
  have p1296_44 := call_point (offset := 1296) result44 (by decide) (by decide) (by decide) p1296_43
  have p1200_44 := call_point (offset := 1200) result44 (by decide) (by decide) (by decide) p1200_43
  obtain ⟨n45, t45, run45, st45, eff45, mem45⟩ :=
    register_block (offset := 0xe8a0) st44 (b116610_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result44.rip
      (by simp [b116610Effect, Effect.components, Component.Covers])
      (by simp [b116610Effect, Effect.components])
      (by simp [b116610Effect, Effect.components])
      (by simp [b116610Effect, Effect.components])
      (by simp [b116610Effect, Effect.components])
  have r1_45 : t45.regValue .rcx = 12 := eff45.writes.1
  have r7_45 : t45.regValue .rdi = stackPtr s - 144 :=
    eff45.writes.2.1.trans r13_44
  have r6_45 : t45.regValue .rsi = stackPtr s - 912 :=
    eff45.writes.2.2.trans r14_44
  have r15_45 : t45.regValue .r15 = s.regValue .rsi :=
    (eff45.agrees.read (n := 64) (r := 15)
      (by simp [b116610Effect, Effect.components])).trans r15_44
  have r3_45 : t45.regValue .rbx = s.regValue .rdi :=
    (eff45.agrees.read (n := 64) (r := 3)
      (by simp [b116610Effect, Effect.components])).trans r3_44
  have r5_45 : t45.regValue .rbp = stackPtr s - 912 :=
    (eff45.agrees.read (n := 64) (r := 5)
      (by simp [b116610Effect, Effect.components])).trans r5_44
  have r12_45 : t45.regValue .r12 = stackPtr s - 912 :=
    (eff45.agrees.read (n := 64) (r := 12)
      (by simp [b116610Effect, Effect.components])).trans r12_44
  have r14_45 : t45.regValue .r14 = stackPtr s - 912 :=
    (eff45.agrees.read (n := 64) (r := 14)
      (by simp [b116610Effect, Effect.components])).trans r14_44
  have r13_45 : t45.regValue .r13 = stackPtr s - 144 :=
    (eff45.agrees.read (n := 64) (r := 13)
      (by simp [b116610Effect, Effect.components])).trans r13_44
  have p1680_45 := point_of_external p1680_44 mem45
  have p144_45 := point_of_external p144_44 mem45
  have p1584_45 := point_of_external p1584_44 mem45
  have p912_45 := point_of_external value44 mem45
  have p1488_45 := point_of_external p1488_44 mem45
  have p1392_45 := point_of_external p1392_44 mem45
  have p1296_45 := point_of_external p1296_44 mem45
  have p1200_45 := point_of_external p1200_44 mem45
  obtain ⟨t46, run46, st46, rip46, value46, eff46, _⟩ :=
    copy_stack (sourceOffset := 912) pre st45 0xe8ab (by decide) (by decide +kernel)
      eff45.rip 144 (by decide) (by decide) r7_45 r1_45
      (by decide) (by decide) (by decide) r6_45 p912_45
  have r15_46 : t46.regValue .r15 = s.regValue .rsi :=
    (eff46.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_45
  have r3_46 : t46.regValue .rbx = s.regValue .rdi :=
    (eff46.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_45
  have r5_46 : t46.regValue .rbp = stackPtr s - 912 :=
    (eff46.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_45
  have r12_46 : t46.regValue .r12 = stackPtr s - 912 :=
    (eff46.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_45
  have r14_46 : t46.regValue .r14 = stackPtr s - 912 :=
    (eff46.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_45
  have r13_46 : t46.regValue .r13 = stackPtr s - 144 :=
    (eff46.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_45
  have p1680_46 := copy_point (offset := 1680) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_45
  have p1584_46 := copy_point (offset := 1584) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_45
  have p912_46 := copy_point (offset := 912) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_45
  have p1488_46 := copy_point (offset := 1488) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_45
  have p1392_46 := copy_point (offset := 1392) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_45
  have p1296_46 := copy_point (offset := 1296) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_45
  have p1200_46 := copy_point (offset := 1200) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1200_45
  obtain ⟨n47, t47, run47, st47, eff47, mem47⟩ :=
    register_block (offset := 0xe8ae) st46 (b11661e_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip46
      (by simp [b11661eEffect, Effect.components, Component.Covers])
      (by simp [b11661eEffect, Effect.components])
      (by simp [b11661eEffect, Effect.components])
      (by simp [b11661eEffect, Effect.components])
      (by simp [b11661eEffect, Effect.components])
  have r1_47 : t47.regValue .rcx = 12 := eff47.writes.1
  have r7_47 : t47.regValue .rdi = stackPtr s - 1104 := by
    have h : t47.regValue .rdi = stackPtr t46 + 840 := eff47.writes.2.1
    exact h.trans (scalar_stack_address st46.rsp (by decide) (by decide))
  have r6_47 : t47.regValue .rsi = stackPtr s - 144 :=
    eff47.writes.2.2.trans r13_46
  have r15_47 : t47.regValue .r15 = s.regValue .rsi :=
    (eff47.agrees.read (n := 64) (r := 15)
      (by simp [b11661eEffect, Effect.components])).trans r15_46
  have r3_47 : t47.regValue .rbx = s.regValue .rdi :=
    (eff47.agrees.read (n := 64) (r := 3)
      (by simp [b11661eEffect, Effect.components])).trans r3_46
  have r5_47 : t47.regValue .rbp = stackPtr s - 912 :=
    (eff47.agrees.read (n := 64) (r := 5)
      (by simp [b11661eEffect, Effect.components])).trans r5_46
  have r12_47 : t47.regValue .r12 = stackPtr s - 912 :=
    (eff47.agrees.read (n := 64) (r := 12)
      (by simp [b11661eEffect, Effect.components])).trans r12_46
  have r14_47 : t47.regValue .r14 = stackPtr s - 912 :=
    (eff47.agrees.read (n := 64) (r := 14)
      (by simp [b11661eEffect, Effect.components])).trans r14_46
  have r13_47 : t47.regValue .r13 = stackPtr s - 144 :=
    (eff47.agrees.read (n := 64) (r := 13)
      (by simp [b11661eEffect, Effect.components])).trans r13_46
  have p1680_47 := point_of_external p1680_46 mem47
  have p144_47 := point_of_external value46 mem47
  have p1584_47 := point_of_external p1584_46 mem47
  have p912_47 := point_of_external p912_46 mem47
  have p1488_47 := point_of_external p1488_46 mem47
  have p1392_47 := point_of_external p1392_46 mem47
  have p1296_47 := point_of_external p1296_46 mem47
  have p1200_47 := point_of_external p1200_46 mem47
  obtain ⟨t48, run48, st48, rip48, value48, eff48, _⟩ :=
    copy_stack (sourceOffset := 144) pre st47 0xe8be (by decide) (by decide +kernel)
      eff47.rip 1104 (by decide) (by decide) r7_47 r1_47
      (by decide) (by decide) (by decide) r6_47 p144_47
  have r15_48 : t48.regValue .r15 = s.regValue .rsi :=
    (eff48.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_47
  have r3_48 : t48.regValue .rbx = s.regValue .rdi :=
    (eff48.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_47
  have r5_48 : t48.regValue .rbp = stackPtr s - 912 :=
    (eff48.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_47
  have r12_48 : t48.regValue .r12 = stackPtr s - 912 :=
    (eff48.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_47
  have r14_48 : t48.regValue .r14 = stackPtr s - 912 :=
    (eff48.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_47
  have r13_48 : t48.regValue .r13 = stackPtr s - 144 :=
    (eff48.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_47
  have p1680_48 := copy_point (offset := 1680) pre eff48 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1680_47
  have p144_48 := copy_point (offset := 144) pre eff48 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_47
  have p1584_48 := copy_point (offset := 1584) pre eff48 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1584_47
  have p912_48 := copy_point (offset := 912) pre eff48 (by decide) (by decide)
    (by decide) (by decide) (by decide) p912_47
  have p1488_48 := copy_point (offset := 1488) pre eff48 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1488_47
  have p1392_48 := copy_point (offset := 1392) pre eff48 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1392_47
  have p1296_48 := copy_point (offset := 1296) pre eff48 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1296_47
  have p1200_48 := copy_point (offset := 1200) pre eff48 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1200_47
  exact ⟨n41 + 12 + n43 + n44 + n45 + 12 + n47 + 12, t48, (((((((run41.trans run42).trans
    run43).trans run44).trans run45).trans run46).trans run47).trans run48), st48, rip48,
    ⟨r3_48, r5_48, r12_48, r13_48, r14_48, r15_48, trivial⟩,
    ⟨p144_48, p912_48, value48, p1200_48, p1296_48, p1392_48, p1488_48, p1584_48, p1680_48,
      trivial⟩⟩

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
