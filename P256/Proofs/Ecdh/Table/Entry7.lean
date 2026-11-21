import P256.Proofs.Ecdh.Table.Memory
import P256.Proofs.Ecdh.Table.Blocks

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Blocks

set_option maxRecDepth 32768 in
theorem entry7 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x100292)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 5), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 5), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3), (656, Projective.tableEntry point 4), (560, Projective.tableEntry point 5)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x1002d4 ∧ Facts s u [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 6), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 6), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3), (656, Projective.tableEntry point 4), (560, Projective.tableEntry point 5), (464, Projective.tableEntry point 6)] := by
  rcases facts.regs with ⟨r3_in, r15_in, r14_in, r12_in, r13_in, r5_in, trivial⟩
  rcases facts.points with ⟨p272_in, p1040_in, p144_in, p944_in, p1808_in, p848_in, p752_in, p656_in, p560_in, trivial⟩
  obtain ⟨n39, t39, run39, st39, eff39, mem39⟩ :=
    register_block (offset := 0x292) (bytes := b114ee2Bytes) (effect := b114ee2Effect) state (b114ee2_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b114ee2Effect, Effect.components, Component.Covers])
      (by simp [b114ee2Effect, Effect.components])
      (by simp [b114ee2Effect, Effect.components])
      (by simp [b114ee2Effect, Effect.components])
      (by simp [b114ee2Effect, Effect.components])
  have r14_39 : t39.regValue .r14 = stackPtr s - 1808 := by
    have h : t39.regValue .r14 = stackPtr t + 248 := eff39.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_39 : t39.regValue .rcx = 12 := eff39.writes.2.1
  have r7_39 : t39.regValue .rdi = stackPtr s - 1808 := by
    have h : t39.regValue .rdi = stackPtr t + 248 := eff39.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_39 : t39.regValue .rsi = stackPtr s - 272 := eff39.writes.2.2.2.trans r15_in
  have r3_39 : t39.regValue .rbx = s.regValue .rdi :=
    (eff39.agrees.read (n := 64) (r := 3) (by simp [b114ee2Effect, Effect.components])).trans r3_in
  have r15_39 : t39.regValue .r15 = stackPtr s - 272 :=
    (eff39.agrees.read (n := 64) (r := 15) (by simp [b114ee2Effect, Effect.components])).trans r15_in
  have r12_39 : t39.regValue .r12 = stackPtr s - 848 :=
    (eff39.agrees.read (n := 64) (r := 12) (by simp [b114ee2Effect, Effect.components])).trans r12_in
  have r13_39 : t39.regValue .r13 = stackPtr s - 752 :=
    (eff39.agrees.read (n := 64) (r := 13) (by simp [b114ee2Effect, Effect.components])).trans r13_in
  have r5_39 : t39.regValue .rbp = stackPtr s - 144 :=
    (eff39.agrees.read (n := 64) (r := 5) (by simp [b114ee2Effect, Effect.components])).trans r5_in
  have p272_39 := point_of_external p272_in mem39
  have p1040_39 := point_of_external p1040_in mem39
  have p144_39 := point_of_external p144_in mem39
  have p944_39 := point_of_external p944_in mem39
  have p1808_39 := point_of_external p1808_in mem39
  have p848_39 := point_of_external p848_in mem39
  have p752_39 := point_of_external p752_in mem39
  have p656_39 := point_of_external p656_in mem39
  have p560_39 := point_of_external p560_in mem39
  have scalar39 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t39 = s.regValue .rsi := by
    change memLoad t39.external _ 64 = _
    rw [mem39]
    exact facts.scalar
  obtain ⟨t40, run40, st40, rip40, value40, eff40, _⟩ :=
    copy_stack (sourceOffset := 272) pre st39 0x2a5 (by decide) (by decide +kernel)
      eff39.rip 1808 (by decide) (by decide) r7_39 r1_39
      (by decide) (by decide) (by decide) r6_39 p272_39
  have p272_40 := copy_point (offset := 272) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_39
  have p1040_40 := copy_point (offset := 1040) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_39
  have p144_40 := copy_point (offset := 144) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_39
  have p944_40 := copy_point (offset := 944) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_39
  have p1808_40 := value40
  have p848_40 := copy_point (offset := 848) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_39
  have p752_40 := copy_point (offset := 752) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_39
  have p656_40 := copy_point (offset := 656) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p656_39
  have p560_40 := copy_point (offset := 560) pre eff40 (by decide) (by decide)
    (by decide) (by decide) (by decide) p560_39
  have r3_40 : t40.regValue .rbx = s.regValue .rdi :=
    (eff40.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_39
  have r15_40 : t40.regValue .r15 = stackPtr s - 272 :=
    (eff40.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_39
  have r14_40 : t40.regValue .r14 = stackPtr s - 1808 :=
    (eff40.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_39
  have r12_40 : t40.regValue .r12 = stackPtr s - 848 :=
    (eff40.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_39
  have r13_40 : t40.regValue .r13 = stackPtr s - 752 :=
    (eff40.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_39
  have r5_40 : t40.regValue .rbp = stackPtr s - 144 :=
    (eff40.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_39
  have scalar40 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t40 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar39
    apply memLoad_congr
    intro i hi
    change ( t40.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t39.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff40 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n41, t41, run41, st41, eff41, mem41⟩ :=
    register_block (offset := 0x2a8) (bytes := b114ef8Bytes) (effect := b114ef8Effect) st40 (b114ef8_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip40
      (by simp [b114ef8Effect, Effect.components, Component.Covers])
      (by simp [b114ef8Effect, Effect.components])
      (by simp [b114ef8Effect, Effect.components])
      (by simp [b114ef8Effect, Effect.components])
      (by simp [b114ef8Effect, Effect.components])
  have r7_41 : t41.regValue .rdi = stackPtr s - 1808 := eff41.writes.1.trans r14_40
  have r6_41 : t41.regValue .rsi = stackPtr s - 144 := eff41.writes.2.trans r5_40
  have r3_41 : t41.regValue .rbx = s.regValue .rdi :=
    (eff41.agrees.read (n := 64) (r := 3) (by simp [b114ef8Effect, Effect.components])).trans r3_40
  have r15_41 : t41.regValue .r15 = stackPtr s - 272 :=
    (eff41.agrees.read (n := 64) (r := 15) (by simp [b114ef8Effect, Effect.components])).trans r15_40
  have r14_41 : t41.regValue .r14 = stackPtr s - 1808 :=
    (eff41.agrees.read (n := 64) (r := 14) (by simp [b114ef8Effect, Effect.components])).trans r14_40
  have r12_41 : t41.regValue .r12 = stackPtr s - 848 :=
    (eff41.agrees.read (n := 64) (r := 12) (by simp [b114ef8Effect, Effect.components])).trans r12_40
  have r13_41 : t41.regValue .r13 = stackPtr s - 752 :=
    (eff41.agrees.read (n := 64) (r := 13) (by simp [b114ef8Effect, Effect.components])).trans r13_40
  have r5_41 : t41.regValue .rbp = stackPtr s - 144 :=
    (eff41.agrees.read (n := 64) (r := 5) (by simp [b114ef8Effect, Effect.components])).trans r5_40
  have p272_41 := point_of_external p272_40 mem41
  have p1040_41 := point_of_external p1040_40 mem41
  have p144_41 := point_of_external p144_40 mem41
  have p944_41 := point_of_external p944_40 mem41
  have p1808_41 := point_of_external p1808_40 mem41
  have p848_41 := point_of_external p848_40 mem41
  have p752_41 := point_of_external p752_40 mem41
  have p656_41 := point_of_external p656_40 mem41
  have p560_41 := point_of_external p560_40 mem41
  have scalar41 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t41 = s.regValue .rsi := by
    change memLoad t41.external _ 64 = _
    rw [mem41]
    exact scalar40
  let site42 : P256.Proofs.Projective.Multiply.Machine.Loop.CallSite 0x1051f0 :=
    ⟨0x2ae, 0x4f3d, by decide, by decide +kernel, by decide +kernel⟩
  obtain ⟨t42, result42⟩ := add_call (outputOffset := 1808) (sourceOffset := 144) pre st41
    site42 eff41.rip (by decide) (by decide) (by decide) (by decide) (by decide)
    r7_41 r6_41 p1808_41 p144_41
  obtain ⟨n42, run42⟩ := result42.execution
  have st42 := result42.toFrameState
  have p272_42 := call_point (offset := 272) result42 (by decide) (by decide) (by decide) p272_41
  have p1040_42 := call_point (offset := 1040) result42 (by decide) (by decide) (by decide) p1040_41
  have p144_42 := call_point (offset := 144) result42 (by decide) (by decide) (by decide) p144_41
  have p944_42 := call_point (offset := 944) result42 (by decide) (by decide) (by decide) p944_41
  have p1808_42 : ProjectiveAt t42 (stackPtr s - 1808) (Projective.tableEntry point 6) := result42.value
  have p848_42 := call_point (offset := 848) result42 (by decide) (by decide) (by decide) p848_41
  have p752_42 := call_point (offset := 752) result42 (by decide) (by decide) (by decide) p752_41
  have p656_42 := call_point (offset := 656) result42 (by decide) (by decide) (by decide) p656_41
  have p560_42 := call_point (offset := 560) result42 (by decide) (by decide) (by decide) p560_41
  have r3_42 : t42.regValue .rbx = s.regValue .rdi :=
    (result42.registers .rbx (by simp)).trans r3_41
  have r15_42 : t42.regValue .r15 = stackPtr s - 272 :=
    (result42.registers .r15 (by simp)).trans r15_41
  have r14_42 : t42.regValue .r14 = stackPtr s - 1808 :=
    (result42.registers .r14 (by simp)).trans r14_41
  have r12_42 : t42.regValue .r12 = stackPtr s - 848 :=
    (result42.registers .r12 (by simp)).trans r12_41
  have r13_42 : t42.regValue .r13 = stackPtr s - 752 :=
    (result42.registers .r13 (by simp)).trans r13_41
  have r5_42 : t42.regValue .rbp = stackPtr s - 144 :=
    (result42.registers .rbp (by simp)).trans r5_41
  have scalar42 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t42 = s.regValue .rsi :=
    (result42.read (by decide) (by decide) (by decide)).trans scalar41
  obtain ⟨n43, t43, run43, st43, eff43, mem43⟩ :=
    register_block (offset := 0x2b3) (bytes := b114f03Bytes) (effect := b114f03Effect) st42 (b114f03_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result42.rip
      (by simp [b114f03Effect, Effect.components, Component.Covers])
      (by simp [b114f03Effect, Effect.components])
      (by simp [b114f03Effect, Effect.components])
      (by simp [b114f03Effect, Effect.components])
      (by simp [b114f03Effect, Effect.components])
  have r1_43 : t43.regValue .rcx = 12 := eff43.writes.1
  have r7_43 : t43.regValue .rdi = stackPtr s - 144 := eff43.writes.2.1.trans r5_42
  have r6_43 : t43.regValue .rsi = stackPtr s - 1808 := eff43.writes.2.2.trans r14_42
  have r3_43 : t43.regValue .rbx = s.regValue .rdi :=
    (eff43.agrees.read (n := 64) (r := 3) (by simp [b114f03Effect, Effect.components])).trans r3_42
  have r15_43 : t43.regValue .r15 = stackPtr s - 272 :=
    (eff43.agrees.read (n := 64) (r := 15) (by simp [b114f03Effect, Effect.components])).trans r15_42
  have r14_43 : t43.regValue .r14 = stackPtr s - 1808 :=
    (eff43.agrees.read (n := 64) (r := 14) (by simp [b114f03Effect, Effect.components])).trans r14_42
  have r12_43 : t43.regValue .r12 = stackPtr s - 848 :=
    (eff43.agrees.read (n := 64) (r := 12) (by simp [b114f03Effect, Effect.components])).trans r12_42
  have r13_43 : t43.regValue .r13 = stackPtr s - 752 :=
    (eff43.agrees.read (n := 64) (r := 13) (by simp [b114f03Effect, Effect.components])).trans r13_42
  have r5_43 : t43.regValue .rbp = stackPtr s - 144 :=
    (eff43.agrees.read (n := 64) (r := 5) (by simp [b114f03Effect, Effect.components])).trans r5_42
  have p272_43 := point_of_external p272_42 mem43
  have p1040_43 := point_of_external p1040_42 mem43
  have p144_43 := point_of_external p144_42 mem43
  have p944_43 := point_of_external p944_42 mem43
  have p1808_43 := point_of_external p1808_42 mem43
  have p848_43 := point_of_external p848_42 mem43
  have p752_43 := point_of_external p752_42 mem43
  have p656_43 := point_of_external p656_42 mem43
  have p560_43 := point_of_external p560_42 mem43
  have scalar43 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t43 = s.regValue .rsi := by
    change memLoad t43.external _ 64 = _
    rw [mem43]
    exact scalar42
  obtain ⟨t44, run44, st44, rip44, value44, eff44, _⟩ :=
    copy_stack (sourceOffset := 1808) pre st43 0x2be (by decide) (by decide +kernel)
      eff43.rip 144 (by decide) (by decide) r7_43 r1_43
      (by decide) (by decide) (by decide) r6_43 p1808_43
  have p272_44 := copy_point (offset := 272) pre eff44 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_43
  have p1040_44 := copy_point (offset := 1040) pre eff44 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_43
  have p144_44 := value44
  have p944_44 := copy_point (offset := 944) pre eff44 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_43
  have p1808_44 := copy_point (offset := 1808) pre eff44 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_43
  have p848_44 := copy_point (offset := 848) pre eff44 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_43
  have p752_44 := copy_point (offset := 752) pre eff44 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_43
  have p656_44 := copy_point (offset := 656) pre eff44 (by decide) (by decide)
    (by decide) (by decide) (by decide) p656_43
  have p560_44 := copy_point (offset := 560) pre eff44 (by decide) (by decide)
    (by decide) (by decide) (by decide) p560_43
  have r3_44 : t44.regValue .rbx = s.regValue .rdi :=
    (eff44.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_43
  have r15_44 : t44.regValue .r15 = stackPtr s - 272 :=
    (eff44.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_43
  have r14_44 : t44.regValue .r14 = stackPtr s - 1808 :=
    (eff44.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_43
  have r12_44 : t44.regValue .r12 = stackPtr s - 848 :=
    (eff44.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_43
  have r13_44 : t44.regValue .r13 = stackPtr s - 752 :=
    (eff44.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_43
  have r5_44 : t44.regValue .rbp = stackPtr s - 144 :=
    (eff44.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_43
  have scalar44 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t44 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar43
    apply memLoad_congr
    intro i hi
    change ( t44.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t43.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff44 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n45, t45, run45, st45, eff45, mem45⟩ :=
    register_block (offset := 0x2c1) (bytes := b114f11Bytes) (effect := b114f11Effect) st44 (b114f11_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip44
      (by simp [b114f11Effect, Effect.components, Component.Covers])
      (by simp [b114f11Effect, Effect.components])
      (by simp [b114f11Effect, Effect.components])
      (by simp [b114f11Effect, Effect.components])
      (by simp [b114f11Effect, Effect.components])
  have r1_45 : t45.regValue .rcx = 12 := eff45.writes.1
  have r7_45 : t45.regValue .rdi = stackPtr s - 464 := by
    have h : t45.regValue .rdi = stackPtr t44 + 1592 := eff45.writes.2.1
    exact h.trans (scalar_stack_address st44.rsp (by decide) (by decide))
  have r6_45 : t45.regValue .rsi = stackPtr s - 144 := eff45.writes.2.2.trans r5_44
  have r3_45 : t45.regValue .rbx = s.regValue .rdi :=
    (eff45.agrees.read (n := 64) (r := 3) (by simp [b114f11Effect, Effect.components])).trans r3_44
  have r15_45 : t45.regValue .r15 = stackPtr s - 272 :=
    (eff45.agrees.read (n := 64) (r := 15) (by simp [b114f11Effect, Effect.components])).trans r15_44
  have r14_45 : t45.regValue .r14 = stackPtr s - 1808 :=
    (eff45.agrees.read (n := 64) (r := 14) (by simp [b114f11Effect, Effect.components])).trans r14_44
  have r12_45 : t45.regValue .r12 = stackPtr s - 848 :=
    (eff45.agrees.read (n := 64) (r := 12) (by simp [b114f11Effect, Effect.components])).trans r12_44
  have r13_45 : t45.regValue .r13 = stackPtr s - 752 :=
    (eff45.agrees.read (n := 64) (r := 13) (by simp [b114f11Effect, Effect.components])).trans r13_44
  have r5_45 : t45.regValue .rbp = stackPtr s - 144 :=
    (eff45.agrees.read (n := 64) (r := 5) (by simp [b114f11Effect, Effect.components])).trans r5_44
  have p272_45 := point_of_external p272_44 mem45
  have p1040_45 := point_of_external p1040_44 mem45
  have p144_45 := point_of_external p144_44 mem45
  have p944_45 := point_of_external p944_44 mem45
  have p1808_45 := point_of_external p1808_44 mem45
  have p848_45 := point_of_external p848_44 mem45
  have p752_45 := point_of_external p752_44 mem45
  have p656_45 := point_of_external p656_44 mem45
  have p560_45 := point_of_external p560_44 mem45
  have scalar45 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t45 = s.regValue .rsi := by
    change memLoad t45.external _ 64 = _
    rw [mem45]
    exact scalar44
  obtain ⟨t46, run46, st46, rip46, value46, eff46, _⟩ :=
    copy_stack (sourceOffset := 144) pre st45 0x2d1 (by decide) (by decide +kernel)
      eff45.rip 464 (by decide) (by decide) r7_45 r1_45
      (by decide) (by decide) (by decide) r6_45 p144_45
  have p272_46 := copy_point (offset := 272) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_45
  have p1040_46 := copy_point (offset := 1040) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_45
  have p144_46 := copy_point (offset := 144) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_45
  have p944_46 := copy_point (offset := 944) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_45
  have p1808_46 := copy_point (offset := 1808) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_45
  have p848_46 := copy_point (offset := 848) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_45
  have p752_46 := copy_point (offset := 752) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_45
  have p656_46 := copy_point (offset := 656) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p656_45
  have p560_46 := copy_point (offset := 560) pre eff46 (by decide) (by decide)
    (by decide) (by decide) (by decide) p560_45
  have p464_46 := value46
  have r3_46 : t46.regValue .rbx = s.regValue .rdi :=
    (eff46.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_45
  have r15_46 : t46.regValue .r15 = stackPtr s - 272 :=
    (eff46.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_45
  have r14_46 : t46.regValue .r14 = stackPtr s - 1808 :=
    (eff46.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_45
  have r12_46 : t46.regValue .r12 = stackPtr s - 848 :=
    (eff46.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_45
  have r13_46 : t46.regValue .r13 = stackPtr s - 752 :=
    (eff46.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_45
  have r5_46 : t46.regValue .rbp = stackPtr s - 144 :=
    (eff46.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_45
  have scalar46 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t46 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar45
    apply memLoad_congr
    intro i hi
    change ( t46.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t45.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff46 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  exact ⟨n39 + 12 + n41 + n42 + n43 + 12 + n45 + 12, t46, (((((((run39.trans run40).trans run41).trans run42).trans run43).trans run44).trans run45).trans run46), st46, rip46,
    ⟨r3_46, r15_46, r14_46, r12_46, r13_46, r5_46, trivial⟩,
    ⟨p272_46, p1040_46, p144_46, p944_46, p1808_46, p848_46, p752_46, p656_46, p560_46, p464_46, trivial⟩, scalar46⟩

end P256.Proofs.Ecdh.Table
