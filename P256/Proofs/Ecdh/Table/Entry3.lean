import P256.Proofs.Ecdh.Table.Memory
import P256.Proofs.Ecdh.Table.Blocks

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Blocks

set_option maxRecDepth 32768 in
theorem entry3 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x100194)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 944), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 1), (944, Projective.tableEntry point 1)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x1001d1 ∧ Facts s u [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 2), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 2), (848, Projective.tableEntry point 2)] := by
  rcases facts.regs with ⟨r3_in, r15_in, r14_in, r12_in, r13_in, r5_in, trivial⟩
  rcases facts.points with ⟨p272_in, p1040_in, p144_in, p944_in, trivial⟩
  obtain ⟨n7, t7, run7, st7, eff7, mem7⟩ :=
    register_block (offset := 0x194) (bytes := b114de4Bytes) (effect := b114de4Effect) state (b114de4_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b114de4Effect, Effect.components, Component.Covers])
      (by simp [b114de4Effect, Effect.components])
      (by simp [b114de4Effect, Effect.components])
      (by simp [b114de4Effect, Effect.components])
      (by simp [b114de4Effect, Effect.components])
  have r14_7 : t7.regValue .r14 = stackPtr s - 1808 := by
    have h : t7.regValue .r14 = stackPtr t + 248 := eff7.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_7 : t7.regValue .rcx = 12 := eff7.writes.2.1
  have r7_7 : t7.regValue .rdi = stackPtr s - 1808 := by
    have h : t7.regValue .rdi = stackPtr t + 248 := eff7.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_7 : t7.regValue .rsi = stackPtr s - 272 := eff7.writes.2.2.2.trans r15_in
  have r3_7 : t7.regValue .rbx = s.regValue .rdi :=
    (eff7.agrees.read (n := 64) (r := 3) (by simp [b114de4Effect, Effect.components])).trans r3_in
  have r15_7 : t7.regValue .r15 = stackPtr s - 272 :=
    (eff7.agrees.read (n := 64) (r := 15) (by simp [b114de4Effect, Effect.components])).trans r15_in
  have r12_7 : t7.regValue .r12 = stackPtr s - 848 :=
    (eff7.agrees.read (n := 64) (r := 12) (by simp [b114de4Effect, Effect.components])).trans r12_in
  have r13_7 : t7.regValue .r13 = stackPtr s - 752 :=
    (eff7.agrees.read (n := 64) (r := 13) (by simp [b114de4Effect, Effect.components])).trans r13_in
  have r5_7 : t7.regValue .rbp = stackPtr s - 144 :=
    (eff7.agrees.read (n := 64) (r := 5) (by simp [b114de4Effect, Effect.components])).trans r5_in
  have p272_7 := point_of_external p272_in mem7
  have p1040_7 := point_of_external p1040_in mem7
  have p144_7 := point_of_external p144_in mem7
  have p944_7 := point_of_external p944_in mem7
  have scalar7 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t7 = s.regValue .rsi := by
    change memLoad t7.external _ 64 = _
    rw [mem7]
    exact facts.scalar
  obtain ⟨t8, run8, st8, rip8, value8, eff8, _⟩ :=
    copy_stack (sourceOffset := 272) pre st7 0x1a7 (by decide) (by decide +kernel)
      eff7.rip 1808 (by decide) (by decide) r7_7 r1_7
      (by decide) (by decide) (by decide) r6_7 p272_7
  have p272_8 := copy_point (offset := 272) pre eff8 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_7
  have p1040_8 := copy_point (offset := 1040) pre eff8 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_7
  have p144_8 := copy_point (offset := 144) pre eff8 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_7
  have p944_8 := copy_point (offset := 944) pre eff8 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_7
  have p1808_8 := value8
  have r3_8 : t8.regValue .rbx = s.regValue .rdi :=
    (eff8.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_7
  have r15_8 : t8.regValue .r15 = stackPtr s - 272 :=
    (eff8.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_7
  have r14_8 : t8.regValue .r14 = stackPtr s - 1808 :=
    (eff8.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_7
  have r12_8 : t8.regValue .r12 = stackPtr s - 848 :=
    (eff8.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_7
  have r13_8 : t8.regValue .r13 = stackPtr s - 752 :=
    (eff8.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_7
  have r5_8 : t8.regValue .rbp = stackPtr s - 144 :=
    (eff8.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_7
  have scalar8 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t8 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar7
    apply memLoad_congr
    intro i hi
    change ( t8.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t7.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff8 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n9, t9, run9, st9, eff9, mem9⟩ :=
    register_block (offset := 0x1aa) (bytes := b114dfaBytes) (effect := b114dfaEffect) st8 (b114dfa_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip8
      (by simp [b114dfaEffect, Effect.components, Component.Covers])
      (by simp [b114dfaEffect, Effect.components])
      (by simp [b114dfaEffect, Effect.components])
      (by simp [b114dfaEffect, Effect.components])
      (by simp [b114dfaEffect, Effect.components])
  have r7_9 : t9.regValue .rdi = stackPtr s - 1808 := eff9.writes.1.trans r14_8
  have r6_9 : t9.regValue .rsi = stackPtr s - 144 := eff9.writes.2.trans r5_8
  have r3_9 : t9.regValue .rbx = s.regValue .rdi :=
    (eff9.agrees.read (n := 64) (r := 3) (by simp [b114dfaEffect, Effect.components])).trans r3_8
  have r15_9 : t9.regValue .r15 = stackPtr s - 272 :=
    (eff9.agrees.read (n := 64) (r := 15) (by simp [b114dfaEffect, Effect.components])).trans r15_8
  have r14_9 : t9.regValue .r14 = stackPtr s - 1808 :=
    (eff9.agrees.read (n := 64) (r := 14) (by simp [b114dfaEffect, Effect.components])).trans r14_8
  have r12_9 : t9.regValue .r12 = stackPtr s - 848 :=
    (eff9.agrees.read (n := 64) (r := 12) (by simp [b114dfaEffect, Effect.components])).trans r12_8
  have r13_9 : t9.regValue .r13 = stackPtr s - 752 :=
    (eff9.agrees.read (n := 64) (r := 13) (by simp [b114dfaEffect, Effect.components])).trans r13_8
  have r5_9 : t9.regValue .rbp = stackPtr s - 144 :=
    (eff9.agrees.read (n := 64) (r := 5) (by simp [b114dfaEffect, Effect.components])).trans r5_8
  have p272_9 := point_of_external p272_8 mem9
  have p1040_9 := point_of_external p1040_8 mem9
  have p144_9 := point_of_external p144_8 mem9
  have p944_9 := point_of_external p944_8 mem9
  have p1808_9 := point_of_external p1808_8 mem9
  have scalar9 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t9 = s.regValue .rsi := by
    change memLoad t9.external _ 64 = _
    rw [mem9]
    exact scalar8
  let site10 : P256.Proofs.Projective.Multiply.Machine.Loop.CallSite 0x1051f0 :=
    ⟨0x1b0, 0x503b, by decide, by decide +kernel, by decide +kernel⟩
  obtain ⟨t10, result10⟩ := add_call (outputOffset := 1808) (sourceOffset := 144) pre st9
    site10 eff9.rip (by decide) (by decide) (by decide) (by decide) (by decide)
    r7_9 r6_9 p1808_9 p144_9
  obtain ⟨n10, run10⟩ := result10.execution
  have st10 := result10.toFrameState
  have p272_10 := call_point (offset := 272) result10 (by decide) (by decide) (by decide) p272_9
  have p1040_10 := call_point (offset := 1040) result10 (by decide) (by decide) (by decide) p1040_9
  have p144_10 := call_point (offset := 144) result10 (by decide) (by decide) (by decide) p144_9
  have p944_10 := call_point (offset := 944) result10 (by decide) (by decide) (by decide) p944_9
  have p1808_10 : ProjectiveAt t10 (stackPtr s - 1808) (Projective.tableEntry point 2) := result10.value
  have r3_10 : t10.regValue .rbx = s.regValue .rdi :=
    (result10.registers .rbx (by simp)).trans r3_9
  have r15_10 : t10.regValue .r15 = stackPtr s - 272 :=
    (result10.registers .r15 (by simp)).trans r15_9
  have r14_10 : t10.regValue .r14 = stackPtr s - 1808 :=
    (result10.registers .r14 (by simp)).trans r14_9
  have r12_10 : t10.regValue .r12 = stackPtr s - 848 :=
    (result10.registers .r12 (by simp)).trans r12_9
  have r13_10 : t10.regValue .r13 = stackPtr s - 752 :=
    (result10.registers .r13 (by simp)).trans r13_9
  have r5_10 : t10.regValue .rbp = stackPtr s - 144 :=
    (result10.registers .rbp (by simp)).trans r5_9
  have scalar10 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t10 = s.regValue .rsi :=
    (result10.read (by decide) (by decide) (by decide)).trans scalar9
  obtain ⟨n11, t11, run11, st11, eff11, mem11⟩ :=
    register_block (offset := 0x1b5) (bytes := b114e05Bytes) (effect := b114e05Effect) st10 (b114e05_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result10.rip
      (by simp [b114e05Effect, Effect.components, Component.Covers])
      (by simp [b114e05Effect, Effect.components])
      (by simp [b114e05Effect, Effect.components])
      (by simp [b114e05Effect, Effect.components])
      (by simp [b114e05Effect, Effect.components])
  have r1_11 : t11.regValue .rcx = 12 := eff11.writes.1
  have r7_11 : t11.regValue .rdi = stackPtr s - 144 := eff11.writes.2.1.trans r5_10
  have r6_11 : t11.regValue .rsi = stackPtr s - 1808 := eff11.writes.2.2.trans r14_10
  have r3_11 : t11.regValue .rbx = s.regValue .rdi :=
    (eff11.agrees.read (n := 64) (r := 3) (by simp [b114e05Effect, Effect.components])).trans r3_10
  have r15_11 : t11.regValue .r15 = stackPtr s - 272 :=
    (eff11.agrees.read (n := 64) (r := 15) (by simp [b114e05Effect, Effect.components])).trans r15_10
  have r14_11 : t11.regValue .r14 = stackPtr s - 1808 :=
    (eff11.agrees.read (n := 64) (r := 14) (by simp [b114e05Effect, Effect.components])).trans r14_10
  have r12_11 : t11.regValue .r12 = stackPtr s - 848 :=
    (eff11.agrees.read (n := 64) (r := 12) (by simp [b114e05Effect, Effect.components])).trans r12_10
  have r13_11 : t11.regValue .r13 = stackPtr s - 752 :=
    (eff11.agrees.read (n := 64) (r := 13) (by simp [b114e05Effect, Effect.components])).trans r13_10
  have r5_11 : t11.regValue .rbp = stackPtr s - 144 :=
    (eff11.agrees.read (n := 64) (r := 5) (by simp [b114e05Effect, Effect.components])).trans r5_10
  have p272_11 := point_of_external p272_10 mem11
  have p1040_11 := point_of_external p1040_10 mem11
  have p144_11 := point_of_external p144_10 mem11
  have p944_11 := point_of_external p944_10 mem11
  have p1808_11 := point_of_external p1808_10 mem11
  have scalar11 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t11 = s.regValue .rsi := by
    change memLoad t11.external _ 64 = _
    rw [mem11]
    exact scalar10
  obtain ⟨t12, run12, st12, rip12, value12, eff12, _⟩ :=
    copy_stack (sourceOffset := 1808) pre st11 0x1c0 (by decide) (by decide +kernel)
      eff11.rip 144 (by decide) (by decide) r7_11 r1_11
      (by decide) (by decide) (by decide) r6_11 p1808_11
  have p272_12 := copy_point (offset := 272) pre eff12 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_11
  have p1040_12 := copy_point (offset := 1040) pre eff12 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_11
  have p144_12 := value12
  have p944_12 := copy_point (offset := 944) pre eff12 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_11
  have p1808_12 := copy_point (offset := 1808) pre eff12 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_11
  have r3_12 : t12.regValue .rbx = s.regValue .rdi :=
    (eff12.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_11
  have r15_12 : t12.regValue .r15 = stackPtr s - 272 :=
    (eff12.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_11
  have r14_12 : t12.regValue .r14 = stackPtr s - 1808 :=
    (eff12.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_11
  have r12_12 : t12.regValue .r12 = stackPtr s - 848 :=
    (eff12.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_11
  have r13_12 : t12.regValue .r13 = stackPtr s - 752 :=
    (eff12.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_11
  have r5_12 : t12.regValue .rbp = stackPtr s - 144 :=
    (eff12.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_11
  have scalar12 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t12 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar11
    apply memLoad_congr
    intro i hi
    change ( t12.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t11.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff12 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n13, t13, run13, st13, eff13, mem13⟩ :=
    register_block (offset := 0x1c3) (bytes := b114e13Bytes) (effect := b114e13Effect) st12 (b114e13_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip12
      (by simp [b114e13Effect, Effect.components, Component.Covers])
      (by simp [b114e13Effect, Effect.components])
      (by simp [b114e13Effect, Effect.components])
      (by simp [b114e13Effect, Effect.components])
      (by simp [b114e13Effect, Effect.components])
  have r1_13 : t13.regValue .rcx = 12 := eff13.writes.1
  have r7_13 : t13.regValue .rdi = stackPtr s - 848 := eff13.writes.2.1.trans r12_12
  have r6_13 : t13.regValue .rsi = stackPtr s - 144 := eff13.writes.2.2.trans r5_12
  have r3_13 : t13.regValue .rbx = s.regValue .rdi :=
    (eff13.agrees.read (n := 64) (r := 3) (by simp [b114e13Effect, Effect.components])).trans r3_12
  have r15_13 : t13.regValue .r15 = stackPtr s - 272 :=
    (eff13.agrees.read (n := 64) (r := 15) (by simp [b114e13Effect, Effect.components])).trans r15_12
  have r14_13 : t13.regValue .r14 = stackPtr s - 1808 :=
    (eff13.agrees.read (n := 64) (r := 14) (by simp [b114e13Effect, Effect.components])).trans r14_12
  have r12_13 : t13.regValue .r12 = stackPtr s - 848 :=
    (eff13.agrees.read (n := 64) (r := 12) (by simp [b114e13Effect, Effect.components])).trans r12_12
  have r13_13 : t13.regValue .r13 = stackPtr s - 752 :=
    (eff13.agrees.read (n := 64) (r := 13) (by simp [b114e13Effect, Effect.components])).trans r13_12
  have r5_13 : t13.regValue .rbp = stackPtr s - 144 :=
    (eff13.agrees.read (n := 64) (r := 5) (by simp [b114e13Effect, Effect.components])).trans r5_12
  have p272_13 := point_of_external p272_12 mem13
  have p1040_13 := point_of_external p1040_12 mem13
  have p144_13 := point_of_external p144_12 mem13
  have p944_13 := point_of_external p944_12 mem13
  have p1808_13 := point_of_external p1808_12 mem13
  have scalar13 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t13 = s.regValue .rsi := by
    change memLoad t13.external _ 64 = _
    rw [mem13]
    exact scalar12
  obtain ⟨t14, run14, st14, rip14, value14, eff14, _⟩ :=
    copy_stack (sourceOffset := 144) pre st13 0x1ce (by decide) (by decide +kernel)
      eff13.rip 848 (by decide) (by decide) r7_13 r1_13
      (by decide) (by decide) (by decide) r6_13 p144_13
  have p272_14 := copy_point (offset := 272) pre eff14 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_13
  have p1040_14 := copy_point (offset := 1040) pre eff14 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_13
  have p144_14 := copy_point (offset := 144) pre eff14 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_13
  have p944_14 := copy_point (offset := 944) pre eff14 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_13
  have p1808_14 := copy_point (offset := 1808) pre eff14 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_13
  have p848_14 := value14
  have r3_14 : t14.regValue .rbx = s.regValue .rdi :=
    (eff14.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_13
  have r15_14 : t14.regValue .r15 = stackPtr s - 272 :=
    (eff14.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_13
  have r14_14 : t14.regValue .r14 = stackPtr s - 1808 :=
    (eff14.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_13
  have r12_14 : t14.regValue .r12 = stackPtr s - 848 :=
    (eff14.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_13
  have r13_14 : t14.regValue .r13 = stackPtr s - 752 :=
    (eff14.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_13
  have r5_14 : t14.regValue .rbp = stackPtr s - 144 :=
    (eff14.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_13
  have scalar14 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t14 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar13
    apply memLoad_congr
    intro i hi
    change ( t14.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t13.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff14 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  exact ⟨n7 + 12 + n9 + n10 + n11 + 12 + n13 + 12, t14, (((((((run7.trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14), st14, rip14,
    ⟨r3_14, r15_14, r14_14, r12_14, r13_14, r5_14, trivial⟩,
    ⟨p272_14, p1040_14, p144_14, p944_14, p1808_14, p848_14, trivial⟩, scalar14⟩

end P256.Proofs.Ecdh.Table
