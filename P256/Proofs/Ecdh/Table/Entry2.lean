import P256.Proofs.Ecdh.Table.Memory
import P256.Proofs.Ecdh.Table.Blocks

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Blocks

set_option maxRecDepth 32768 in
theorem entry2 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x10014d)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x100194 ∧ Facts s u [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 944), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 1), (944, Projective.tableEntry point 1)] := by
  rcases facts.regs with ⟨r3_in, r15_in, trivial⟩
  rcases facts.points with ⟨p272_in, p1040_in, trivial⟩
  obtain ⟨n1, t1, run1, st1, eff1, mem1⟩ :=
    register_block (offset := 0x14d) (bytes := b114d9dBytes) (effect := b114d9dEffect) state (b114d9d_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b114d9dEffect, Effect.components, Component.Covers])
      (by simp [b114d9dEffect, Effect.components])
      (by simp [b114d9dEffect, Effect.components])
      (by simp [b114d9dEffect, Effect.components])
      (by simp [b114d9dEffect, Effect.components])
  have r14_1 : t1.regValue .r14 = stackPtr s - 944 := by
    have h : t1.regValue .r14 = stackPtr t + 1112 := eff1.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r12_1 : t1.regValue .r12 = stackPtr s - 848 := by
    have h : t1.regValue .r12 = stackPtr t + 1208 := eff1.writes.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r13_1 : t1.regValue .r13 = stackPtr s - 752 := by
    have h : t1.regValue .r13 = stackPtr t + 1304 := eff1.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r5_1 : t1.regValue .rbp = stackPtr s - 144 := by
    have h : t1.regValue .rbp = stackPtr t + 1912 := eff1.writes.2.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_1 : t1.regValue .rcx = 12 := eff1.writes.2.2.2.2.1
  have r7_1 : t1.regValue .rdi = stackPtr s - 144 := by
    have h : t1.regValue .rdi = stackPtr t + 1912 := eff1.writes.2.2.2.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_1 : t1.regValue .rsi = stackPtr s - 272 := eff1.writes.2.2.2.2.2.2.trans r15_in
  have r3_1 : t1.regValue .rbx = s.regValue .rdi :=
    (eff1.agrees.read (n := 64) (r := 3) (by simp [b114d9dEffect, Effect.components])).trans r3_in
  have r15_1 : t1.regValue .r15 = stackPtr s - 272 :=
    (eff1.agrees.read (n := 64) (r := 15) (by simp [b114d9dEffect, Effect.components])).trans r15_in
  have p272_1 := point_of_external p272_in mem1
  have p1040_1 := point_of_external p1040_in mem1
  have scalar1 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t1 = s.regValue .rsi := by
    change memLoad t1.external _ 64 = _
    rw [mem1]
    exact facts.scalar
  obtain ⟨t2, run2, st2, rip2, value2, eff2, _⟩ :=
    copy_stack (sourceOffset := 272) pre st1 0x178 (by decide) (by decide +kernel)
      eff1.rip 144 (by decide) (by decide) r7_1 r1_1
      (by decide) (by decide) (by decide) r6_1 p272_1
  have p272_2 := copy_point (offset := 272) pre eff2 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_1
  have p1040_2 := copy_point (offset := 1040) pre eff2 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_1
  have p144_2 := value2
  have r3_2 : t2.regValue .rbx = s.regValue .rdi :=
    (eff2.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_1
  have r15_2 : t2.regValue .r15 = stackPtr s - 272 :=
    (eff2.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_1
  have r14_2 : t2.regValue .r14 = stackPtr s - 944 :=
    (eff2.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_1
  have r12_2 : t2.regValue .r12 = stackPtr s - 848 :=
    (eff2.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_1
  have r13_2 : t2.regValue .r13 = stackPtr s - 752 :=
    (eff2.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_1
  have r5_2 : t2.regValue .rbp = stackPtr s - 144 :=
    (eff2.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_1
  have scalar2 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t2 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar1
    apply memLoad_congr
    intro i hi
    change ( t2.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t1.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff2 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n3, t3, run3, st3, eff3, mem3⟩ :=
    register_block (offset := 0x17b) (bytes := b114dcbBytes) (effect := b114dcbEffect) st2 (b114dcb_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip2
      (by simp [b114dcbEffect, Effect.components, Component.Covers])
      (by simp [b114dcbEffect, Effect.components])
      (by simp [b114dcbEffect, Effect.components])
      (by simp [b114dcbEffect, Effect.components])
      (by simp [b114dcbEffect, Effect.components])
  have r7_3 : t3.regValue .rdi = stackPtr s - 144 := eff3.writes.1.trans r5_2
  have r6_3 : t3.regValue .rsi = stackPtr s - 272 := eff3.writes.2.trans r15_2
  have r3_3 : t3.regValue .rbx = s.regValue .rdi :=
    (eff3.agrees.read (n := 64) (r := 3) (by simp [b114dcbEffect, Effect.components])).trans r3_2
  have r15_3 : t3.regValue .r15 = stackPtr s - 272 :=
    (eff3.agrees.read (n := 64) (r := 15) (by simp [b114dcbEffect, Effect.components])).trans r15_2
  have r14_3 : t3.regValue .r14 = stackPtr s - 944 :=
    (eff3.agrees.read (n := 64) (r := 14) (by simp [b114dcbEffect, Effect.components])).trans r14_2
  have r12_3 : t3.regValue .r12 = stackPtr s - 848 :=
    (eff3.agrees.read (n := 64) (r := 12) (by simp [b114dcbEffect, Effect.components])).trans r12_2
  have r13_3 : t3.regValue .r13 = stackPtr s - 752 :=
    (eff3.agrees.read (n := 64) (r := 13) (by simp [b114dcbEffect, Effect.components])).trans r13_2
  have r5_3 : t3.regValue .rbp = stackPtr s - 144 :=
    (eff3.agrees.read (n := 64) (r := 5) (by simp [b114dcbEffect, Effect.components])).trans r5_2
  have p272_3 := point_of_external p272_2 mem3
  have p1040_3 := point_of_external p1040_2 mem3
  have p144_3 := point_of_external p144_2 mem3
  have scalar3 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t3 = s.regValue .rsi := by
    change memLoad t3.external _ 64 = _
    rw [mem3]
    exact scalar2
  let site4 : P256.Proofs.Projective.Multiply.Machine.Loop.CallSite 0x1051f0 :=
    ⟨0x181, 0x506a, by decide, by decide +kernel, by decide +kernel⟩
  obtain ⟨t4, result4⟩ := add_call (outputOffset := 144) (sourceOffset := 272) pre st3
    site4 eff3.rip (by decide) (by decide) (by decide) (by decide) (by decide)
    r7_3 r6_3 p144_3 p272_3
  obtain ⟨n4, run4⟩ := result4.execution
  have st4 := result4.toFrameState
  have p272_4 := call_point (offset := 272) result4 (by decide) (by decide) (by decide) p272_3
  have p1040_4 := call_point (offset := 1040) result4 (by decide) (by decide) (by decide) p1040_3
  have p144_4 : ProjectiveAt t4 (stackPtr s - 144) (Projective.tableEntry point 1) := result4.value
  have r3_4 : t4.regValue .rbx = s.regValue .rdi :=
    (result4.registers .rbx (by simp)).trans r3_3
  have r15_4 : t4.regValue .r15 = stackPtr s - 272 :=
    (result4.registers .r15 (by simp)).trans r15_3
  have r14_4 : t4.regValue .r14 = stackPtr s - 944 :=
    (result4.registers .r14 (by simp)).trans r14_3
  have r12_4 : t4.regValue .r12 = stackPtr s - 848 :=
    (result4.registers .r12 (by simp)).trans r12_3
  have r13_4 : t4.regValue .r13 = stackPtr s - 752 :=
    (result4.registers .r13 (by simp)).trans r13_3
  have r5_4 : t4.regValue .rbp = stackPtr s - 144 :=
    (result4.registers .rbp (by simp)).trans r5_3
  have scalar4 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t4 = s.regValue .rsi :=
    (result4.read (by decide) (by decide) (by decide)).trans scalar3
  obtain ⟨n5, t5, run5, st5, eff5, mem5⟩ :=
    register_block (offset := 0x186) (bytes := b114dd6Bytes) (effect := b114dd6Effect) st4 (b114dd6_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result4.rip
      (by simp [b114dd6Effect, Effect.components, Component.Covers])
      (by simp [b114dd6Effect, Effect.components])
      (by simp [b114dd6Effect, Effect.components])
      (by simp [b114dd6Effect, Effect.components])
      (by simp [b114dd6Effect, Effect.components])
  have r1_5 : t5.regValue .rcx = 12 := eff5.writes.1
  have r7_5 : t5.regValue .rdi = stackPtr s - 944 := eff5.writes.2.1.trans r14_4
  have r6_5 : t5.regValue .rsi = stackPtr s - 144 := eff5.writes.2.2.trans r5_4
  have r3_5 : t5.regValue .rbx = s.regValue .rdi :=
    (eff5.agrees.read (n := 64) (r := 3) (by simp [b114dd6Effect, Effect.components])).trans r3_4
  have r15_5 : t5.regValue .r15 = stackPtr s - 272 :=
    (eff5.agrees.read (n := 64) (r := 15) (by simp [b114dd6Effect, Effect.components])).trans r15_4
  have r14_5 : t5.regValue .r14 = stackPtr s - 944 :=
    (eff5.agrees.read (n := 64) (r := 14) (by simp [b114dd6Effect, Effect.components])).trans r14_4
  have r12_5 : t5.regValue .r12 = stackPtr s - 848 :=
    (eff5.agrees.read (n := 64) (r := 12) (by simp [b114dd6Effect, Effect.components])).trans r12_4
  have r13_5 : t5.regValue .r13 = stackPtr s - 752 :=
    (eff5.agrees.read (n := 64) (r := 13) (by simp [b114dd6Effect, Effect.components])).trans r13_4
  have r5_5 : t5.regValue .rbp = stackPtr s - 144 :=
    (eff5.agrees.read (n := 64) (r := 5) (by simp [b114dd6Effect, Effect.components])).trans r5_4
  have p272_5 := point_of_external p272_4 mem5
  have p1040_5 := point_of_external p1040_4 mem5
  have p144_5 := point_of_external p144_4 mem5
  have scalar5 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t5 = s.regValue .rsi := by
    change memLoad t5.external _ 64 = _
    rw [mem5]
    exact scalar4
  obtain ⟨t6, run6, st6, rip6, value6, eff6, _⟩ :=
    copy_stack (sourceOffset := 144) pre st5 0x191 (by decide) (by decide +kernel)
      eff5.rip 944 (by decide) (by decide) r7_5 r1_5
      (by decide) (by decide) (by decide) r6_5 p144_5
  have p272_6 := copy_point (offset := 272) pre eff6 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_5
  have p1040_6 := copy_point (offset := 1040) pre eff6 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_5
  have p144_6 := copy_point (offset := 144) pre eff6 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_5
  have p944_6 := value6
  have r3_6 : t6.regValue .rbx = s.regValue .rdi :=
    (eff6.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_5
  have r15_6 : t6.regValue .r15 = stackPtr s - 272 :=
    (eff6.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_5
  have r14_6 : t6.regValue .r14 = stackPtr s - 944 :=
    (eff6.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_5
  have r12_6 : t6.regValue .r12 = stackPtr s - 848 :=
    (eff6.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_5
  have r13_6 : t6.regValue .r13 = stackPtr s - 752 :=
    (eff6.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_5
  have r5_6 : t6.regValue .rbp = stackPtr s - 144 :=
    (eff6.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_5
  have scalar6 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t6 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar5
    apply memLoad_congr
    intro i hi
    change ( t6.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t5.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff6 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  exact ⟨n1 + 12 + n3 + n4 + n5 + 12, t6, (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6), st6, rip6,
    ⟨r3_6, r15_6, r14_6, r12_6, r13_6, r5_6, trivial⟩,
    ⟨p272_6, p1040_6, p144_6, p944_6, trivial⟩, scalar6⟩

end P256.Proofs.Ecdh.Table
