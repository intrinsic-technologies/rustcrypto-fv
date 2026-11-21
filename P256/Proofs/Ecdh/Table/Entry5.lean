import P256.Proofs.Ecdh.Table.Memory
import P256.Proofs.Ecdh.Table.Blocks

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Blocks

set_option maxRecDepth 32768 in
theorem entry5 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x10020e)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 3), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 3), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x100250 ∧ Facts s u [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 4), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 4), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3), (656, Projective.tableEntry point 4)] := by
  rcases facts.regs with ⟨r3_in, r15_in, r14_in, r12_in, r13_in, r5_in, trivial⟩
  rcases facts.points with ⟨p272_in, p1040_in, p144_in, p944_in, p1808_in, p848_in, p752_in, trivial⟩
  obtain ⟨n23, t23, run23, st23, eff23, mem23⟩ :=
    register_block (offset := 0x20e) (bytes := b114e5eBytes) (effect := b114e5eEffect) state (b114e5e_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b114e5eEffect, Effect.components, Component.Covers])
      (by simp [b114e5eEffect, Effect.components])
      (by simp [b114e5eEffect, Effect.components])
      (by simp [b114e5eEffect, Effect.components])
      (by simp [b114e5eEffect, Effect.components])
  have r14_23 : t23.regValue .r14 = stackPtr s - 1808 := by
    have h : t23.regValue .r14 = stackPtr t + 248 := eff23.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_23 : t23.regValue .rcx = 12 := eff23.writes.2.1
  have r7_23 : t23.regValue .rdi = stackPtr s - 1808 := by
    have h : t23.regValue .rdi = stackPtr t + 248 := eff23.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_23 : t23.regValue .rsi = stackPtr s - 272 := eff23.writes.2.2.2.trans r15_in
  have r3_23 : t23.regValue .rbx = s.regValue .rdi :=
    (eff23.agrees.read (n := 64) (r := 3) (by simp [b114e5eEffect, Effect.components])).trans r3_in
  have r15_23 : t23.regValue .r15 = stackPtr s - 272 :=
    (eff23.agrees.read (n := 64) (r := 15) (by simp [b114e5eEffect, Effect.components])).trans r15_in
  have r12_23 : t23.regValue .r12 = stackPtr s - 848 :=
    (eff23.agrees.read (n := 64) (r := 12) (by simp [b114e5eEffect, Effect.components])).trans r12_in
  have r13_23 : t23.regValue .r13 = stackPtr s - 752 :=
    (eff23.agrees.read (n := 64) (r := 13) (by simp [b114e5eEffect, Effect.components])).trans r13_in
  have r5_23 : t23.regValue .rbp = stackPtr s - 144 :=
    (eff23.agrees.read (n := 64) (r := 5) (by simp [b114e5eEffect, Effect.components])).trans r5_in
  have p272_23 := point_of_external p272_in mem23
  have p1040_23 := point_of_external p1040_in mem23
  have p144_23 := point_of_external p144_in mem23
  have p944_23 := point_of_external p944_in mem23
  have p1808_23 := point_of_external p1808_in mem23
  have p848_23 := point_of_external p848_in mem23
  have p752_23 := point_of_external p752_in mem23
  have scalar23 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t23 = s.regValue .rsi := by
    change memLoad t23.external _ 64 = _
    rw [mem23]
    exact facts.scalar
  obtain ⟨t24, run24, st24, rip24, value24, eff24, _⟩ :=
    copy_stack (sourceOffset := 272) pre st23 0x221 (by decide) (by decide +kernel)
      eff23.rip 1808 (by decide) (by decide) r7_23 r1_23
      (by decide) (by decide) (by decide) r6_23 p272_23
  have p272_24 := copy_point (offset := 272) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_23
  have p1040_24 := copy_point (offset := 1040) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_23
  have p144_24 := copy_point (offset := 144) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_23
  have p944_24 := copy_point (offset := 944) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_23
  have p1808_24 := value24
  have p848_24 := copy_point (offset := 848) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_23
  have p752_24 := copy_point (offset := 752) pre eff24 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_23
  have r3_24 : t24.regValue .rbx = s.regValue .rdi :=
    (eff24.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_23
  have r15_24 : t24.regValue .r15 = stackPtr s - 272 :=
    (eff24.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_23
  have r14_24 : t24.regValue .r14 = stackPtr s - 1808 :=
    (eff24.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_23
  have r12_24 : t24.regValue .r12 = stackPtr s - 848 :=
    (eff24.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_23
  have r13_24 : t24.regValue .r13 = stackPtr s - 752 :=
    (eff24.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_23
  have r5_24 : t24.regValue .rbp = stackPtr s - 144 :=
    (eff24.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_23
  have scalar24 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t24 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar23
    apply memLoad_congr
    intro i hi
    change ( t24.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t23.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff24 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n25, t25, run25, st25, eff25, mem25⟩ :=
    register_block (offset := 0x224) (bytes := b114e74Bytes) (effect := b114e74Effect) st24 (b114e74_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip24
      (by simp [b114e74Effect, Effect.components, Component.Covers])
      (by simp [b114e74Effect, Effect.components])
      (by simp [b114e74Effect, Effect.components])
      (by simp [b114e74Effect, Effect.components])
      (by simp [b114e74Effect, Effect.components])
  have r7_25 : t25.regValue .rdi = stackPtr s - 1808 := eff25.writes.1.trans r14_24
  have r6_25 : t25.regValue .rsi = stackPtr s - 144 := eff25.writes.2.trans r5_24
  have r3_25 : t25.regValue .rbx = s.regValue .rdi :=
    (eff25.agrees.read (n := 64) (r := 3) (by simp [b114e74Effect, Effect.components])).trans r3_24
  have r15_25 : t25.regValue .r15 = stackPtr s - 272 :=
    (eff25.agrees.read (n := 64) (r := 15) (by simp [b114e74Effect, Effect.components])).trans r15_24
  have r14_25 : t25.regValue .r14 = stackPtr s - 1808 :=
    (eff25.agrees.read (n := 64) (r := 14) (by simp [b114e74Effect, Effect.components])).trans r14_24
  have r12_25 : t25.regValue .r12 = stackPtr s - 848 :=
    (eff25.agrees.read (n := 64) (r := 12) (by simp [b114e74Effect, Effect.components])).trans r12_24
  have r13_25 : t25.regValue .r13 = stackPtr s - 752 :=
    (eff25.agrees.read (n := 64) (r := 13) (by simp [b114e74Effect, Effect.components])).trans r13_24
  have r5_25 : t25.regValue .rbp = stackPtr s - 144 :=
    (eff25.agrees.read (n := 64) (r := 5) (by simp [b114e74Effect, Effect.components])).trans r5_24
  have p272_25 := point_of_external p272_24 mem25
  have p1040_25 := point_of_external p1040_24 mem25
  have p144_25 := point_of_external p144_24 mem25
  have p944_25 := point_of_external p944_24 mem25
  have p1808_25 := point_of_external p1808_24 mem25
  have p848_25 := point_of_external p848_24 mem25
  have p752_25 := point_of_external p752_24 mem25
  have scalar25 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t25 = s.regValue .rsi := by
    change memLoad t25.external _ 64 = _
    rw [mem25]
    exact scalar24
  let site26 : P256.Proofs.Projective.Multiply.Machine.Loop.CallSite 0x1051f0 :=
    ⟨0x22a, 0x4fc1, by decide, by decide +kernel, by decide +kernel⟩
  obtain ⟨t26, result26⟩ := add_call (outputOffset := 1808) (sourceOffset := 144) pre st25
    site26 eff25.rip (by decide) (by decide) (by decide) (by decide) (by decide)
    r7_25 r6_25 p1808_25 p144_25
  obtain ⟨n26, run26⟩ := result26.execution
  have st26 := result26.toFrameState
  have p272_26 := call_point (offset := 272) result26 (by decide) (by decide) (by decide) p272_25
  have p1040_26 := call_point (offset := 1040) result26 (by decide) (by decide) (by decide) p1040_25
  have p144_26 := call_point (offset := 144) result26 (by decide) (by decide) (by decide) p144_25
  have p944_26 := call_point (offset := 944) result26 (by decide) (by decide) (by decide) p944_25
  have p1808_26 : ProjectiveAt t26 (stackPtr s - 1808) (Projective.tableEntry point 4) := result26.value
  have p848_26 := call_point (offset := 848) result26 (by decide) (by decide) (by decide) p848_25
  have p752_26 := call_point (offset := 752) result26 (by decide) (by decide) (by decide) p752_25
  have r3_26 : t26.regValue .rbx = s.regValue .rdi :=
    (result26.registers .rbx (by simp)).trans r3_25
  have r15_26 : t26.regValue .r15 = stackPtr s - 272 :=
    (result26.registers .r15 (by simp)).trans r15_25
  have r14_26 : t26.regValue .r14 = stackPtr s - 1808 :=
    (result26.registers .r14 (by simp)).trans r14_25
  have r12_26 : t26.regValue .r12 = stackPtr s - 848 :=
    (result26.registers .r12 (by simp)).trans r12_25
  have r13_26 : t26.regValue .r13 = stackPtr s - 752 :=
    (result26.registers .r13 (by simp)).trans r13_25
  have r5_26 : t26.regValue .rbp = stackPtr s - 144 :=
    (result26.registers .rbp (by simp)).trans r5_25
  have scalar26 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t26 = s.regValue .rsi :=
    (result26.read (by decide) (by decide) (by decide)).trans scalar25
  obtain ⟨n27, t27, run27, st27, eff27, mem27⟩ :=
    register_block (offset := 0x22f) (bytes := b114e7fBytes) (effect := b114e7fEffect) st26 (b114e7f_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result26.rip
      (by simp [b114e7fEffect, Effect.components, Component.Covers])
      (by simp [b114e7fEffect, Effect.components])
      (by simp [b114e7fEffect, Effect.components])
      (by simp [b114e7fEffect, Effect.components])
      (by simp [b114e7fEffect, Effect.components])
  have r1_27 : t27.regValue .rcx = 12 := eff27.writes.1
  have r7_27 : t27.regValue .rdi = stackPtr s - 144 := eff27.writes.2.1.trans r5_26
  have r6_27 : t27.regValue .rsi = stackPtr s - 1808 := eff27.writes.2.2.trans r14_26
  have r3_27 : t27.regValue .rbx = s.regValue .rdi :=
    (eff27.agrees.read (n := 64) (r := 3) (by simp [b114e7fEffect, Effect.components])).trans r3_26
  have r15_27 : t27.regValue .r15 = stackPtr s - 272 :=
    (eff27.agrees.read (n := 64) (r := 15) (by simp [b114e7fEffect, Effect.components])).trans r15_26
  have r14_27 : t27.regValue .r14 = stackPtr s - 1808 :=
    (eff27.agrees.read (n := 64) (r := 14) (by simp [b114e7fEffect, Effect.components])).trans r14_26
  have r12_27 : t27.regValue .r12 = stackPtr s - 848 :=
    (eff27.agrees.read (n := 64) (r := 12) (by simp [b114e7fEffect, Effect.components])).trans r12_26
  have r13_27 : t27.regValue .r13 = stackPtr s - 752 :=
    (eff27.agrees.read (n := 64) (r := 13) (by simp [b114e7fEffect, Effect.components])).trans r13_26
  have r5_27 : t27.regValue .rbp = stackPtr s - 144 :=
    (eff27.agrees.read (n := 64) (r := 5) (by simp [b114e7fEffect, Effect.components])).trans r5_26
  have p272_27 := point_of_external p272_26 mem27
  have p1040_27 := point_of_external p1040_26 mem27
  have p144_27 := point_of_external p144_26 mem27
  have p944_27 := point_of_external p944_26 mem27
  have p1808_27 := point_of_external p1808_26 mem27
  have p848_27 := point_of_external p848_26 mem27
  have p752_27 := point_of_external p752_26 mem27
  have scalar27 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t27 = s.regValue .rsi := by
    change memLoad t27.external _ 64 = _
    rw [mem27]
    exact scalar26
  obtain ⟨t28, run28, st28, rip28, value28, eff28, _⟩ :=
    copy_stack (sourceOffset := 1808) pre st27 0x23a (by decide) (by decide +kernel)
      eff27.rip 144 (by decide) (by decide) r7_27 r1_27
      (by decide) (by decide) (by decide) r6_27 p1808_27
  have p272_28 := copy_point (offset := 272) pre eff28 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_27
  have p1040_28 := copy_point (offset := 1040) pre eff28 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_27
  have p144_28 := value28
  have p944_28 := copy_point (offset := 944) pre eff28 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_27
  have p1808_28 := copy_point (offset := 1808) pre eff28 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_27
  have p848_28 := copy_point (offset := 848) pre eff28 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_27
  have p752_28 := copy_point (offset := 752) pre eff28 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_27
  have r3_28 : t28.regValue .rbx = s.regValue .rdi :=
    (eff28.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_27
  have r15_28 : t28.regValue .r15 = stackPtr s - 272 :=
    (eff28.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_27
  have r14_28 : t28.regValue .r14 = stackPtr s - 1808 :=
    (eff28.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_27
  have r12_28 : t28.regValue .r12 = stackPtr s - 848 :=
    (eff28.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_27
  have r13_28 : t28.regValue .r13 = stackPtr s - 752 :=
    (eff28.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_27
  have r5_28 : t28.regValue .rbp = stackPtr s - 144 :=
    (eff28.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_27
  have scalar28 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t28 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar27
    apply memLoad_congr
    intro i hi
    change ( t28.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t27.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff28 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n29, t29, run29, st29, eff29, mem29⟩ :=
    register_block (offset := 0x23d) (bytes := b114e8dBytes) (effect := b114e8dEffect) st28 (b114e8d_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip28
      (by simp [b114e8dEffect, Effect.components, Component.Covers])
      (by simp [b114e8dEffect, Effect.components])
      (by simp [b114e8dEffect, Effect.components])
      (by simp [b114e8dEffect, Effect.components])
      (by simp [b114e8dEffect, Effect.components])
  have r1_29 : t29.regValue .rcx = 12 := eff29.writes.1
  have r7_29 : t29.regValue .rdi = stackPtr s - 656 := by
    have h : t29.regValue .rdi = stackPtr t28 + 1400 := eff29.writes.2.1
    exact h.trans (scalar_stack_address st28.rsp (by decide) (by decide))
  have r6_29 : t29.regValue .rsi = stackPtr s - 144 := eff29.writes.2.2.trans r5_28
  have r3_29 : t29.regValue .rbx = s.regValue .rdi :=
    (eff29.agrees.read (n := 64) (r := 3) (by simp [b114e8dEffect, Effect.components])).trans r3_28
  have r15_29 : t29.regValue .r15 = stackPtr s - 272 :=
    (eff29.agrees.read (n := 64) (r := 15) (by simp [b114e8dEffect, Effect.components])).trans r15_28
  have r14_29 : t29.regValue .r14 = stackPtr s - 1808 :=
    (eff29.agrees.read (n := 64) (r := 14) (by simp [b114e8dEffect, Effect.components])).trans r14_28
  have r12_29 : t29.regValue .r12 = stackPtr s - 848 :=
    (eff29.agrees.read (n := 64) (r := 12) (by simp [b114e8dEffect, Effect.components])).trans r12_28
  have r13_29 : t29.regValue .r13 = stackPtr s - 752 :=
    (eff29.agrees.read (n := 64) (r := 13) (by simp [b114e8dEffect, Effect.components])).trans r13_28
  have r5_29 : t29.regValue .rbp = stackPtr s - 144 :=
    (eff29.agrees.read (n := 64) (r := 5) (by simp [b114e8dEffect, Effect.components])).trans r5_28
  have p272_29 := point_of_external p272_28 mem29
  have p1040_29 := point_of_external p1040_28 mem29
  have p144_29 := point_of_external p144_28 mem29
  have p944_29 := point_of_external p944_28 mem29
  have p1808_29 := point_of_external p1808_28 mem29
  have p848_29 := point_of_external p848_28 mem29
  have p752_29 := point_of_external p752_28 mem29
  have scalar29 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t29 = s.regValue .rsi := by
    change memLoad t29.external _ 64 = _
    rw [mem29]
    exact scalar28
  obtain ⟨t30, run30, st30, rip30, value30, eff30, _⟩ :=
    copy_stack (sourceOffset := 144) pre st29 0x24d (by decide) (by decide +kernel)
      eff29.rip 656 (by decide) (by decide) r7_29 r1_29
      (by decide) (by decide) (by decide) r6_29 p144_29
  have p272_30 := copy_point (offset := 272) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_29
  have p1040_30 := copy_point (offset := 1040) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_29
  have p144_30 := copy_point (offset := 144) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_29
  have p944_30 := copy_point (offset := 944) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_29
  have p1808_30 := copy_point (offset := 1808) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_29
  have p848_30 := copy_point (offset := 848) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_29
  have p752_30 := copy_point (offset := 752) pre eff30 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_29
  have p656_30 := value30
  have r3_30 : t30.regValue .rbx = s.regValue .rdi :=
    (eff30.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_29
  have r15_30 : t30.regValue .r15 = stackPtr s - 272 :=
    (eff30.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_29
  have r14_30 : t30.regValue .r14 = stackPtr s - 1808 :=
    (eff30.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_29
  have r12_30 : t30.regValue .r12 = stackPtr s - 848 :=
    (eff30.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_29
  have r13_30 : t30.regValue .r13 = stackPtr s - 752 :=
    (eff30.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_29
  have r5_30 : t30.regValue .rbp = stackPtr s - 144 :=
    (eff30.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_29
  have scalar30 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t30 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar29
    apply memLoad_congr
    intro i hi
    change ( t30.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t29.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff30 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  exact ⟨n23 + 12 + n25 + n26 + n27 + 12 + n29 + 12, t30, (((((((run23.trans run24).trans run25).trans run26).trans run27).trans run28).trans run29).trans run30), st30, rip30,
    ⟨r3_30, r15_30, r14_30, r12_30, r13_30, r5_30, trivial⟩,
    ⟨p272_30, p1040_30, p144_30, p944_30, p1808_30, p848_30, p752_30, p656_30, trivial⟩, scalar30⟩

end P256.Proofs.Ecdh.Table
