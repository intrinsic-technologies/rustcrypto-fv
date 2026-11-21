import P256.Proofs.Ecdh.Table.Memory
import P256.Proofs.Ecdh.Table.Blocks

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Blocks

set_option maxRecDepth 32768 in
theorem entry4 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x1001d1)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 2), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 2), (848, Projective.tableEntry point 2)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x10020e ∧ Facts s u [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 3), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 3), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3)] := by
  rcases facts.regs with ⟨r3_in, r15_in, r14_in, r12_in, r13_in, r5_in, trivial⟩
  rcases facts.points with ⟨p272_in, p1040_in, p144_in, p944_in, p1808_in, p848_in, trivial⟩
  obtain ⟨n15, t15, run15, st15, eff15, mem15⟩ :=
    register_block (offset := 0x1d1) (bytes := b114e21Bytes) (effect := b114e21Effect) state (b114e21_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b114e21Effect, Effect.components, Component.Covers])
      (by simp [b114e21Effect, Effect.components])
      (by simp [b114e21Effect, Effect.components])
      (by simp [b114e21Effect, Effect.components])
      (by simp [b114e21Effect, Effect.components])
  have r14_15 : t15.regValue .r14 = stackPtr s - 1808 := by
    have h : t15.regValue .r14 = stackPtr t + 248 := eff15.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_15 : t15.regValue .rcx = 12 := eff15.writes.2.1
  have r7_15 : t15.regValue .rdi = stackPtr s - 1808 := by
    have h : t15.regValue .rdi = stackPtr t + 248 := eff15.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_15 : t15.regValue .rsi = stackPtr s - 272 := eff15.writes.2.2.2.trans r15_in
  have r3_15 : t15.regValue .rbx = s.regValue .rdi :=
    (eff15.agrees.read (n := 64) (r := 3) (by simp [b114e21Effect, Effect.components])).trans r3_in
  have r15_15 : t15.regValue .r15 = stackPtr s - 272 :=
    (eff15.agrees.read (n := 64) (r := 15) (by simp [b114e21Effect, Effect.components])).trans r15_in
  have r12_15 : t15.regValue .r12 = stackPtr s - 848 :=
    (eff15.agrees.read (n := 64) (r := 12) (by simp [b114e21Effect, Effect.components])).trans r12_in
  have r13_15 : t15.regValue .r13 = stackPtr s - 752 :=
    (eff15.agrees.read (n := 64) (r := 13) (by simp [b114e21Effect, Effect.components])).trans r13_in
  have r5_15 : t15.regValue .rbp = stackPtr s - 144 :=
    (eff15.agrees.read (n := 64) (r := 5) (by simp [b114e21Effect, Effect.components])).trans r5_in
  have p272_15 := point_of_external p272_in mem15
  have p1040_15 := point_of_external p1040_in mem15
  have p144_15 := point_of_external p144_in mem15
  have p944_15 := point_of_external p944_in mem15
  have p1808_15 := point_of_external p1808_in mem15
  have p848_15 := point_of_external p848_in mem15
  have scalar15 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t15 = s.regValue .rsi := by
    change memLoad t15.external _ 64 = _
    rw [mem15]
    exact facts.scalar
  obtain ⟨t16, run16, st16, rip16, value16, eff16, _⟩ :=
    copy_stack (sourceOffset := 272) pre st15 0x1e4 (by decide) (by decide +kernel)
      eff15.rip 1808 (by decide) (by decide) r7_15 r1_15
      (by decide) (by decide) (by decide) r6_15 p272_15
  have p272_16 := copy_point (offset := 272) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_15
  have p1040_16 := copy_point (offset := 1040) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_15
  have p144_16 := copy_point (offset := 144) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_15
  have p944_16 := copy_point (offset := 944) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_15
  have p1808_16 := value16
  have p848_16 := copy_point (offset := 848) pre eff16 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_15
  have r3_16 : t16.regValue .rbx = s.regValue .rdi :=
    (eff16.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_15
  have r15_16 : t16.regValue .r15 = stackPtr s - 272 :=
    (eff16.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_15
  have r14_16 : t16.regValue .r14 = stackPtr s - 1808 :=
    (eff16.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_15
  have r12_16 : t16.regValue .r12 = stackPtr s - 848 :=
    (eff16.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_15
  have r13_16 : t16.regValue .r13 = stackPtr s - 752 :=
    (eff16.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_15
  have r5_16 : t16.regValue .rbp = stackPtr s - 144 :=
    (eff16.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_15
  have scalar16 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t16 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar15
    apply memLoad_congr
    intro i hi
    change ( t16.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t15.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff16 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n17, t17, run17, st17, eff17, mem17⟩ :=
    register_block (offset := 0x1e7) (bytes := b114e37Bytes) (effect := b114e37Effect) st16 (b114e37_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip16
      (by simp [b114e37Effect, Effect.components, Component.Covers])
      (by simp [b114e37Effect, Effect.components])
      (by simp [b114e37Effect, Effect.components])
      (by simp [b114e37Effect, Effect.components])
      (by simp [b114e37Effect, Effect.components])
  have r7_17 : t17.regValue .rdi = stackPtr s - 1808 := eff17.writes.1.trans r14_16
  have r6_17 : t17.regValue .rsi = stackPtr s - 144 := eff17.writes.2.trans r5_16
  have r3_17 : t17.regValue .rbx = s.regValue .rdi :=
    (eff17.agrees.read (n := 64) (r := 3) (by simp [b114e37Effect, Effect.components])).trans r3_16
  have r15_17 : t17.regValue .r15 = stackPtr s - 272 :=
    (eff17.agrees.read (n := 64) (r := 15) (by simp [b114e37Effect, Effect.components])).trans r15_16
  have r14_17 : t17.regValue .r14 = stackPtr s - 1808 :=
    (eff17.agrees.read (n := 64) (r := 14) (by simp [b114e37Effect, Effect.components])).trans r14_16
  have r12_17 : t17.regValue .r12 = stackPtr s - 848 :=
    (eff17.agrees.read (n := 64) (r := 12) (by simp [b114e37Effect, Effect.components])).trans r12_16
  have r13_17 : t17.regValue .r13 = stackPtr s - 752 :=
    (eff17.agrees.read (n := 64) (r := 13) (by simp [b114e37Effect, Effect.components])).trans r13_16
  have r5_17 : t17.regValue .rbp = stackPtr s - 144 :=
    (eff17.agrees.read (n := 64) (r := 5) (by simp [b114e37Effect, Effect.components])).trans r5_16
  have p272_17 := point_of_external p272_16 mem17
  have p1040_17 := point_of_external p1040_16 mem17
  have p144_17 := point_of_external p144_16 mem17
  have p944_17 := point_of_external p944_16 mem17
  have p1808_17 := point_of_external p1808_16 mem17
  have p848_17 := point_of_external p848_16 mem17
  have scalar17 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t17 = s.regValue .rsi := by
    change memLoad t17.external _ 64 = _
    rw [mem17]
    exact scalar16
  let site18 : P256.Proofs.Projective.Multiply.Machine.Loop.CallSite 0x1051f0 :=
    ⟨0x1ed, 0x4ffe, by decide, by decide +kernel, by decide +kernel⟩
  obtain ⟨t18, result18⟩ := add_call (outputOffset := 1808) (sourceOffset := 144) pre st17
    site18 eff17.rip (by decide) (by decide) (by decide) (by decide) (by decide)
    r7_17 r6_17 p1808_17 p144_17
  obtain ⟨n18, run18⟩ := result18.execution
  have st18 := result18.toFrameState
  have p272_18 := call_point (offset := 272) result18 (by decide) (by decide) (by decide) p272_17
  have p1040_18 := call_point (offset := 1040) result18 (by decide) (by decide) (by decide) p1040_17
  have p144_18 := call_point (offset := 144) result18 (by decide) (by decide) (by decide) p144_17
  have p944_18 := call_point (offset := 944) result18 (by decide) (by decide) (by decide) p944_17
  have p1808_18 : ProjectiveAt t18 (stackPtr s - 1808) (Projective.tableEntry point 3) := result18.value
  have p848_18 := call_point (offset := 848) result18 (by decide) (by decide) (by decide) p848_17
  have r3_18 : t18.regValue .rbx = s.regValue .rdi :=
    (result18.registers .rbx (by simp)).trans r3_17
  have r15_18 : t18.regValue .r15 = stackPtr s - 272 :=
    (result18.registers .r15 (by simp)).trans r15_17
  have r14_18 : t18.regValue .r14 = stackPtr s - 1808 :=
    (result18.registers .r14 (by simp)).trans r14_17
  have r12_18 : t18.regValue .r12 = stackPtr s - 848 :=
    (result18.registers .r12 (by simp)).trans r12_17
  have r13_18 : t18.regValue .r13 = stackPtr s - 752 :=
    (result18.registers .r13 (by simp)).trans r13_17
  have r5_18 : t18.regValue .rbp = stackPtr s - 144 :=
    (result18.registers .rbp (by simp)).trans r5_17
  have scalar18 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t18 = s.regValue .rsi :=
    (result18.read (by decide) (by decide) (by decide)).trans scalar17
  obtain ⟨n19, t19, run19, st19, eff19, mem19⟩ :=
    register_block (offset := 0x1f2) (bytes := b114e42Bytes) (effect := b114e42Effect) st18 (b114e42_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result18.rip
      (by simp [b114e42Effect, Effect.components, Component.Covers])
      (by simp [b114e42Effect, Effect.components])
      (by simp [b114e42Effect, Effect.components])
      (by simp [b114e42Effect, Effect.components])
      (by simp [b114e42Effect, Effect.components])
  have r1_19 : t19.regValue .rcx = 12 := eff19.writes.1
  have r7_19 : t19.regValue .rdi = stackPtr s - 144 := eff19.writes.2.1.trans r5_18
  have r6_19 : t19.regValue .rsi = stackPtr s - 1808 := eff19.writes.2.2.trans r14_18
  have r3_19 : t19.regValue .rbx = s.regValue .rdi :=
    (eff19.agrees.read (n := 64) (r := 3) (by simp [b114e42Effect, Effect.components])).trans r3_18
  have r15_19 : t19.regValue .r15 = stackPtr s - 272 :=
    (eff19.agrees.read (n := 64) (r := 15) (by simp [b114e42Effect, Effect.components])).trans r15_18
  have r14_19 : t19.regValue .r14 = stackPtr s - 1808 :=
    (eff19.agrees.read (n := 64) (r := 14) (by simp [b114e42Effect, Effect.components])).trans r14_18
  have r12_19 : t19.regValue .r12 = stackPtr s - 848 :=
    (eff19.agrees.read (n := 64) (r := 12) (by simp [b114e42Effect, Effect.components])).trans r12_18
  have r13_19 : t19.regValue .r13 = stackPtr s - 752 :=
    (eff19.agrees.read (n := 64) (r := 13) (by simp [b114e42Effect, Effect.components])).trans r13_18
  have r5_19 : t19.regValue .rbp = stackPtr s - 144 :=
    (eff19.agrees.read (n := 64) (r := 5) (by simp [b114e42Effect, Effect.components])).trans r5_18
  have p272_19 := point_of_external p272_18 mem19
  have p1040_19 := point_of_external p1040_18 mem19
  have p144_19 := point_of_external p144_18 mem19
  have p944_19 := point_of_external p944_18 mem19
  have p1808_19 := point_of_external p1808_18 mem19
  have p848_19 := point_of_external p848_18 mem19
  have scalar19 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t19 = s.regValue .rsi := by
    change memLoad t19.external _ 64 = _
    rw [mem19]
    exact scalar18
  obtain ⟨t20, run20, st20, rip20, value20, eff20, _⟩ :=
    copy_stack (sourceOffset := 1808) pre st19 0x1fd (by decide) (by decide +kernel)
      eff19.rip 144 (by decide) (by decide) r7_19 r1_19
      (by decide) (by decide) (by decide) r6_19 p1808_19
  have p272_20 := copy_point (offset := 272) pre eff20 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_19
  have p1040_20 := copy_point (offset := 1040) pre eff20 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_19
  have p144_20 := value20
  have p944_20 := copy_point (offset := 944) pre eff20 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_19
  have p1808_20 := copy_point (offset := 1808) pre eff20 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_19
  have p848_20 := copy_point (offset := 848) pre eff20 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_19
  have r3_20 : t20.regValue .rbx = s.regValue .rdi :=
    (eff20.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_19
  have r15_20 : t20.regValue .r15 = stackPtr s - 272 :=
    (eff20.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_19
  have r14_20 : t20.regValue .r14 = stackPtr s - 1808 :=
    (eff20.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_19
  have r12_20 : t20.regValue .r12 = stackPtr s - 848 :=
    (eff20.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_19
  have r13_20 : t20.regValue .r13 = stackPtr s - 752 :=
    (eff20.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_19
  have r5_20 : t20.regValue .rbp = stackPtr s - 144 :=
    (eff20.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_19
  have scalar20 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t20 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar19
    apply memLoad_congr
    intro i hi
    change ( t20.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t19.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff20 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n21, t21, run21, st21, eff21, mem21⟩ :=
    register_block (offset := 0x200) (bytes := b114e50Bytes) (effect := b114e50Effect) st20 (b114e50_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip20
      (by simp [b114e50Effect, Effect.components, Component.Covers])
      (by simp [b114e50Effect, Effect.components])
      (by simp [b114e50Effect, Effect.components])
      (by simp [b114e50Effect, Effect.components])
      (by simp [b114e50Effect, Effect.components])
  have r1_21 : t21.regValue .rcx = 12 := eff21.writes.1
  have r7_21 : t21.regValue .rdi = stackPtr s - 752 := eff21.writes.2.1.trans r13_20
  have r6_21 : t21.regValue .rsi = stackPtr s - 144 := eff21.writes.2.2.trans r5_20
  have r3_21 : t21.regValue .rbx = s.regValue .rdi :=
    (eff21.agrees.read (n := 64) (r := 3) (by simp [b114e50Effect, Effect.components])).trans r3_20
  have r15_21 : t21.regValue .r15 = stackPtr s - 272 :=
    (eff21.agrees.read (n := 64) (r := 15) (by simp [b114e50Effect, Effect.components])).trans r15_20
  have r14_21 : t21.regValue .r14 = stackPtr s - 1808 :=
    (eff21.agrees.read (n := 64) (r := 14) (by simp [b114e50Effect, Effect.components])).trans r14_20
  have r12_21 : t21.regValue .r12 = stackPtr s - 848 :=
    (eff21.agrees.read (n := 64) (r := 12) (by simp [b114e50Effect, Effect.components])).trans r12_20
  have r13_21 : t21.regValue .r13 = stackPtr s - 752 :=
    (eff21.agrees.read (n := 64) (r := 13) (by simp [b114e50Effect, Effect.components])).trans r13_20
  have r5_21 : t21.regValue .rbp = stackPtr s - 144 :=
    (eff21.agrees.read (n := 64) (r := 5) (by simp [b114e50Effect, Effect.components])).trans r5_20
  have p272_21 := point_of_external p272_20 mem21
  have p1040_21 := point_of_external p1040_20 mem21
  have p144_21 := point_of_external p144_20 mem21
  have p944_21 := point_of_external p944_20 mem21
  have p1808_21 := point_of_external p1808_20 mem21
  have p848_21 := point_of_external p848_20 mem21
  have scalar21 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t21 = s.regValue .rsi := by
    change memLoad t21.external _ 64 = _
    rw [mem21]
    exact scalar20
  obtain ⟨t22, run22, st22, rip22, value22, eff22, _⟩ :=
    copy_stack (sourceOffset := 144) pre st21 0x20b (by decide) (by decide +kernel)
      eff21.rip 752 (by decide) (by decide) r7_21 r1_21
      (by decide) (by decide) (by decide) r6_21 p144_21
  have p272_22 := copy_point (offset := 272) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_21
  have p1040_22 := copy_point (offset := 1040) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_21
  have p144_22 := copy_point (offset := 144) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_21
  have p944_22 := copy_point (offset := 944) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_21
  have p1808_22 := copy_point (offset := 1808) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_21
  have p848_22 := copy_point (offset := 848) pre eff22 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_21
  have p752_22 := value22
  have r3_22 : t22.regValue .rbx = s.regValue .rdi :=
    (eff22.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_21
  have r15_22 : t22.regValue .r15 = stackPtr s - 272 :=
    (eff22.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_21
  have r14_22 : t22.regValue .r14 = stackPtr s - 1808 :=
    (eff22.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_21
  have r12_22 : t22.regValue .r12 = stackPtr s - 848 :=
    (eff22.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_21
  have r13_22 : t22.regValue .r13 = stackPtr s - 752 :=
    (eff22.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_21
  have r5_22 : t22.regValue .rbp = stackPtr s - 144 :=
    (eff22.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_21
  have scalar22 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t22 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar21
    apply memLoad_congr
    intro i hi
    change ( t22.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t21.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff22 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  exact ⟨n15 + 12 + n17 + n18 + n19 + 12 + n21 + 12, t22, (((((((run15.trans run16).trans run17).trans run18).trans run19).trans run20).trans run21).trans run22), st22, rip22,
    ⟨r3_22, r15_22, r14_22, r12_22, r13_22, r5_22, trivial⟩,
    ⟨p272_22, p1040_22, p144_22, p944_22, p1808_22, p848_22, p752_22, trivial⟩, scalar22⟩

end P256.Proofs.Ecdh.Table
