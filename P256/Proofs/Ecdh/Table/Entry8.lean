import P256.Proofs.Ecdh.Table.Memory
import P256.Proofs.Ecdh.Table.Blocks

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Blocks

set_option maxRecDepth 32768 in
theorem entry8 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x1002d4)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 6), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 6), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3), (656, Projective.tableEntry point 4), (560, Projective.tableEntry point 5), (464, Projective.tableEntry point 6)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x1002f2 ∧ Facts s u [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 7), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 6), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 6), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3), (656, Projective.tableEntry point 4), (560, Projective.tableEntry point 5), (464, Projective.tableEntry point 6), (368, Projective.tableEntry point 7)] := by
  rcases facts.regs with ⟨r3_in, r15_in, r14_in, r12_in, r13_in, r5_in, trivial⟩
  rcases facts.points with ⟨p272_in, p1040_in, p144_in, p944_in, p1808_in, p848_in, p752_in, p656_in, p560_in, p464_in, trivial⟩
  obtain ⟨n47, t47, run47, st47, eff47, mem47⟩ :=
    register_block (offset := 0x2d4) (bytes := b114f24Bytes) (effect := b114f24Effect) state (b114f24_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b114f24Effect, Effect.components, Component.Covers])
      (by simp [b114f24Effect, Effect.components])
      (by simp [b114f24Effect, Effect.components])
      (by simp [b114f24Effect, Effect.components])
      (by simp [b114f24Effect, Effect.components])
  have r7_47 : t47.regValue .rdi = stackPtr s - 272 := eff47.writes.1.trans r15_in
  have r6_47 : t47.regValue .rsi = stackPtr s - 144 := eff47.writes.2.trans r5_in
  have r3_47 : t47.regValue .rbx = s.regValue .rdi :=
    (eff47.agrees.read (n := 64) (r := 3) (by simp [b114f24Effect, Effect.components])).trans r3_in
  have r15_47 : t47.regValue .r15 = stackPtr s - 272 :=
    (eff47.agrees.read (n := 64) (r := 15) (by simp [b114f24Effect, Effect.components])).trans r15_in
  have r14_47 : t47.regValue .r14 = stackPtr s - 1808 :=
    (eff47.agrees.read (n := 64) (r := 14) (by simp [b114f24Effect, Effect.components])).trans r14_in
  have r12_47 : t47.regValue .r12 = stackPtr s - 848 :=
    (eff47.agrees.read (n := 64) (r := 12) (by simp [b114f24Effect, Effect.components])).trans r12_in
  have r13_47 : t47.regValue .r13 = stackPtr s - 752 :=
    (eff47.agrees.read (n := 64) (r := 13) (by simp [b114f24Effect, Effect.components])).trans r13_in
  have r5_47 : t47.regValue .rbp = stackPtr s - 144 :=
    (eff47.agrees.read (n := 64) (r := 5) (by simp [b114f24Effect, Effect.components])).trans r5_in
  have p272_47 := point_of_external p272_in mem47
  have p1040_47 := point_of_external p1040_in mem47
  have p144_47 := point_of_external p144_in mem47
  have p944_47 := point_of_external p944_in mem47
  have p1808_47 := point_of_external p1808_in mem47
  have p848_47 := point_of_external p848_in mem47
  have p752_47 := point_of_external p752_in mem47
  have p656_47 := point_of_external p656_in mem47
  have p560_47 := point_of_external p560_in mem47
  have p464_47 := point_of_external p464_in mem47
  have scalar47 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t47 = s.regValue .rsi := by
    change memLoad t47.external _ 64 = _
    rw [mem47]
    exact facts.scalar
  let site48 : P256.Proofs.Projective.Multiply.Machine.Loop.CallSite 0x1051f0 :=
    ⟨0x2da, 0x4f11, by decide, by decide +kernel, by decide +kernel⟩
  obtain ⟨t48, result48⟩ := add_call (outputOffset := 272) (sourceOffset := 144) pre st47
    site48 eff47.rip (by decide) (by decide) (by decide) (by decide) (by decide)
    r7_47 r6_47 p272_47 p144_47
  obtain ⟨n48, run48⟩ := result48.execution
  have st48 := result48.toFrameState
  have p272_48 : ProjectiveAt t48 (stackPtr s - 272) (Projective.tableEntry point 7) := result48.value
  have p1040_48 := call_point (offset := 1040) result48 (by decide) (by decide) (by decide) p1040_47
  have p144_48 := call_point (offset := 144) result48 (by decide) (by decide) (by decide) p144_47
  have p944_48 := call_point (offset := 944) result48 (by decide) (by decide) (by decide) p944_47
  have p1808_48 := call_point (offset := 1808) result48 (by decide) (by decide) (by decide) p1808_47
  have p848_48 := call_point (offset := 848) result48 (by decide) (by decide) (by decide) p848_47
  have p752_48 := call_point (offset := 752) result48 (by decide) (by decide) (by decide) p752_47
  have p656_48 := call_point (offset := 656) result48 (by decide) (by decide) (by decide) p656_47
  have p560_48 := call_point (offset := 560) result48 (by decide) (by decide) (by decide) p560_47
  have p464_48 := call_point (offset := 464) result48 (by decide) (by decide) (by decide) p464_47
  have r3_48 : t48.regValue .rbx = s.regValue .rdi :=
    (result48.registers .rbx (by simp)).trans r3_47
  have r15_48 : t48.regValue .r15 = stackPtr s - 272 :=
    (result48.registers .r15 (by simp)).trans r15_47
  have r14_48 : t48.regValue .r14 = stackPtr s - 1808 :=
    (result48.registers .r14 (by simp)).trans r14_47
  have r12_48 : t48.regValue .r12 = stackPtr s - 848 :=
    (result48.registers .r12 (by simp)).trans r12_47
  have r13_48 : t48.regValue .r13 = stackPtr s - 752 :=
    (result48.registers .r13 (by simp)).trans r13_47
  have r5_48 : t48.regValue .rbp = stackPtr s - 144 :=
    (result48.registers .rbp (by simp)).trans r5_47
  have scalar48 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t48 = s.regValue .rsi :=
    (result48.read (by decide) (by decide) (by decide)).trans scalar47
  obtain ⟨n49, t49, run49, st49, eff49, mem49⟩ :=
    register_block (offset := 0x2df) (bytes := b114f2fBytes) (effect := b114f2fEffect) st48 (b114f2f_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result48.rip
      (by simp [b114f2fEffect, Effect.components, Component.Covers])
      (by simp [b114f2fEffect, Effect.components])
      (by simp [b114f2fEffect, Effect.components])
      (by simp [b114f2fEffect, Effect.components])
      (by simp [b114f2fEffect, Effect.components])
  have r1_49 : t49.regValue .rcx = 12 := eff49.writes.1
  have r7_49 : t49.regValue .rdi = stackPtr s - 368 := by
    have h : t49.regValue .rdi = stackPtr t48 + 1688 := eff49.writes.2.1
    exact h.trans (scalar_stack_address st48.rsp (by decide) (by decide))
  have r6_49 : t49.regValue .rsi = stackPtr s - 272 := eff49.writes.2.2.trans r15_48
  have r3_49 : t49.regValue .rbx = s.regValue .rdi :=
    (eff49.agrees.read (n := 64) (r := 3) (by simp [b114f2fEffect, Effect.components])).trans r3_48
  have r15_49 : t49.regValue .r15 = stackPtr s - 272 :=
    (eff49.agrees.read (n := 64) (r := 15) (by simp [b114f2fEffect, Effect.components])).trans r15_48
  have r14_49 : t49.regValue .r14 = stackPtr s - 1808 :=
    (eff49.agrees.read (n := 64) (r := 14) (by simp [b114f2fEffect, Effect.components])).trans r14_48
  have r12_49 : t49.regValue .r12 = stackPtr s - 848 :=
    (eff49.agrees.read (n := 64) (r := 12) (by simp [b114f2fEffect, Effect.components])).trans r12_48
  have r13_49 : t49.regValue .r13 = stackPtr s - 752 :=
    (eff49.agrees.read (n := 64) (r := 13) (by simp [b114f2fEffect, Effect.components])).trans r13_48
  have r5_49 : t49.regValue .rbp = stackPtr s - 144 :=
    (eff49.agrees.read (n := 64) (r := 5) (by simp [b114f2fEffect, Effect.components])).trans r5_48
  have p272_49 := point_of_external p272_48 mem49
  have p1040_49 := point_of_external p1040_48 mem49
  have p144_49 := point_of_external p144_48 mem49
  have p944_49 := point_of_external p944_48 mem49
  have p1808_49 := point_of_external p1808_48 mem49
  have p848_49 := point_of_external p848_48 mem49
  have p752_49 := point_of_external p752_48 mem49
  have p656_49 := point_of_external p656_48 mem49
  have p560_49 := point_of_external p560_48 mem49
  have p464_49 := point_of_external p464_48 mem49
  have scalar49 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t49 = s.regValue .rsi := by
    change memLoad t49.external _ 64 = _
    rw [mem49]
    exact scalar48
  obtain ⟨t50, run50, st50, rip50, value50, eff50, _⟩ :=
    copy_stack (sourceOffset := 272) pre st49 0x2ef (by decide) (by decide +kernel)
      eff49.rip 368 (by decide) (by decide) r7_49 r1_49
      (by decide) (by decide) (by decide) r6_49 p272_49
  have p272_50 := copy_point (offset := 272) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_49
  have p1040_50 := copy_point (offset := 1040) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_49
  have p144_50 := copy_point (offset := 144) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_49
  have p944_50 := copy_point (offset := 944) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_49
  have p1808_50 := copy_point (offset := 1808) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_49
  have p848_50 := copy_point (offset := 848) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_49
  have p752_50 := copy_point (offset := 752) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_49
  have p656_50 := copy_point (offset := 656) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p656_49
  have p560_50 := copy_point (offset := 560) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p560_49
  have p464_50 := copy_point (offset := 464) pre eff50 (by decide) (by decide)
    (by decide) (by decide) (by decide) p464_49
  have p368_50 := value50
  have r3_50 : t50.regValue .rbx = s.regValue .rdi :=
    (eff50.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_49
  have r15_50 : t50.regValue .r15 = stackPtr s - 272 :=
    (eff50.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_49
  have r14_50 : t50.regValue .r14 = stackPtr s - 1808 :=
    (eff50.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_49
  have r12_50 : t50.regValue .r12 = stackPtr s - 848 :=
    (eff50.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_49
  have r13_50 : t50.regValue .r13 = stackPtr s - 752 :=
    (eff50.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_49
  have r5_50 : t50.regValue .rbp = stackPtr s - 144 :=
    (eff50.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_49
  have scalar50 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t50 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar49
    apply memLoad_congr
    intro i hi
    change ( t50.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t49.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff50 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  exact ⟨n47 + n48 + n49 + 12, t50, (((run47.trans run48).trans run49).trans run50), st50, rip50,
    ⟨r3_50, r15_50, r14_50, r12_50, r13_50, r5_50, trivial⟩,
    ⟨p272_50, p1040_50, p144_50, p944_50, p1808_50, p848_50, p752_50, p656_50, p560_50, p464_50, p368_50, trivial⟩, scalar50⟩

end P256.Proofs.Ecdh.Table
