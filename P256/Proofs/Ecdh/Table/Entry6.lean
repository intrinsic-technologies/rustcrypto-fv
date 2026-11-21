import P256.Proofs.Ecdh.Table.Memory
import P256.Proofs.Ecdh.Table.Blocks

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Blocks

set_option maxRecDepth 32768 in
theorem entry6 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x100250)
    (facts : Facts s t [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 4), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 4), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3), (656, Projective.tableEntry point 4)]) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x100292 ∧ Facts s u [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272), (.r14, stackPtr s - 1808), (.r12, stackPtr s - 848), (.r13, stackPtr s - 752), (.rbp, stackPtr s - 144)]
      [(272, Projective.tableEntry point 0), (1040, Projective.tableEntry point 0), (144, Projective.tableEntry point 5), (944, Projective.tableEntry point 1), (1808, Projective.tableEntry point 5), (848, Projective.tableEntry point 2), (752, Projective.tableEntry point 3), (656, Projective.tableEntry point 4), (560, Projective.tableEntry point 5)] := by
  rcases facts.regs with ⟨r3_in, r15_in, r14_in, r12_in, r13_in, r5_in, trivial⟩
  rcases facts.points with ⟨p272_in, p1040_in, p144_in, p944_in, p1808_in, p848_in, p752_in, p656_in, trivial⟩
  obtain ⟨n31, t31, run31, st31, eff31, mem31⟩ :=
    register_block (offset := 0x250) (bytes := b114ea0Bytes) (effect := b114ea0Effect) state (b114ea0_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip
      (by simp [b114ea0Effect, Effect.components, Component.Covers])
      (by simp [b114ea0Effect, Effect.components])
      (by simp [b114ea0Effect, Effect.components])
      (by simp [b114ea0Effect, Effect.components])
      (by simp [b114ea0Effect, Effect.components])
  have r14_31 : t31.regValue .r14 = stackPtr s - 1808 := by
    have h : t31.regValue .r14 = stackPtr t + 248 := eff31.writes.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r1_31 : t31.regValue .rcx = 12 := eff31.writes.2.1
  have r7_31 : t31.regValue .rdi = stackPtr s - 1808 := by
    have h : t31.regValue .rdi = stackPtr t + 248 := eff31.writes.2.2.1
    exact h.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have r6_31 : t31.regValue .rsi = stackPtr s - 272 := eff31.writes.2.2.2.trans r15_in
  have r3_31 : t31.regValue .rbx = s.regValue .rdi :=
    (eff31.agrees.read (n := 64) (r := 3) (by simp [b114ea0Effect, Effect.components])).trans r3_in
  have r15_31 : t31.regValue .r15 = stackPtr s - 272 :=
    (eff31.agrees.read (n := 64) (r := 15) (by simp [b114ea0Effect, Effect.components])).trans r15_in
  have r12_31 : t31.regValue .r12 = stackPtr s - 848 :=
    (eff31.agrees.read (n := 64) (r := 12) (by simp [b114ea0Effect, Effect.components])).trans r12_in
  have r13_31 : t31.regValue .r13 = stackPtr s - 752 :=
    (eff31.agrees.read (n := 64) (r := 13) (by simp [b114ea0Effect, Effect.components])).trans r13_in
  have r5_31 : t31.regValue .rbp = stackPtr s - 144 :=
    (eff31.agrees.read (n := 64) (r := 5) (by simp [b114ea0Effect, Effect.components])).trans r5_in
  have p272_31 := point_of_external p272_in mem31
  have p1040_31 := point_of_external p1040_in mem31
  have p144_31 := point_of_external p144_in mem31
  have p944_31 := point_of_external p944_in mem31
  have p1808_31 := point_of_external p1808_in mem31
  have p848_31 := point_of_external p848_in mem31
  have p752_31 := point_of_external p752_in mem31
  have p656_31 := point_of_external p656_in mem31
  have scalar31 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t31 = s.regValue .rsi := by
    change memLoad t31.external _ 64 = _
    rw [mem31]
    exact facts.scalar
  obtain ⟨t32, run32, st32, rip32, value32, eff32, _⟩ :=
    copy_stack (sourceOffset := 272) pre st31 0x263 (by decide) (by decide +kernel)
      eff31.rip 1808 (by decide) (by decide) r7_31 r1_31
      (by decide) (by decide) (by decide) r6_31 p272_31
  have p272_32 := copy_point (offset := 272) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_31
  have p1040_32 := copy_point (offset := 1040) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_31
  have p144_32 := copy_point (offset := 144) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_31
  have p944_32 := copy_point (offset := 944) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_31
  have p1808_32 := value32
  have p848_32 := copy_point (offset := 848) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_31
  have p752_32 := copy_point (offset := 752) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_31
  have p656_32 := copy_point (offset := 656) pre eff32 (by decide) (by decide)
    (by decide) (by decide) (by decide) p656_31
  have r3_32 : t32.regValue .rbx = s.regValue .rdi :=
    (eff32.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_31
  have r15_32 : t32.regValue .r15 = stackPtr s - 272 :=
    (eff32.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_31
  have r14_32 : t32.regValue .r14 = stackPtr s - 1808 :=
    (eff32.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_31
  have r12_32 : t32.regValue .r12 = stackPtr s - 848 :=
    (eff32.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_31
  have r13_32 : t32.regValue .r13 = stackPtr s - 752 :=
    (eff32.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_31
  have r5_32 : t32.regValue .rbp = stackPtr s - 144 :=
    (eff32.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_31
  have scalar32 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t32 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar31
    apply memLoad_congr
    intro i hi
    change ( t32.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t31.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff32 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n33, t33, run33, st33, eff33, mem33⟩ :=
    register_block (offset := 0x266) (bytes := b114eb6Bytes) (effect := b114eb6Effect) st32 (b114eb6_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip32
      (by simp [b114eb6Effect, Effect.components, Component.Covers])
      (by simp [b114eb6Effect, Effect.components])
      (by simp [b114eb6Effect, Effect.components])
      (by simp [b114eb6Effect, Effect.components])
      (by simp [b114eb6Effect, Effect.components])
  have r7_33 : t33.regValue .rdi = stackPtr s - 1808 := eff33.writes.1.trans r14_32
  have r6_33 : t33.regValue .rsi = stackPtr s - 144 := eff33.writes.2.trans r5_32
  have r3_33 : t33.regValue .rbx = s.regValue .rdi :=
    (eff33.agrees.read (n := 64) (r := 3) (by simp [b114eb6Effect, Effect.components])).trans r3_32
  have r15_33 : t33.regValue .r15 = stackPtr s - 272 :=
    (eff33.agrees.read (n := 64) (r := 15) (by simp [b114eb6Effect, Effect.components])).trans r15_32
  have r14_33 : t33.regValue .r14 = stackPtr s - 1808 :=
    (eff33.agrees.read (n := 64) (r := 14) (by simp [b114eb6Effect, Effect.components])).trans r14_32
  have r12_33 : t33.regValue .r12 = stackPtr s - 848 :=
    (eff33.agrees.read (n := 64) (r := 12) (by simp [b114eb6Effect, Effect.components])).trans r12_32
  have r13_33 : t33.regValue .r13 = stackPtr s - 752 :=
    (eff33.agrees.read (n := 64) (r := 13) (by simp [b114eb6Effect, Effect.components])).trans r13_32
  have r5_33 : t33.regValue .rbp = stackPtr s - 144 :=
    (eff33.agrees.read (n := 64) (r := 5) (by simp [b114eb6Effect, Effect.components])).trans r5_32
  have p272_33 := point_of_external p272_32 mem33
  have p1040_33 := point_of_external p1040_32 mem33
  have p144_33 := point_of_external p144_32 mem33
  have p944_33 := point_of_external p944_32 mem33
  have p1808_33 := point_of_external p1808_32 mem33
  have p848_33 := point_of_external p848_32 mem33
  have p752_33 := point_of_external p752_32 mem33
  have p656_33 := point_of_external p656_32 mem33
  have scalar33 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t33 = s.regValue .rsi := by
    change memLoad t33.external _ 64 = _
    rw [mem33]
    exact scalar32
  let site34 : P256.Proofs.Projective.Multiply.Machine.Loop.CallSite 0x1051f0 :=
    ⟨0x26c, 0x4f7f, by decide, by decide +kernel, by decide +kernel⟩
  obtain ⟨t34, result34⟩ := add_call (outputOffset := 1808) (sourceOffset := 144) pre st33
    site34 eff33.rip (by decide) (by decide) (by decide) (by decide) (by decide)
    r7_33 r6_33 p1808_33 p144_33
  obtain ⟨n34, run34⟩ := result34.execution
  have st34 := result34.toFrameState
  have p272_34 := call_point (offset := 272) result34 (by decide) (by decide) (by decide) p272_33
  have p1040_34 := call_point (offset := 1040) result34 (by decide) (by decide) (by decide) p1040_33
  have p144_34 := call_point (offset := 144) result34 (by decide) (by decide) (by decide) p144_33
  have p944_34 := call_point (offset := 944) result34 (by decide) (by decide) (by decide) p944_33
  have p1808_34 : ProjectiveAt t34 (stackPtr s - 1808) (Projective.tableEntry point 5) := result34.value
  have p848_34 := call_point (offset := 848) result34 (by decide) (by decide) (by decide) p848_33
  have p752_34 := call_point (offset := 752) result34 (by decide) (by decide) (by decide) p752_33
  have p656_34 := call_point (offset := 656) result34 (by decide) (by decide) (by decide) p656_33
  have r3_34 : t34.regValue .rbx = s.regValue .rdi :=
    (result34.registers .rbx (by simp)).trans r3_33
  have r15_34 : t34.regValue .r15 = stackPtr s - 272 :=
    (result34.registers .r15 (by simp)).trans r15_33
  have r14_34 : t34.regValue .r14 = stackPtr s - 1808 :=
    (result34.registers .r14 (by simp)).trans r14_33
  have r12_34 : t34.regValue .r12 = stackPtr s - 848 :=
    (result34.registers .r12 (by simp)).trans r12_33
  have r13_34 : t34.regValue .r13 = stackPtr s - 752 :=
    (result34.registers .r13 (by simp)).trans r13_33
  have r5_34 : t34.regValue .rbp = stackPtr s - 144 :=
    (result34.registers .rbp (by simp)).trans r5_33
  have scalar34 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t34 = s.regValue .rsi :=
    (result34.read (by decide) (by decide) (by decide)).trans scalar33
  obtain ⟨n35, t35, run35, st35, eff35, mem35⟩ :=
    register_block (offset := 0x271) (bytes := b114ec1Bytes) (effect := b114ec1Effect) st34 (b114ec1_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) result34.rip
      (by simp [b114ec1Effect, Effect.components, Component.Covers])
      (by simp [b114ec1Effect, Effect.components])
      (by simp [b114ec1Effect, Effect.components])
      (by simp [b114ec1Effect, Effect.components])
      (by simp [b114ec1Effect, Effect.components])
  have r1_35 : t35.regValue .rcx = 12 := eff35.writes.1
  have r7_35 : t35.regValue .rdi = stackPtr s - 144 := eff35.writes.2.1.trans r5_34
  have r6_35 : t35.regValue .rsi = stackPtr s - 1808 := eff35.writes.2.2.trans r14_34
  have r3_35 : t35.regValue .rbx = s.regValue .rdi :=
    (eff35.agrees.read (n := 64) (r := 3) (by simp [b114ec1Effect, Effect.components])).trans r3_34
  have r15_35 : t35.regValue .r15 = stackPtr s - 272 :=
    (eff35.agrees.read (n := 64) (r := 15) (by simp [b114ec1Effect, Effect.components])).trans r15_34
  have r14_35 : t35.regValue .r14 = stackPtr s - 1808 :=
    (eff35.agrees.read (n := 64) (r := 14) (by simp [b114ec1Effect, Effect.components])).trans r14_34
  have r12_35 : t35.regValue .r12 = stackPtr s - 848 :=
    (eff35.agrees.read (n := 64) (r := 12) (by simp [b114ec1Effect, Effect.components])).trans r12_34
  have r13_35 : t35.regValue .r13 = stackPtr s - 752 :=
    (eff35.agrees.read (n := 64) (r := 13) (by simp [b114ec1Effect, Effect.components])).trans r13_34
  have r5_35 : t35.regValue .rbp = stackPtr s - 144 :=
    (eff35.agrees.read (n := 64) (r := 5) (by simp [b114ec1Effect, Effect.components])).trans r5_34
  have p272_35 := point_of_external p272_34 mem35
  have p1040_35 := point_of_external p1040_34 mem35
  have p144_35 := point_of_external p144_34 mem35
  have p944_35 := point_of_external p944_34 mem35
  have p1808_35 := point_of_external p1808_34 mem35
  have p848_35 := point_of_external p848_34 mem35
  have p752_35 := point_of_external p752_34 mem35
  have p656_35 := point_of_external p656_34 mem35
  have scalar35 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t35 = s.regValue .rsi := by
    change memLoad t35.external _ 64 = _
    rw [mem35]
    exact scalar34
  obtain ⟨t36, run36, st36, rip36, value36, eff36, _⟩ :=
    copy_stack (sourceOffset := 1808) pre st35 0x27c (by decide) (by decide +kernel)
      eff35.rip 144 (by decide) (by decide) r7_35 r1_35
      (by decide) (by decide) (by decide) r6_35 p1808_35
  have p272_36 := copy_point (offset := 272) pre eff36 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_35
  have p1040_36 := copy_point (offset := 1040) pre eff36 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_35
  have p144_36 := value36
  have p944_36 := copy_point (offset := 944) pre eff36 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_35
  have p1808_36 := copy_point (offset := 1808) pre eff36 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_35
  have p848_36 := copy_point (offset := 848) pre eff36 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_35
  have p752_36 := copy_point (offset := 752) pre eff36 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_35
  have p656_36 := copy_point (offset := 656) pre eff36 (by decide) (by decide)
    (by decide) (by decide) (by decide) p656_35
  have r3_36 : t36.regValue .rbx = s.regValue .rdi :=
    (eff36.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_35
  have r15_36 : t36.regValue .r15 = stackPtr s - 272 :=
    (eff36.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_35
  have r14_36 : t36.regValue .r14 = stackPtr s - 1808 :=
    (eff36.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_35
  have r12_36 : t36.regValue .r12 = stackPtr s - 848 :=
    (eff36.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_35
  have r13_36 : t36.regValue .r13 = stackPtr s - 752 :=
    (eff36.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_35
  have r5_36 : t36.regValue .rbp = stackPtr s - 144 :=
    (eff36.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_35
  have scalar36 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t36 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar35
    apply memLoad_congr
    intro i hi
    change ( t36.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t35.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff36 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  obtain ⟨n37, t37, run37, st37, eff37, mem37⟩ :=
    register_block (offset := 0x27f) (bytes := b114ecfBytes) (effect := b114ecfEffect) st36 (b114ecf_correct boundary pre.outerBoundary)
      (by decide +kernel) (by decide +kernel) rip36
      (by simp [b114ecfEffect, Effect.components, Component.Covers])
      (by simp [b114ecfEffect, Effect.components])
      (by simp [b114ecfEffect, Effect.components])
      (by simp [b114ecfEffect, Effect.components])
      (by simp [b114ecfEffect, Effect.components])
  have r1_37 : t37.regValue .rcx = 12 := eff37.writes.1
  have r7_37 : t37.regValue .rdi = stackPtr s - 560 := by
    have h : t37.regValue .rdi = stackPtr t36 + 1496 := eff37.writes.2.1
    exact h.trans (scalar_stack_address st36.rsp (by decide) (by decide))
  have r6_37 : t37.regValue .rsi = stackPtr s - 144 := eff37.writes.2.2.trans r5_36
  have r3_37 : t37.regValue .rbx = s.regValue .rdi :=
    (eff37.agrees.read (n := 64) (r := 3) (by simp [b114ecfEffect, Effect.components])).trans r3_36
  have r15_37 : t37.regValue .r15 = stackPtr s - 272 :=
    (eff37.agrees.read (n := 64) (r := 15) (by simp [b114ecfEffect, Effect.components])).trans r15_36
  have r14_37 : t37.regValue .r14 = stackPtr s - 1808 :=
    (eff37.agrees.read (n := 64) (r := 14) (by simp [b114ecfEffect, Effect.components])).trans r14_36
  have r12_37 : t37.regValue .r12 = stackPtr s - 848 :=
    (eff37.agrees.read (n := 64) (r := 12) (by simp [b114ecfEffect, Effect.components])).trans r12_36
  have r13_37 : t37.regValue .r13 = stackPtr s - 752 :=
    (eff37.agrees.read (n := 64) (r := 13) (by simp [b114ecfEffect, Effect.components])).trans r13_36
  have r5_37 : t37.regValue .rbp = stackPtr s - 144 :=
    (eff37.agrees.read (n := 64) (r := 5) (by simp [b114ecfEffect, Effect.components])).trans r5_36
  have p272_37 := point_of_external p272_36 mem37
  have p1040_37 := point_of_external p1040_36 mem37
  have p144_37 := point_of_external p144_36 mem37
  have p944_37 := point_of_external p944_36 mem37
  have p1808_37 := point_of_external p1808_36 mem37
  have p848_37 := point_of_external p848_36 mem37
  have p752_37 := point_of_external p752_36 mem37
  have p656_37 := point_of_external p656_36 mem37
  have scalar37 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t37 = s.regValue .rsi := by
    change memLoad t37.external _ 64 = _
    rw [mem37]
    exact scalar36
  obtain ⟨t38, run38, st38, rip38, value38, eff38, _⟩ :=
    copy_stack (sourceOffset := 144) pre st37 0x28f (by decide) (by decide +kernel)
      eff37.rip 560 (by decide) (by decide) r7_37 r1_37
      (by decide) (by decide) (by decide) r6_37 p144_37
  have p272_38 := copy_point (offset := 272) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p272_37
  have p1040_38 := copy_point (offset := 1040) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1040_37
  have p144_38 := copy_point (offset := 144) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p144_37
  have p944_38 := copy_point (offset := 944) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p944_37
  have p1808_38 := copy_point (offset := 1808) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p1808_37
  have p848_38 := copy_point (offset := 848) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p848_37
  have p752_38 := copy_point (offset := 752) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p752_37
  have p656_38 := copy_point (offset := 656) pre eff38 (by decide) (by decide)
    (by decide) (by decide) (by decide) p656_37
  have p560_38 := value38
  have r3_38 : t38.regValue .rbx = s.regValue .rdi :=
    (eff38.read (n := 64) (r := 3) (by simp [copyComponents])).trans r3_37
  have r15_38 : t38.regValue .r15 = stackPtr s - 272 :=
    (eff38.read (n := 64) (r := 15) (by simp [copyComponents])).trans r15_37
  have r14_38 : t38.regValue .r14 = stackPtr s - 1808 :=
    (eff38.read (n := 64) (r := 14) (by simp [copyComponents])).trans r14_37
  have r12_38 : t38.regValue .r12 = stackPtr s - 848 :=
    (eff38.read (n := 64) (r := 12) (by simp [copyComponents])).trans r12_37
  have r13_38 : t38.regValue .r13 = stackPtr s - 752 :=
    (eff38.read (n := 64) (r := 13) (by simp [copyComponents])).trans r13_37
  have r5_38 : t38.regValue .rbp = stackPtr s - 144 :=
    (eff38.read (n := 64) (r := 5) (by simp [copyComponents])).trans r5_37
  have scalar38 : (Operand.mem (stackPtr s - 2048) : Operand 64).read t38 = s.regValue .rsi := by
    apply Eq.trans ?_ scalar37
    apply memLoad_congr
    intro i hi
    change ( t38.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0 =
      (t37.external[stackPtr s - 2048 + BitVec.ofNat 64 i]?).getD 0
    exact congrArg (fun value : Option UInt8 => value.getD 0) (copy_byte (offset := 2048) (len := 8) pre eff38 (by decide) (by decide)
      (by decide) (by decide) (by decide) hi)
  exact ⟨n31 + 12 + n33 + n34 + n35 + 12 + n37 + 12, t38, (((((((run31.trans run32).trans run33).trans run34).trans run35).trans run36).trans run37).trans run38), st38, rip38,
    ⟨r3_38, r15_38, r14_38, r12_38, r13_38, r5_38, trivial⟩,
    ⟨p272_38, p1040_38, p144_38, p944_38, p1808_38, p848_38, p752_38, p656_38, p560_38, trivial⟩, scalar38⟩

end P256.Proofs.Ecdh.Table
