import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Store
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.BitOps.Extensions
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Rounds.Register.Or
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Copied.Md5.Proofs.Block Base16ct.Proofs.Copied.Md5.Proofs.Block.Rounds.Register

def tailCounterEffect (s : RamState) : Effect where
  rip := 0x1002e6
  writes := [
    ⟨(.reg 0 : Operand 64), (Operand.reg 0 : Operand 64).read s + 1⟩,
    ⟨(.reg 3 : Operand 64),
      (((Operand.reg 3 : Operand 64).read s).extractLsb' 8 8).setWidth 64⟩,
    ⟨(.reg 6 : Operand 64),
      ((Operand.reg 6 : Operand 32).read s |||
        (((Operand.reg 3 : Operand 64).read s).extractLsb' 8 8).setWidth 32).setWidth 64⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 9 : Operand 64).read s)
    ((Operand.reg 0 : Operand 64).read s + 1)))

theorem tail_counter [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1002db)
      (codeRange 0x1002db [0x48, 0xff, 0xc0, 0x0f, 0xb6, 0xdf, 0x09, 0xde,
        0x49, 0x39, 0xc1]) tailCounterEffect := by
  intro s hReady hCode hRip
  obtain ⟨a, hRunA, hReadyA, eA⟩ :=
    (inc_r64_effect_step 0x1002db 0x48 0xc0
      (by unfold RexWPrefix; decide) (by decide) (by decide)).advances hReady
      (hCode.mono (codeRange_mem_of_take (by decide +kernel))) hRip
      (outsideMixed_ne (pc := 0x1002de) hOutside (by decide) (by decide))
  change (incR64Effect 0x1002db 0 s).Holds s a at eA
  have cA := eA.codeIn (incR64Effect_avoids _ _ _ _) hCode
  obtain ⟨b, hRunB, hReadyB, eB⟩ := (movzx_ebx_bh_effect_step 0x1002de).advances hReadyA
    (cA.mono (codeRange_mem_of_drop (p := 0x1002db) 3 (by decide +kernel))) eA.rip
    (outsideMixed_ne (pc := 0x1002e1) hOutside (by decide) (by decide))
  have cB := eB.codeIn (movzxEbxBhEffect_avoids _ _ _) cA
  obtain ⟨c, hRunC, hReadyC, eC⟩ := (or_r32_r32_effect_step 0x1002e1 0xde (by decide)).advances
    hReadyB (cB.mono (codeRange_mem_of_drop (p := 0x1002db) 6 (by decide +kernel))) eB.rip
    (outsideMixed_ne (pc := 0x1002e3) hOutside (by decide) (by decide))
  change (orR32R32Effect 0x1002e1 2 6 3 b).Holds b c at eC
  have cC := eC.codeIn (orR32R32Effect_avoids _ _ _ _ _ _) cB
  obtain ⟨t, hRunT, hReadyT, eT⟩ :=
    (cmp_r64_r64_effect_step 0x1002e3 0x49 0xc1
      (by unfold RexWPrefix; decide) (by decide)).advances hReadyC
      (cC.mono (codeRange_mem_of_drop (p := 0x1002db) 8 (by decide +kernel))) eC.rip
      (outsideMixed_ne (pc := 0x1002e6) hOutside (by decide) (by decide))
  change (cmpR64R64Effect 0x1002e3 9 0 c).Holds c t at eT
  have hIndexA : (Operand.reg 0 : Operand 64).read a =
      (Operand.reg 0 : Operand 64).read s + 1 := eA.writes
  have hRbxA : (Operand.reg 3 : Operand 64).read a =
      (Operand.reg 3 : Operand 64).read s := eA.agrees.read (by simp)
  have hRbxB : (Operand.reg 3 : Operand 64).read b =
      (((Operand.reg 3 : Operand 64).read s).extractLsb' 8 8).setWidth 64 := by
    simpa only [movzxEbxBhEffect, Write.AllHold, hRbxA] using eB.writes
  have hRbxB32 : (Operand.reg 3 : Operand 32).read b =
      (((Operand.reg 3 : Operand 64).read s).extractLsb' 8 8).setWidth 32 := by
    change ((Operand.reg 3 : Operand 64).read b).setWidth 32 = _
    rw [hRbxB, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
  have hRsiB : (Operand.reg 6 : Operand 32).read b =
      (Operand.reg 6 : Operand 32).read s :=
    (eA.agrees.trans eB.agrees).read (by simp [movzxEbxBhEffect_components])
  have hRsiC : (Operand.reg 6 : Operand 64).read c =
      ((Operand.reg 6 : Operand 32).read s |||
        (((Operand.reg 3 : Operand 64).read s).extractLsb' 8 8).setWidth 32).setWidth 64 := by
    simpa only [orR32R32Effect, Write.AllHold, hRsiB, hRbxB32] using eC.writes
  have hR9C : (Operand.reg 9 : Operand 64).read c = (Operand.reg 9 : Operand 64).read s :=
    ((eA.agrees.trans eB.agrees).trans eC.agrees).read (by
      simp [movzxEbxBhEffect_components, orR32R32Effect_components])
  have hRaxC : (Operand.reg 0 : Operand 64).read c = (Operand.reg 0 : Operand 64).read s + 1 :=
    ((eB.agrees.trans eC.agrees).read (by
      simp [movzxEbxBhEffect_components, orR32R32Effect_components])).trans hIndexA
  refine ⟨4, t, ((hRunA.trans hRunB).trans hRunC).trans hRunT, hReadyT,
    eT.codeIn (cmpR64R64Effect_avoids _ _ _ _ _) cC, eT.rip, ?_, ?_, ?_⟩
  · refine ⟨(eT.agrees.read (by simp)).trans hRaxC, ?_,
      (eT.agrees.read (by simp)).trans hRsiC⟩
    exact ((eC.agrees.trans eT.agrees).read (by
      simp [orR32R32Effect_components])).trans hRbxB
  · simpa only [Effect.FlagsHold, tailCounterEffect, cmpR64R64Effect, hR9C, hRaxC] using eT.flags
  · exact (((eA.agrees.trans eB.agrees).trans eC.agrees).trans eT.agrees).mono (by
      change ∀ c : Component, c ∈ ([.reg 0, .flags, .rip] ++ [.reg 3, .rip] ++
        [.reg 6, .flags, .rip] ++ [.flags, .rip]) →
        c ∈ [.reg 0, .reg 3, .reg 6, .flags, .rip]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      intro c hc
      rcases hc with (((rfl | rfl | rfl) | (rfl | rfl)) |
        (rfl | rfl | rfl)) | (rfl | rfl) <;> simp)


theorem tail_registers [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002db) (hOutside : OutsideMixed boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      t.RIP = (if s.regValue .r9 = s.regValue .rax + 1 then 0x1002ec else 0x1001f0) ∧
      t.regValue .rax = s.regValue .rax + 1 ∧
      t.regValue .rsi = ((s.regValue .rsi).setWidth 32 |||
        ((s.regValue .rbx).extractLsb' 8 8).setWidth 32).setWidth 64 ∧
      AgreesExcept [.reg 6, .reg 3, .reg 0, .flags, .rip] s t := by
  have hb : CodeIn (codeRange 0x1002db [0x48, 0xff, 0xc0, 0x0f, 0xb6, 0xdf, 0x09, 0xde,
      0x49, 0x39, 0xc1]) s := program_text_slice hCode 0x2db 11 (by decide +kernel)
  obtain ⟨fuel, u, hRun, hReady', _, hEffect⟩ := tail_counter boundary hOutside s hReady hb hRip
  have hCode' := hEffect.agrees.codeIn (by simp [tailCounterEffect, Effect.components,
    Component.Covers]) hCode
  have hIndex : u.regValue .rax = s.regValue .rax + 1 := hEffect.writes.1
  have hAccumulator : u.regValue .rsi = ((s.regValue .rsi).setWidth 32 |||
      ((s.regValue .rbx).extractLsb' 8 8).setWidth 32).setWidth 64 := hEffect.writes.2.2
  have hZero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (s.regValue .r9 == s.regValue .rax + 1) := by
    have hz := hEffect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((s.regValue .r9 - (s.regValue .rax + 1)) == 0) at hz
    rw [hz]
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.sub_eq_iff_eq_add]
  have hNext : (jccEffect 0x1002e6 6 5 ((0xffffff04#32).signExtend 64) u).rip =
      (if s.regValue .r9 = s.regValue .rax + 1 then 0x1002ec else 0x1001f0) := by
    simp [jccEffect, branchEffect, condHolds, hZero, branchTarget]
  have hNextNe : (jccEffect 0x1002e6 6 5 ((0xffffff04#32).signExtend 64) u).rip ≠
      boundary.rip := by
    rw [hNext]
    split <;> exact outsideMixed_ne hOutside (by decide) (by decide)
  obtain ⟨t, hBranch, hReady'', hBranchEffect⟩ :=
    (jcc_rel32_effect_step 0x1002e6 5 0xffffff04).advances hReady'
      (program_text_slice hCode' 0x2e6 6 (by decide +kernel))
      ⟨hEffect.rip, fun _ ↦ by decide +kernel⟩ hNextNe
  have hBranchFrame : AgreesExcept [.rip] u t := hBranchEffect.agrees
  refine ⟨fuel + 1, t, hRun.trans hBranch, hReady'',
    hBranchFrame.codeIn (by simp [Component.Covers]) hCode',
    hBranchEffect.rip.trans hNext,
    (hBranchFrame.read (r := 0) (n := 64) (by simp)).trans hIndex,
    (hBranchFrame.read (r := 6) (n := 64) (by simp)).trans hAccumulator, ?_⟩
  exact (hEffect.agrees.trans hBranchFrame).mono (by simp [tailCounterEffect, Effect.components])

theorem tail_advances [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002d8)
    (hWritable : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (s.regValue .rcx + s.regValue .rax) 1)
    (hAvoid : ¬ InProgram (s.regValue .rcx + s.regValue .rax))
    (hOutside : OutsideMixed boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      t.RIP = (if s.regValue .r9 = s.regValue .rax + 1 then 0x1002ec else 0x1001f0) ∧
      t.regValue .rax = s.regValue .rax + 1 ∧
      t.regValue .rsi = ((s.regValue .rsi).setWidth 32 |||
        ((s.regValue .rbx).extractLsb' 8 8).setWidth 32).setWidth 64 ∧
      t.external[s.regValue .rcx + s.regValue .rax]? =
        some (UInt8.ofNat ((s.regValue .rbx).setWidth 8).toNat) ∧
      AgreesExcept [.reg 6, .reg 3, .reg 0, .flags, .rip,
        .mem (s.regValue .rcx + s.regValue .rax) 1] s t := by
  obtain ⟨u, hStore, hReady', hCode', hRip', hByte, hStoreFrame⟩ :=
    output_store hReady hCode hRip hWritable hAvoid hOutside
  obtain ⟨fuel, t, hRun, hReady'', hCode'', hRip'', hIndex, hAccumulator, hFrame⟩ :=
    tail_registers hReady' hCode' hRip' hOutside
  have hRead (r : BitVec 5) : (Operand.reg r : Operand 64).read u =
      (Operand.reg r : Operand 64).read s := hStoreFrame.read (by simp)
  have ha : u.regValue .r9 = s.regValue .r9 := hRead 9
  have hi : u.regValue .rax = s.regValue .rax := hRead 0
  have hc : u.regValue .rsi = s.regValue .rsi := hRead 6
  have hb : u.regValue .rbx = s.regValue .rbx := hRead 3
  rw [ha, hi] at hRip''
  rw [hi] at hIndex
  rw [hc, hb] at hAccumulator
  refine ⟨1 + fuel, t, hStore.trans hRun, hReady'', hCode'', hRip'', hIndex,
    hAccumulator, (hFrame.byte (by simp [Component.Covers])).trans hByte, ?_⟩
  exact (hStoreFrame.trans hFrame).mono (by simp)

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
