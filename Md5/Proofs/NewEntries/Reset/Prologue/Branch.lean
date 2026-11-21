import Md5.Proofs.Streaming.Prologue

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Block Md5.Proofs.Streaming

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read BitVec.sub_eq_add_neg jmpEffect branchTarget decR64Effect incR64Effect

private theorem mergeGPR8_setWidth (value : BitVec 8) (old : BitVec 64) :
    (mergeGPR 8 value old).setWidth 8 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, decide_true, Bool.true_and,
    mergeGPR, show ¬ (8 : Nat) = 32 from by decide, ite_false,
    getLsbD_setSlice old 0 8 value i (by omega), Nat.zero_le, Nat.zero_add,
    hi, and_self, ite_true, Nat.sub_zero]

private theorem mergeGPR8_overwrite (a b : BitVec 8) (old : BitVec 64) :
    mergeGPR 8 a (mergeGPR 8 b old) = mergeGPR 8 a old := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mergeGPR, show ¬ (8 : Nat) = 32 from by decide, ite_false]
  rw [getLsbD_setSlice _ 0 8 a i hi, getLsbD_setSlice _ 0 8 a i hi,
    getLsbD_setSlice old 0 8 b i hi]
  split <;> rfl

attribute [local x86_compose] mergeGPR8_setWidth mergeGPR8_overwrite

def resetDispatchPrefixEffect (first count : BitVec 64) (s : RamState) : Effect :=
  let a : BitVec 8 := if first = 0 then 1 else 0
  let b : BitVec 8 := if count = 0 then 1 else 0
  { rip := 0x1013a0
    writes := [⟨(.reg 0 : Operand 64), mergeGPR 8 a ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), mergeGPR 8 (b ||| a) ((Operand.reg 1 : Operand 64).read s)⟩]
    flags := some (andFlags (b ||| a)) }

theorem reset_dispatch_prefix [Bindings] (first count : BitVec 64)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x101392 ∧ (Operand.reg 1 : Operand 64).read s = first ∧
        (Operand.reg 6 : Operand 64).read s = count)
      (codeRange 0x101392 [0x48, 0x85, 0xc9, 0x0f, 0x94, 0xc0, 0x48,
        0x85, 0xf6, 0x0f, 0x94, 0xc1, 0x08, 0xc1])
      (resetDispatchPrefixEffect first count) := by
  have hTestA := test_r64_r64_effect_step 0x101392 0x48 0xc9
    (by unfold RexWPrefix; decide) (by decide)
  change StepEffect _ _ (testR64R64Effect 0x101392 1 1) at hTestA
  have hTestB := test_r64_r64_effect_step 0x101398 0x48 0xf6
    (by unfold RexWPrefix; decide) (by decide)
  change StepEffect _ _ (testR64R64Effect 0x101398 6 6) at hTestB
  md5_run_begin hTestA
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1395 (by decide +kernel)
  md5_run_then (sete_al_fixed_effect_step 0x101395 (decide (first = 0)))
  case sub => exact codeRange_mem_of_drop (p := 0x101392) 3 (by decide +kernel)
  case mid =>
    intro s t h hE _
    refine ⟨⟨hE.rip, ?_⟩, setzR8FixedEffect_avoids _ _ _ _ _⟩
    simpa only [Effect.flag, testR64R64Effect, testFlags, StatusFlagsOutcome.get,
      StatusFlags.get, FlagAllows, BitVec.and_self, Bool.beq_eq_decide_eq, h.2.1]
      using hE.flag .ZF
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1398 (by decide +kernel)
  md5_run_then hTestB
  case sub => exact codeRange_mem_of_drop (p := 0x101392) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x139b (by decide +kernel)
  md5_run_then (sete_cl_fixed_effect_step 0x10139b (decide (count = 0)))
  case sub => exact codeRange_mem_of_drop (p := 0x101392) 9 (by decide +kernel)
  case mid =>
    intro s t h hE _
    refine ⟨⟨hE.rip, ?_⟩, setzR8FixedEffect_avoids _ _ _ _ _⟩
    have hz := hE.flag .ZF
    x86_norm [Effect.flag, testFlags, StatusFlagsOutcome.get, StatusFlags.get, FlagAllows,
      BitVec.and_self, Bool.beq_eq_decide_eq, h.2.2] at hz
    exact hz
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x139e (by decide +kernel)
  md5_run_then (or_cl_al_effect_step 0x10139e)
  case sub => exact codeRange_mem_of_drop (p := 0x101392) 12 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13a0 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t h hE
  apply hE.weaken
  · x86_norm [resetDispatchPrefixEffect, decide_eq_true_iff]
  · x86_norm [resetDispatchPrefixEffect, decide_eq_true_iff]
  · intro i; cases i <;> x86_norm [resetDispatchPrefixEffect, decide_eq_true_iff]
  · x86_norm [resetDispatchPrefixEffect, decide_eq_true_iff]

def resetCountEffect (s : RamState) : Effect where
  rip := 0x1013a5
  writes := [⟨(.mem (stackPtr s + 8) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩]

theorem reset_count_effect_step [Bindings] :
    StepEffect (Memory.StorePre 0x1013a0 5 (fun s ↦ stackPtr s + 8) 8)
      (codeRange 0x1013a0 [0x48, 0x89, 0x74, 0x24, 8]) resetCountEffect := by
  exact Buffered.Stores.mov_m64_r64_effect_step 0x1013a0 0x48
    (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 8))
    (by decide) (by decide) (by decide)

def resetClampPrefixEffect (s : RamState) : Effect where
  rip := 0x1013b5
  writes := [⟨(.reg 12 : Operand 64), (Operand.reg 12 : Operand 64).read s - 1⟩,
    ⟨(.reg 0 : Operand 64), (Operand.reg 6 : Operand 64).read s - 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 12 : Operand 64).read s - 1)
    ((Operand.reg 6 : Operand 64).read s - 1)))

theorem reset_clamp_prefix [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1013ab)
      (codeRange 0x1013ab [0x49, 0xff, 0xcc, 0x48, 0x8d, 0x46, 0xff,
        0x49, 0x39, 0xc4]) resetClampPrefixEffect := by
  have hFirst := dec_r64_effect_step 0x1013ab 0x49 0xcc
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (decR64Effect 0x1013ab 12) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13ae (by decide +kernel)
  md5_run_then (lea_r64_effect_step 0x1013ae 0x48
    (by unfold RexWPrefix; decide) 0 (.base 6 (.d8 (-1)))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1013ab) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13b2 (by decide +kernel)
  md5_run_then (cmp_r64_r64_effect_step 0x1013b2 0x49 0xc4
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1013ab) 7 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13b5 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetClampPrefixEffect, decR64Effect]
  · x86_norm [resetClampPrefixEffect, decR64Effect]
  · intro i; cases i <;> x86_norm [resetClampPrefixEffect, decR64Effect]
  · x86_norm [resetClampPrefixEffect, decR64Effect]

def resetClampSuffixEffect (s : RamState) : Effect where
  rip := 0x1013f8
  writes := [⟨(.reg 12 : Operand 64), (Operand.reg 12 : Operand 64).read s + 1⟩,
    ⟨(.reg 15 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem reset_clamp_suffix [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1013b9)
      (codeRange 0x1013b9 [0x49, 0xff, 0xc4, 0x45, 0x31, 0xff, 0xeb, 0x37])
      resetClampSuffixEffect := by
  have hFirst := inc_r64_effect_step 0x1013b9 0x49 0xc4
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (incR64Effect 0x1013b9 12) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13bc (by decide +kernel)
  md5_run_then (xor_r32_r32_rex_effect_step 0x1013bc 0x45 0xff
    (by unfold RexNoWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1013b9) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13bf (by decide +kernel)
  md5_run_then (jmp_rel8_effect_step 0x1013bf 0x37 (by decide +kernel))
  case mid => intro s t _ hE _; exact ⟨hE.rip, jmpEffect_avoids _ _ _ _⟩
  case sub => exact codeRange_mem_of_drop (p := 0x1013b9) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13f8 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetClampSuffixEffect]
  · x86_norm [resetClampSuffixEffect]
    change (0 : BitVec 64) = (((Operand.reg 15 : Operand 32).read s) ^^^
      (Operand.reg 15 : Operand 32).read s).setWidth 64
    simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat]
  · intro i; cases i <;> x86_norm [resetClampSuffixEffect]
  · x86_norm [resetClampSuffixEffect]

theorem reset_clamp_branch [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1013ab) (hOutside : ¬ InProgram boundary.rip)
    (hFirst : (Operand.reg 12 : Operand 64).read s ≠ 0)
    (hCount : (Operand.reg 6 : Operand 64).read s ≠ 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x1013f8 ∧
      (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64
        (min ((Operand.reg 12 : Operand 64).read s).toNat
          ((Operand.reg 6 : Operand 64).read s).toNat) ∧
      (Operand.reg 15 : Operand 64).read t = 0 ∧
      AgreesExcept [.reg 0, .reg 12, .reg 15, .flags, .rip] s t := by
  obtain ⟨n, u, hPrefix, hu, _, hEPrefix⟩ :=
    reset_clamp_prefix boundary hOutside s hReady
      (program_text_slice hCode 0x13ab 10 (by decide +kernel)) hRip
  have hCodeU := hEPrefix.codeIn (Effect.Avoids.of_noMem (by
    simp [resetClampPrefixEffect, Effect.components, Component.Covers]) _) hCode
  obtain ⟨v, hMove, hv, hEMove⟩ :=
    (cmovae_r64_r64_effect_step 0x1013b5 0x4c 0xe0 (by unfold RexWPrefix; decide) (by decide)).advances hu
      (program_text_slice hCodeU 0x13b5 4 (by decide +kernel)) hEPrefix.rip
      (text_address_ne_return hOutside 0x13b9 (by decide +kernel))
  change (cmovaeR64R64Effect 0x1013b5 12 0 u).Holds u v at hEMove
  have hCodeV := hEMove.codeIn (Effect.Avoids.of_noMem (by
    simp [cmovaeR64R64Effect, Effect.components, Component.Covers]) _) hCodeU
  obtain ⟨m, t, hSuffix, ht, _, hESuffix⟩ :=
    reset_clamp_suffix boundary hOutside v hv
      (program_text_slice hCodeV 0x13b9 8 (by decide +kernel)) hEMove.rip
  have hW := hEPrefix.writes
  change (Operand.reg 12 : Operand 64).read u = (Operand.reg 12 : Operand 64).read s - 1 ∧
    (Operand.reg 0 : Operand 64).read u = (Operand.reg 6 : Operand 64).read s - 1 at hW
  have hCF : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      (cmpSpec ((Operand.reg 12 : Operand 64).read s - 1)
        ((Operand.reg 6 : Operand 64).read s - 1)).CF := by
    simpa only [Effect.flag, resetClampPrefixEffect, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, FlagAllows] using hEPrefix.flag .CF
  have hBP := hEMove.writes
  change (Operand.reg 12 : Operand 64).read v =
    if !(StatusFlags.ofRFLAGS u.RFLAGS).CF then (Operand.reg 0 : Operand 64).read u
    else (Operand.reg 12 : Operand 64).read u at hBP
  rw [hCF, hW.1, hW.2] at hBP
  have hWSuffix := hESuffix.writes
  change (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read v + 1 ∧
    (Operand.reg 15 : Operand 64).read t = 0 at hWSuffix
  refine ⟨n + 1 + m, t, (hPrefix.trans hMove).trans hSuffix, ht,
    hESuffix.codeIn (Effect.Avoids.of_noMem (by
      simp [resetClampSuffixEffect, Effect.components, Component.Covers]) _) hCodeV,
    hESuffix.rip, ?_, hWSuffix.2, ?_⟩
  · rw [hWSuffix.1, hBP]
    exact reset_clamp_value _ _ hFirst hCount
  · exact ((hEPrefix.agrees.trans hEMove.agrees).trans hESuffix.agrees).mono (by
      simp [resetClampPrefixEffect, cmovaeR64R64Effect, resetClampSuffixEffect, Effect.components])


def resetEmptyEffect (_ : RamState) : Effect where
  rip := 0x1014e0
  writes := [⟨(.reg 12 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem reset_empty_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1014c2)
      (codeRange 0x1014c2 [0x45, 0x31, 0xe4, 0xeb, 0x19])
      resetEmptyEffect := by
  md5_run_begin (xor_r32_r32_rex_effect_step 0x1014c2 0x45 0xe4
    (by unfold RexNoWPrefix; decide) (by decide))
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14c5 (by decide +kernel)
  md5_run_then (jmp_rel8_effect_step 0x1014c5 0x19 (by decide +kernel))
  case mid => intro s t _ hE _; exact ⟨hE.rip, jmpEffect_avoids _ _ _ _⟩
  case sub => exact codeRange_mem_of_drop (p := 0x1014c2) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14e0 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetEmptyEffect]
  · x86_norm [resetEmptyEffect]
    change (0 : BitVec 64) = (((Operand.reg 12 : Operand 32).read s) ^^^
      (Operand.reg 12 : Operand 32).read s).setWidth 64
    simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat]
  · intro i; cases i <;> x86_norm [resetEmptyEffect]
  · x86_norm [resetEmptyEffect]

theorem reset_branch [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (first count : BitVec 64)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x101392) (hOutside : ¬ InProgram boundary.rip)
    (hFirst : (Operand.reg 1 : Operand 64).read s = first)
    (hBound : (Operand.reg 12 : Operand 64).read s = first)
    (hCount : (Operand.reg 6 : Operand 64).read s = count)
    (hWrite : Memory.MemWritable s (stackPtr s + 8) 8)
    (hAvoid : ∀ x ∈ Extracted.programImage,
      ¬ (Component.mem (stackPtr s + 8) 8).Covers x.1) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      t.RIP = (if first = 0 ∨ count = 0 then 0x1014e0 else 0x1013f8) ∧
      (Operand.reg 12 : Operand 64).read t =
        BitVec.ofNat 64 (min first.toNat count.toNat) ∧
      (¬ (first = 0 ∨ count = 0) → (Operand.reg 15 : Operand 64).read t = 0) ∧
      (Operand.mem (stackPtr t + 8) : Operand 64).read t = count ∧
      AgreesExcept [.reg 0, .reg 1, .reg 12, .reg 15, .flags,
        .mem (stackPtr s + 8) 8, .rip] s t := by
  obtain ⟨n, u, hPrefix, hu, _, hEPrefix⟩ :=
    reset_dispatch_prefix first count boundary hOutside s hReady
      (program_text_slice hCode 0x1392 14 (by decide +kernel)) ⟨hRip, hFirst, hCount⟩
  have hCodeU := hEPrefix.codeIn (Effect.Avoids.of_noMem (by
    simp [resetDispatchPrefixEffect, Effect.components, Component.Covers]) _) hCode
  have hRspU : stackPtr u = stackPtr s := hEPrefix.agrees.read (n := 64) (r := 4) (by
    simp [resetDispatchPrefixEffect, Effect.components])
  have hWriteU : Memory.MemWritable u (stackPtr u + 8) 8 := by
    rw [hRspU]
    exact hWrite.of_holds hEPrefix
  have hApart : RangeApart (stackPtr u + 8) 8 0x1013a0 5 := by
    rw [hRspU]
    intro i hi j hj he
    exact hAvoid _ (prologue_text_sub 0x13a0 5 (by decide +kernel) _
      (mem_codeRange 0x1013a0 [0x48, 0x89, 0x74, 0x24, 8] j hj)) ⟨i, hi, he.symm⟩
  obtain ⟨v, hStore, hv, hEStore⟩ := reset_count_effect_step.advances hu
    (program_text_slice hCodeU 0x13a0 5 (by decide +kernel))
    ⟨hEPrefix.rip, hWriteU, hApart⟩
    (text_address_ne_return hOutside 0x13a5 (by decide +kernel))
  have hCodeV := hEStore.codeIn (by
    intro x hx c hc hcov
    have hc' : c = .mem (stackPtr u + 8) 8 ∨ c = .rip := by
      simpa [resetCountEffect, Effect.components] using hc
    rcases hc' with rfl | rfl
    · exact hAvoid x hx (by simpa only [hRspU] using hcov)
    · exact hcov) hCodeU
  have hStoreAgrees : AgreesExcept [.mem (stackPtr s + 8) 8, .rip] u v := by
    simpa [resetCountEffect, Effect.components, hRspU] using hEStore.agrees
  have hZFV : (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      decide (¬ (first = 0 ∨ count = 0)) := by
    have ha := hEPrefix.flag .ZF
    have hb := hEStore.flag .ZF
    simp only [Effect.flag, resetDispatchPrefixEffect, andFlags,
      StatusFlagsOutcome.get, StatusFlags.get, FlagAllows] at ha
    simp only [Effect.flag, resetCountEffect,
      StatusFlags.get, FlagAllows] at hb
    exact hb.trans (ha.trans (reset_dispatch_zero_value first count))
  obtain ⟨w, hJump, hw, hEJump⟩ :=
    (jcc_rel32_effect_step 0x1013a5 5 0x117).advances hv
      (program_text_slice hCodeV 0x13a5 6 (by decide +kernel))
      ⟨hEStore.rip, fun _ ↦ by decide +kernel⟩ (by
        change (if !(StatusFlags.ofRFLAGS v.RFLAGS).ZF then 0x1014c2 else 0x1013ab) ≠ boundary.rip
        split
        · exact text_address_ne_return hOutside 0x14c2 (by decide +kernel)
        · exact text_address_ne_return hOutside 0x13ab (by decide +kernel))
  have hCodeW := hEJump.codeIn (branchEffect_avoids _ _ _ _) hCodeV
  have hJumpAgrees : AgreesExcept [.rip] v w := hEJump.agrees
  have hRipW : w.RIP = if first = 0 ∨ count = 0 then 0x1014c2 else 0x1013ab := by
    have hr := hEJump.rip
    change w.RIP = if !(StatusFlags.ofRFLAGS v.RFLAGS).ZF then 0x1014c2 else 0x1013ab at hr
    rw [hZFV] at hr
    simpa only [decide_not, Bool.not_not, decide_eq_true_iff] using hr
  have hPreAgrees : AgreesExcept [.reg 0, .reg 1, .flags,
      .mem (stackPtr s + 8) 8, .rip] s w :=
    ((hEPrefix.agrees.trans hStoreAgrees).trans hJumpAgrees).mono (by
      simp [resetDispatchPrefixEffect, Effect.components])
  have hBoundW : (Operand.reg 12 : Operand 64).read w = first :=
    (hPreAgrees.read (by simp)).trans hBound
  have hCountW : (Operand.reg 6 : Operand 64).read w = count :=
    (hPreAgrees.read (by simp)).trans hCount
  obtain ⟨m, t, hTail, ht, hCodeT, hRipT, hBoundT, hIndexT, hTailAgrees⟩ :
      ∃ m t, Advances boundary m w t ∧ ReadyToStep t ∧
        CodeIn Extracted.programImage t ∧
        t.RIP = (if first = 0 ∨ count = 0 then 0x1014e0 else 0x1013f8) ∧
        (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (min first.toNat count.toNat) ∧
        (¬ (first = 0 ∨ count = 0) → (Operand.reg 15 : Operand 64).read t = 0) ∧
        AgreesExcept [.reg 0, .reg 12, .reg 15, .flags, .rip] w t := by
    by_cases hEmpty : first = 0 ∨ count = 0
    · obtain ⟨m, t, hTail, ht, _, hETail⟩ := reset_empty_branch boundary hOutside w hw
        (program_text_slice hCodeW 0x14c2 5 (by decide +kernel))
        (by simpa only [hEmpty, ite_true] using hRipW)
      refine ⟨m, t, hTail, ht, hETail.codeIn (Effect.Avoids.of_noMem (by
        simp [resetEmptyEffect, Effect.components, Component.Covers]) _) hCodeW,
        ?_, ?_, fun h ↦ False.elim (h hEmpty), hETail.agrees.mono (by
          simp [resetEmptyEffect, Effect.components])⟩
      · simpa only [hEmpty, ite_true, resetEmptyEffect] using hETail.rip
      · have hW : (Operand.reg 12 : Operand 64).read t = 0 := hETail.writes
        rcases hEmpty with hf | hc
        · simpa [hf] using hW
        · simpa [hc] using hW
    · obtain ⟨m, t, hTail, ht, hCodeT, hRipT, hBoundT, hIndexT, hAgrees⟩ :=
        reset_clamp_branch boundary hw hCodeW
          (by simpa only [hEmpty, ite_false] using hRipW) hOutside
          (by rw [hBoundW]; exact fun h ↦ hEmpty (.inl h))
          (by rw [hCountW]; exact fun h ↦ hEmpty (.inr h))
      refine ⟨m, t, hTail, ht, hCodeT, ?_, ?_, fun _ ↦ hIndexT, hAgrees⟩
      · simpa only [hEmpty, ite_false] using hRipT
      · simpa only [hBoundW, hCountW] using hBoundT
  have hTailMemory : t.external = v.external :=
    (hJumpAgrees.trans hTailAgrees).external (by simp [Component.Covers])
  have hRspT : stackPtr t = stackPtr u :=
    ((hStoreAgrees.trans hJumpAgrees).trans hTailAgrees).read (n := 64) (r := 4) (by simp)
  have hStored : (Operand.mem (stackPtr u + 8) : Operand 64).read v =
      (Operand.reg 6 : Operand 64).read u := hEStore.writes
  have hCountU : (Operand.reg 6 : Operand 64).read u = count :=
    (hEPrefix.agrees.read (by simp [resetDispatchPrefixEffect, Effect.components])).trans hCount
  refine ⟨n + 1 + 1 + m, t, ((hPrefix.trans hStore).trans hJump).trans hTail,
    ht, hCodeT, hRipT, hBoundT, hIndexT, ?_, ?_⟩
  · rw [hRspT]
    simpa only [Operand.read, hTailMemory] using hStored.trans hCountU
  · exact (hPreAgrees.trans hTailAgrees).mono (by simp)

end Md5.Proofs.NewEntries.Reset
