import ChaCha20Poly1305.Proofs.Wrapper
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix
open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper MemoryRoutines.Machine

def claimChanges : List Component :=
  [.rip, .reg 0, .reg 1, .reg 2, .reg 7, .flags, .mem 0x300000 8]

set_option maxHeartbeats 1000000 in
 theorem reserve_claim [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (T0 : GTrack claimChanges s s)
    (rip : s.RIP = 0x1017be) {heap size limit : BitVec 64}
    (rbp : rd s 5 = size) (cursor : wd s 0x300000 = heap) (bound : wd s 0x300008 = limit)
    (readCursor : MemReadable s 0x300000 8) (readLimit : MemReadable s 0x300008 8)
    (writeCursor : MemWritable s 0x300000 8)
    (avoid : ∀ x, (Component.mem 0x300000 8).Covers x → ¬ InProgram x)
    (overflow : heap.toNat + size.toNat < 2^64)
    (capacity : (heap + size).toNat ≤ limit.toNat) (nonzero : heap ≠ 0) :
    ∃ t, Advances boundary 11 s t ∧ GTrack claimChanges s t ∧
      t.RIP = 0x1017f6 ∧ rd t 7 = heap := by
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x1017be 0x48 (by unfold RexWPrefix; decide) 7 (.rip 0x1fe83b) (by decide) (by decide) (by decide)) T0
    (program_text_slice T0.code 0x17be 7 (by decide +kernel))
    (⟨rip, readCursor⟩) (code_ne_boundary outside 0x17c5 (by omega))
    (by fits [claimChanges, addR64R64Effect_components])
  change (movR64M64Effect 0x1017be 7 (.rip 0x1fe83b) s).Holds s u1 at e1
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x1017c5 0x48 0xf9 (by unfold RexWPrefix; decide) (by decide)) T1
    (program_text_slice T1.code 0x17c5 3 (by decide +kernel))
    (e1.rip) (code_ne_boundary outside 0x17c8 (by omega))
    (by fits [claimChanges, addR64R64Effect_components])
  change (movR64R64Effect 0x1017c5 1 7 u1).Holds u1 u2 at e2
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_r32_imm32_effect_step 0x1017c8 0xb8 (by decide) 1) T2
    (program_text_slice T2.code 0x17c8 5 (by decide +kernel))
    (e2.rip) (code_ne_boundary outside 0x17cd (by omega))
    (by fits [claimChanges, addR64R64Effect_components])
  change (movR32Imm32Effect 0x1017c8 5 0 1 u2).Holds u2 u3 at e3
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (add_r64_r64_effect_step 0x1017cd 0x48 0xe9 (by unfold RexWPrefix; decide) (by decide)) T3
    (program_text_slice T3.code 0x17cd 3 (by decide +kernel))
    (e3.rip) (code_ne_boundary outside 0x17d0 (by omega))
    (by fits [claimChanges, addR64R64Effect_components])
  change (addR64R64Effect 0x1017cd 1 5 u3).Holds u3 u4 at e4
  have v1 : rd u1 7 = heap := e1.writes.trans cursor
  have v3 : rd u3 1 = heap := by
    change (Operand.reg 1 : Operand 64).read u3 = heap
    rw [e3.agrees.read (by simp), e2.writes]
    exact v1
  have b3 : rd u3 5 = size := by
    change (Operand.reg 5 : Operand 64).read u3 = size
    rw [((e1.agrees.trans e2.agrees).trans e3.agrees).read (by simp)]
    exact rbp
  have cf4 : condHolds 2 (StatusFlags.ofRFLAGS u4.RFLAGS) = false := by
    have hf := e4.flags
    simp only [Effect.FlagsHold, addR64R64Effect] at hf
    rw [condHolds_2, hf.1]
    change decide ((rd u3 1 + rd u3 5).toNat ≠ (rd u3 1).toNat + (rd u3 5).toNat) = false
    rw [v3, b3]
    simp only [BitVec.toNat_add, Nat.mod_eq_of_lt overflow, ne_eq, not_true_eq_false, decide_false]
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step
    (jcc_rel32_effect_step 0x1017d0 2 0x14a) T4
    (program_text_slice T4.code 0x17d0 6 (by decide +kernel))
    ⟨e4.rip, by intro; decide⟩
    (by simp only [jccEffect, branchEffect, cf4, Bool.false_eq_true, ↓reduceIte];
        exact code_ne_boundary outside 0x17d6 (by omega))
    (by fits [claimChanges])
  have rip5 : u5.RIP = 0x1017d6 := (jccEffect_not_taken cf4 e5).rip
  have pre6 : MemReadable u5 0x300008 8 := by
    exact ⟨readLimit.low, fun i hi => T5.agrees.grow _ (readLimit.mem i hi)⟩
  obtain ⟨u6, a6, T6, e6⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x1017d6 0x48 (by unfold RexWPrefix; decide) 2
      (.rip 0x1fe82b) (by decide) (by decide) (by decide)) T5
    (program_text_slice T5.code 0x17d6 7 (by decide +kernel))
    ⟨rip5, pre6⟩ (code_ne_boundary outside 0x17dd (by omega)) (by fits [claimChanges])
  change (movR64M64Effect 0x1017d6 2 (.rip 0x1fe82b) u5).Holds u5 u6 at e6
  have v6 : rd u6 2 = limit := by
    have keep : wd u5 0x300008 = wd s 0x300008 := by
      apply gload T5.agrees
      intro c hc i hi
      simp only [claimChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact fun h => h
      rintro ⟨j, hj, he⟩
      change 0x300008#64 + BitVec.ofNat 64 i = 0x300000#64 + BitVec.ofNat 64 j at he
      have hn := congrArg BitVec.toNat he
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
      omega
    exact e6.writes.trans (keep.trans bound)
  have v6c : rd u6 1 = heap + size := by
    change (Operand.reg 1 : Operand 64).read u6 = heap + size
    rw [(e5.agrees.trans e6.agrees).read (by simp [jccEffect]), e4.writes]
    change rd u3 1 + rd u3 5 = heap + size
    rw [v3, b3]
  obtain ⟨u7, a7, T7, e7⟩ := gtrack_step
    (cmp_r64_r64_effect_step 0x1017dd 0x48 0xd1 (by unfold RexWPrefix; decide) (by decide)) T6
    (program_text_slice T6.code 0x17dd 3 (by decide +kernel))
    e6.rip (code_ne_boundary outside 0x17e0 (by omega)) (by fits [claimChanges])
  change (cmpR64R64Effect 0x1017dd 1 2 u6).Holds u6 u7 at e7
  have cf7 : condHolds 7 (StatusFlags.ofRFLAGS u7.RFLAGS) = false := by
    have hf := e7.flags
    simp only [Effect.FlagsHold, cmpR64R64Effect] at hf
    rw [condHolds_7, hf.1, hf.2.2.2.1]
    rw [cmpSpec_ZF]
    change (!(decide ((rd u6 1).toNat < (rd u6 2).toNat) || (rd u6 1 == rd u6 2))) = false
    rw [v6c, v6]
    by_cases hh : heap + size = limit
    · simp [hh]
    · have hlt : (heap + size).toNat < limit.toNat := by
        have hne : (heap + size).toNat ≠ limit.toNat := fun h => hh (BitVec.eq_of_toNat_eq h)
        omega
      simp only [hlt, decide_true, Bool.true_or, Bool.not_true]
  obtain ⟨u8, a8, T8, e8⟩ := gtrack_step
    (jcc_rel32_effect_step 0x1017e0 7 0x13a) T7
    (program_text_slice T7.code 0x17e0 6 (by decide +kernel))
    ⟨e7.rip, by intro; decide⟩
    (by simp only [jccEffect, branchEffect, cf7, Bool.false_eq_true, ↓reduceIte];
        exact code_ne_boundary outside 0x17e6 (by omega)) (by fits [claimChanges])
  have rip8 : u8.RIP = 0x1017e6 := (jccEffect_not_taken cf7 e8).rip
  obtain ⟨u9, a9, T9, e9⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x1017e6 0x48 (by unfold RexWPrefix; decide) 1
      (.rip 0x1fe813) (by decide) (by decide) (by decide)) T8
    (program_text_slice T8.code 0x17e6 7 (by decide +kernel))
    ⟨rip8, ⟨writeCursor.low, fun i hi => T8.agrees.grow _ (writeCursor.mem i hi), writeCursor.tables⟩,
      by change RangeApart 0x300000 8 0x1017e6 7
         exact RangeApart.of_toNat (by decide) (by decide) (Or.inr (by decide))⟩
    (code_ne_boundary outside 0x17ed (by omega))
    (by
      fits [claimChanges, AddrMode.addr, storeAddrAt]
      exact .inr ⟨rfl, fun x hx => ⟨⟨.mem 0x300000 8, by simp, hx⟩,
        avoid x hx⟩⟩)
  change (movM64R64Effect 0x1017e6 1 (.rip 0x1fe813) u8).Holds u8 u9 at e9
  have v9 : rd u9 7 = heap := by
    change (Operand.reg 7 : Operand 64).read u9 = heap
    rw [(((((((e2.agrees.trans e3.agrees).trans e4.agrees).trans e5.agrees).trans
      e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).read
        (by simp [jccEffect])]
    exact v1
  obtain ⟨u10, a10, T10, e10⟩ := gtrack_step
    (test_r64_r64_effect_step 0x1017ed 0x48 0xff (by unfold RexWPrefix; decide) (by decide)) T9
    (program_text_slice T9.code 0x17ed 3 (by decide +kernel))
    e9.rip (code_ne_boundary outside 0x17f0 (by omega))
    (by fits [claimChanges, testR64R64Effect_components])
  change (testR64R64Effect 0x1017ed 7 7 u9).Holds u9 u10 at e10
  have cf10 : condHolds 4 (StatusFlags.ofRFLAGS u10.RFLAGS) = false := by
    have hf := e10.flags
    simp only [Effect.FlagsHold, testR64R64Effect, testFlags] at hf
    rw [condHolds_4, hf.2.2.2.1]
    change (rd u9 7 &&& rd u9 7 == 0) = false
    rw [v9]
    simp only [BitVec.and_self, beq_eq_false_iff_ne]
    exact nonzero
  obtain ⟨u11, a11, T11, e11⟩ := gtrack_step
    (jcc_rel32_effect_step 0x1017f0 4 0x12a) T10
    (program_text_slice T10.code 0x17f0 6 (by decide +kernel))
    ⟨e10.rip, by intro; decide⟩
    (by simp only [jccEffect, branchEffect, cf10, Bool.false_eq_true, ↓reduceIte];
        exact code_ne_boundary outside 0x17f6 (by omega)) (by fits [claimChanges])
  refine ⟨u11, ?_, T11, (jccEffect_not_taken cf10 e11).rip, ?_⟩
  · exact a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans
      (a8.trans (a9.trans (a10.trans a11)))))))))
  · change (Operand.reg 7 : Operand 64).read u11 = heap
    rw [(e10.agrees.trans e11.agrees).read (by simp [jccEffect])]
    exact v9

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
