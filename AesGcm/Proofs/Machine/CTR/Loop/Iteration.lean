import AesGcm.Proofs.Machine.CTR.BatchFull
import AesGcm.Proofs.Machine.CTR.Loop.HeaderStep
import AesGcm.Proofs.Machine.CTR.Loop.Key1Step
import AesGcm.Proofs.Machine.CTR.Loop.Key3Step
import AesGcm.Proofs.Machine.CTR.Loop.SboxStep
import AesGcm.Proofs.Machine.CTR.Loop.Inline2Step
import AesGcm.Proofs.Machine.CTR.Loop.Inline0Step
import AesGcm.Proofs.Machine.CTR.Loop.MixStep
import AesGcm.Proofs.Machine.CTR.Loop.Algebra
import AesGcm.Proofs.Machine.CTR.Loop.RoundKey

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice
open AesGcm.Proofs.Machine.AESCore
open AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.AES

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem batch_cipher_step
    (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Fixslice.Blocks) (sp : BitVec 64)
    (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hSchedule : ∀ i : Fin (keyWords use256), scheduleWords[i.val] =
      (narrowScheduleWords (AES16.variant use256) key)[i.val]'(by cases use256 <;> exact i.isLt))
    (_hBlocks : WordsAt mem (sp + 8) 64 (Vector.ofFn (Fixslice.encode blocks)))
    (j : Nat) (hj : 4 * j < (AES16.variant use256).Nr + 1)
    (hjlast : j ≤ batchLastIteration use256)
    (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp scheduleWords loc)
    (hloop : CipherLoopState use256 key blocks fr sp j hj loc) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp scheduleWords next ∧
      ((j = batchLastIteration use256 ∧
          CipherFinalState use256 key blocks fr sp next) ∨
        (j < batchLastIteration use256 ∧
          ∃ hnext : 4 * (j + 1) < (AES16.variant use256).Nr + 1,
            CipherLoopState use256 key blocks fr sp (j + 1) hnext next)) := by
  let n := (AES16.variant use256).Nr
  have hfirst : 4 * j + 1 < n := by
    cases use256 <;> simp only [batchLastIteration, n, AES16.variant, Variant.Nr, Bool.false_eq_true,
        ↓reduceIte] at hjlast ⊢ <;> omega
  let index := BitVec.ofNat 64 (32 * j + (if use256 then 8 else 0))
  let addr (k : Nat) := sp + (index <<< 3) +
    (if use256 then BitVec.ofNat 64 (280 + 64 * k) else BitVec.ofNat 64 (344 + 64 * k))
  let keyAt (k : Nat) (hk : 4 * j + k ≤ n) :=
    KeySchedule.expectedKey (AES16.variant use256) key ⟨4 * j + k, by omega⟩
  have haddr (k : Nat) : addr k = sp + 344 + BitVec.ofNat 64 (64 * (4 * j + k)) := by
    dsimp only [addr, index]
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change sp + (BitVec.ofNat 64 _ * BitVec.ofNat 64 8) + _ = _
    rw [← BitVec.ofNat_mul]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc]
    all_goals
      apply congrArg (sp + ·)
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 _ =
        BitVec.ofNat 64 344 + BitVec.ofNat 64 _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      omega
  have slice (s : LIR.lifted.Location)
      (hw : CipherWorkingState use256 code fr args mem sp scheduleWords s)
      (k : Nat) (hk : 4 * j + k ≤ n) :
      Readable s.store (addr k) 64 ∧
        WordsAt s.store (addr k) 64 (Vector.ofFn (keyAt k hk)) := by
    rw [haddr]
    exact round_key_slice use256 s.store sp key scheduleWords hSchedule hw.keyRead hw.keys
      ⟨4 * j + k, by omega⟩
  obtain ⟨hlo, hhi⟩ := round_bounds use256 loc.store sp hwork.stack.readable hwork.keyRead
  have hnr : n ≤ 14 := by cases use256 <;> decide
  have hnat (a : BitVec 64) (k : Nat) (h : a.toNat + k < 2 ^ 64) :
      (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt h]
  have h344 : (sp + 344).toNat = sp.toNat + 344 := hnat sp 344 (by omega)
  have haddrNat (k : Nat) (hk : 4 * j + k ≤ n) :
      (addr k).toNat = sp.toNat + 344 + 64 * (4 * j + k) := by
    rw [haddr, hnat _ _ (by omega), h344]
  have hleft : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
  have hright : (sp + 8).toNat = sp.toNat + 8 := by bv_omega
  let planes := batchDelayedPlanes use256 key blocks (4 * j)
  let state := batchRoundState use256 key blocks (4 * j)
  have hrestore : (fun p : Fin 8 ↦ if p.val = 7 then planes 7 ^^^ keyAt 0 (by omega) 7
      else planes p) = state := by
    have hm : min (4 * j) (AES16.variant use256).Nr = 4 * j := Nat.min_eq_left (by omega)
    simpa only [planes, batchDelayedPlanes,
      hm, ctrDelayedPlanes, Nat.add_zero, state, keyAt] using
      restore_batchDelayed state (keyAt 0 (by omega))
  have htailAddr : sp + (index <<< 3) + (if use256 then 336 else 400) = addr 0 + 56 := by
    cases use256 <;> simp only [addr, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc] <;> rfl
  obtain ⟨hread0, hkeys0⟩ := slice loc hwork 0 (by omega)
  have hreadTail : Readable loc.store (addr 0 + 56) 8 :=
    hread0.of_offsets rfl (addr_self (addr 0)) (by decide)
  have htailKey : memLoad loc.store (addr 0 + 56) 64 = keyAt 0 (by omega) 7 :=
    hkeys0 7 (by decide)
  obtain ⟨s1, hr1, hw1, hl1, hp1, hb1, hkeep1⟩ :=
    header_step use256 code hcode fr args mem sp scheduleWords index (planes 7)
      (keyAt 0 (by omega) 7) planes loc hwork hloop.label hloop.index hloop.tail
      (htailAddr ▸ hreadTail) (htailAddr ▸ htailKey) hloop.words
  rw [hrestore] at hp1
  obtain ⟨s2, hr2, hw2, hl2, hp2, hkeep2⟩ :=
    mix_step use256 false code hcode fr args mem sp scheduleWords (Fixslice.subBytes state)
      s1 hw1 hl1 (congrArg (Value.get 64) hb1) hp1
  obtain ⟨hread1, hkeys1⟩ := slice s2 hw2 1 (by omega)
  have hi2 := (hkeep2 5 (by decide)).trans ((hkeep1 5 (by decide)).trans hloop.index)
  let p1 := xorPlanes (mixColumns1 (Fixslice.subBytes state)) (keyAt 1 (by omega))
  obtain ⟨s3, hr3, hw3, hl3, hp3, hkeep3, hregs⟩ :=
    key1_step use256 code hcode fr args mem sp scheduleWords index
      (mixColumns1 (Fixslice.subBytes state)) (keyAt 1 (by omega)) s2 hw2 hl2 hi2
      hread1 (Or.inl (show (sp + 8).toNat + 64 ≤ (addr 1).toNat by
        rw [haddrNat 1 (by omega), hright]; omega)) hp2 hkeys1
  have hr := hr1.trans (hr2.trans hr3)
  by_cases hlast : j = batchLastIteration use256
  · have heq : 4 * j + 1 = n - 1 := by subst j; cases use256 <;> rfl
    have hi : index = (if use256 then 104 else 64) := by
      subst j
      cases use256 <;> rfl
    have hm : (4 * j + 1) % 4 = 1 := by omega
    have he : p1 = batchRoundState use256 key blocks (n - 1) := by
      rw [← heq]
      simpa only [p1, batchRoundMix, hm, keyAt, state] using
        batchRoundState_step use256 key blocks (4 * j) hfirst
    change WordsAt s3.store (sp + 8) 64 (Vector.ofFn p1) at hp3
    change ∀ p : Fin 8, _ = p1 p at hregs
    rw [he] at hp3 hregs
    exact ⟨s3, hr, hw3, Or.inl ⟨hlast, ⟨by simpa only [hi, ite_true] using hl3, hp3, hregs⟩⟩⟩
  · have hlt : j < batchLastIteration use256 := by omega
    have hround : 4 * (j + 1) < n := by
      cases use256 <;> simp only [batchLastIteration, n, AES16.variant, Variant.Nr,
        Bool.false_eq_true, ↓reduceIte] at hlt ⊢ <;> omega
    have hi : index ≠ (if use256 then 104 else 64) := by
      intro he
      have h := congrArg BitVec.toNat he
      cases use256
      · change j < 2 at hlt
        change (32 * j + 0) % (2 ^ 64) = 64 at h
        rw [Nat.mod_eq_of_lt (by omega)] at h
        omega
      · change j < 3 at hlt
        change (32 * j + 8) % (2 ^ 64) = 104 at h
        rw [Nat.mod_eq_of_lt (by omega)] at h
        omega
    obtain ⟨s4, hr4, hw4, hl4, hp4, hkeep4⟩ :=
      sbox_step use256 code hcode fr args mem sp scheduleWords p1 s3 hw3
        (by simpa only [hi, ite_false] using hl3) hp3
    have hi4 := (hkeep4 5 (by decide)).trans ((hkeep3 5 (by decide)).trans hi2)
    obtain ⟨hread2, hkeys2⟩ := slice s4 hw4 2 (by omega)
    obtain ⟨s5, hr5, hw5, hl5, hp5, hb5, hkeep5⟩ :=
      inline2_step use256 code hcode fr args mem sp scheduleWords index (Fixslice.subBytes p1)
        (keyAt 2 (by omega)) s4 hw4 hl4 hi4 hread2
        (Or.inl (show (sp - 8).toNat + 160 ≤ (addr 2).toNat by
          rw [haddrNat 2 (by omega), hleft]; omega)) hp4 hkeys2
    let p2 := xorPlanes (mixColumns2 (Fixslice.subBytes p1)) (keyAt 2 (by omega))
    obtain ⟨s6, hr6, hw6, hl6, hp6, hkeep6⟩ :=
      mix_step use256 true code hcode fr args mem sp scheduleWords (Fixslice.subBytes p2)
        s5 hw5 hl5 (congrArg (Value.get 64) hb5) hp5
    have hi6 := (hkeep6 5 (by decide)).trans ((hkeep5 5 (by decide)).trans hi4)
    have hb6 := (hkeep6 3 (by decide)).trans hb5
    obtain ⟨hread3, hkeys3⟩ := slice s6 hw6 3 (by omega)
    obtain ⟨s7, hr7, hw7, hl7, hp7, hkeep7⟩ :=
      key3_step use256 code hcode fr args mem sp scheduleWords index
        (mixColumns3 (Fixslice.subBytes p2)) (keyAt 3 (by omega)) s6 hw6 hl6 hi6 hb6
        hread3 (Or.inl (show (sp - 8).toNat + 80 ≤ (addr 3).toNat by
          rw [haddrNat 3 (by omega), hleft]; omega)) hp6 hkeys3
    let p3 := xorPlanes (mixColumns3 (Fixslice.subBytes p2)) (keyAt 3 (by omega))
    have hi7 := (hkeep7 5 (by decide)).trans hi6
    obtain ⟨hread4, hkeys4⟩ := slice s7 hw7 4 (by omega)
    obtain ⟨s8, hr8, hw8, hl8, hp8, ht8, _, hi8⟩ :=
      inline0_step use256 code hcode fr args mem sp scheduleWords index (Fixslice.subBytes p3)
        (keyAt 4 (by omega)) s7 hw7 hl7 hi7 hread4
        (Or.inl (show (sp + 8).toNat + (if use256 then 128 else 64) ≤ (addr 4).toNat by
          rw [haddrNat 4 (by omega), hright]
          split <;> omega)) hp7 hkeys4
    have hfinish := batch_iteration use256 key blocks j hround
    have h4 : 4 * (j + 1) = 4 * j + 4 := by omega
    dsimp only at hfinish
    simp only [h4] at hfinish
    change (fun p : Fin 8 ↦ if p.val = 7 then mixColumns0 (Fixslice.subBytes p3) p
      else mixColumns0 (Fixslice.subBytes p3) p ^^^ keyAt 4 (by omega) p) =
      batchDelayedPlanes use256 key blocks (4 * j + 4) at hfinish
    refine ⟨s8, hr.trans (hr4.trans (hr5.trans (hr6.trans (hr7.trans hr8)))), hw8,
      Or.inr ⟨hlt, by omega, ⟨hl8, ?_, ?_, ?_⟩⟩⟩
    · rw [hi8]
      change Value.mk 64 (BitVec.ofNat 64 _ + BitVec.ofNat 64 32) = _
      rw [← BitVec.ofNat_add]
      congr 2
      omega
    · rw [h4, ← hfinish]
      exact hp8
    · apply ht8.trans
      rw [h4]
      exact congrFun hfinish 7

end AesGcm.Proofs.Machine.CTR.Loop
