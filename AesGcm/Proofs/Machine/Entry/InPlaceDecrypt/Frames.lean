import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Guards

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 400000 in
theorem core_saved_outside (use256 : Bool) (rsp destination : BitVec 64)
    (sealedSize : Nat) (core : Activation)
    (hroom : (if use256 then 3504 else 2848) ≤ rsp.toNat)
    (hlow : rsp.toNat + 8 ≤ 2^32) (hlarge : 16 ≤ sealedSize)
    (hsp : core.rsp = rsp - (if use256 then 592 else 464))
    (hcore : core.low.toNat ≤ core.rsp.toNat)
    (hapart : (span destination sealedSize).Disjoint
      (span (rsp - (if use256 then 3504 else 2848))
        ((if use256 then 3504 else 2848) + 8))) :
    Outside [core.region, span destination (sealedSize - 16),
      span (rsp - (if use256 then 584 else 456) + 24) 8]
      (rsp - 48) 56 := by
  have hs : (rsp - (48 : BitVec 64)).toNat = rsp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · change 48 ≤ rsp.toNat
      split at hroom <;> omega
  have hcs : core.rsp.toNat = rsp.toNat - (if use256 then 592 else 464) := by
    rw [hsp, BitVec.toNat_sub_of_le]
    · cases use256 <;> rfl
    · cases use256
      · exact Nat.le_trans (by decide : 464 ≤ 2848) hroom
      · exact Nat.le_trans (by decide : 592 ≤ 3504) hroom
  have hd : (rsp - (if use256 then 584 else 456) + (24 : BitVec 64)).toNat =
      rsp.toNat - (if use256 then 584 else 456) + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le]
    · cases use256
      all_goals
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat] at hroom ⊢
        exact Nat.mod_eq_of_lt (by omega)
    · cases use256
      · exact Nat.le_trans (by decide : 456 ≤ 2848) hroom
      · exact Nat.le_trans (by decide : 584 ≤ 3504) hroom
  have hw : (rsp - (if use256 then 3504 else 2848)).toNat =
      rsp.toNat - (if use256 then 3504 else 2848) := by
    rw [BitVec.toNat_sub_of_le]
    · cases use256 <;> rfl
    · cases use256 <;> exact hroom
  have hp := disjoint_bounds destination.toNat sealedSize
    (rsp - (if use256 then 3504 else 2848)).toNat
    ((if use256 then 3504 else 2848) + 8) (by omega)
    (by cases use256 <;> decide) hapart
  rw [hw] at hp
  refine ⟨by rw [hs]; omega, ?_⟩
  intro region hregion
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hregion
  rcases hregion with rfl | rfl | rfl
  · simp only [Activation.region]
    rw [hs, hcs]
    rw [hcs] at hcore
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hroom hcore ⊢ <;> omega
  · simp only [span]
    rw [hs]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hroom hp ⊢ <;> omega
  · simp only [span]
    rw [hs, hd]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hroom ⊢ <;> omega

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
