import AesGcm.Proofs.Machine.CTR.KeyLoop
import AesGcm.Proofs.Machine.KeySchedule.Memory

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice
open AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.AES

theorem round_bounds (use256 : Bool) (mem : Ram) (sp : BitVec 64)
    (hstack : Readable mem (sp - 296) 528)
    (hkeys : Readable mem (sp + 344) (if use256 then 960 else 704)) :
    296 ≤ sp.toNat ∧
      sp.toNat + 344 + (if use256 then 960 else 704) ≤ 2 ^ 32 := by
  have hlow := hstack.low
  have hadd (base : BitVec 64) (n : Nat) (h : base.toNat + n < 2 ^ 64) :
      (base + BitVec.ofNat 64 n).toNat = base.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]
  have hsp := hadd (sp - 296) 296 (by omega)
  rw [show sp - 296 + BitVec.ofNat 64 296 = sp by bv_omega] at hsp
  have hkeysLow := hkeys.low
  have haddr : (sp + 344).toNat = sp.toNat + 344 := hadd sp 344 (by omega)
  rw [haddr] at hkeysLow
  exact ⟨by omega, hkeysLow⟩

theorem round_key_slice
    (use256 : Bool) (mem : Ram) (sp : BitVec 64)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (hSchedule : ∀ i : Fin (keyWords use256), scheduleWords[i.val] =
      (narrowScheduleWords (AES16.variant use256) key)[i.val]'(by cases use256 <;> exact i.isLt))
    (hread : Readable mem (sp + 344) (if use256 then 960 else 704))
    (hkeys : WordsAt mem (sp + 344) 64
      (scheduleWords.map Fixslice16.widenWord))
    (r : Fin ((AES16.variant use256).Nr + 1)) :
    Readable mem (sp + 344 + BitVec.ofNat 64 (64 * r.val)) 64 ∧
      WordsAt mem (sp + 344 + BitVec.ofNat 64 (64 * r.val)) 64
        (Vector.ofFn (KeySchedule.expectedKey (AES16.variant use256) key r)) := by
  have hr := r.isLt
  constructor
  · apply hread.of_offsets rfl (addr_self (sp + 344))
    simp only [sub_zero_lit, BitVec.toNat_ofNat]
    have hm := Nat.mod_le (64 * r.val) (2 ^ 64)
    have hlen : (if use256 then 960 else 704) = 64 * ((AES16.variant use256).Nr + 1) := by
      cases use256 <;> rfl
    rw [hlen]
    omega
  · have hw : WordsAt mem (sp + 344) 64
        ((narrowScheduleWords (AES16.variant use256) key).map Fixslice16.widenWord) := by
      intro i hi
      have hi' : i < keyWords use256 := by cases use256 <;> exact hi
      simpa only [Vector.getElem_map, hSchedule ⟨i, hi'⟩] using hkeys i hi'
    intro i hi
    simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn, BitVec.add_assoc,
      ← BitVec.ofNat_add] using widenedScheduleWords_in hw r ⟨i, hi⟩

end AesGcm.Proofs.Machine.CTR.Loop
