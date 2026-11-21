import Sha2.Proofs.FIPS180.SHA512

namespace Sha2.Proofs.FIPS180
namespace SHA512Bridge
open Standards.NIST.SHA2
open Sha2.Proofs.Common.SHA512

theorem bitsToWord_extract (input : Array Bool) (start w : Nat) (h : start + w ≤ input.size) :
    BitVec.ofNat w (NIST.Encoding.bitsToNat (input.extract start (start+w))) =
      bitsToWord (Vector.ofFn fun i : Fin w => input[start+i.val]'(by omega)) := by
  have heq : input.extract start (start+w) =
      (Vector.ofFn fun i : Fin w => input[start+i.val]'(by omega)).toArray := by
    apply Array.ext
    · simp only [Array.size_extract, Nat.min_eq_left h, Vector.size_toArray]
      omega
    · intro i hi hi'
      simp only [Array.getElem_extract, Vector.getElem_toArray, Vector.getElem_ofFn]
  rw [heq, bitsToNat_eq_bitsToWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem initialSchedule_parse (input : Array Bool) (i : Nat) (hi : i < input.size / 1024)
    (j : Nat) (hj : j < 16) :
    (initialSchedule (input.extract (1024*i) (1024*(i+1))))[j]!.toBitVec =
      ((Standards.NIST.SHA2.SHA512.parse input)[i]'(by simpa [Standards.NIST.SHA2.SHA512.parse] using hi))[j] := by
  have hi' : 1024*(i+1) ≤ input.size := by omega
  have hj' : 64*(j+1) ≤ 1024 := by omega
  have hmin : min (1024*i+64*(j+1)) (1024*(i+1)) = 1024*i+64*(j+1) := by omega
  rw [getElem!_pos (initialSchedule (input.extract (1024*i) (1024*(i+1)))) j
    (by simpa only [initialSchedule_size] using hj)]
  simp only [initialSchedule, Array.getElem_map,
    Array.getElem_range, UInt64.toBitVec_ofNat', Array.extract_extract, hmin]
  rw [show 1024*i+64*(j+1) = (1024*i+64*j)+64 by omega,
    bitsToWord_extract input (1024*i+64*j) 64 (by omega)]
  simp [Standards.NIST.SHA2.SHA512.parse, Nat.add_assoc]

end SHA512Bridge
end Sha2.Proofs.FIPS180
