import X86Proofs.Instructions.Add.Operation
import Sha2.Proofs.Wrapper512.Absorb.Arithmetic

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large

open X86Proofs

theorem count_high_add (count added : Nat) (bound : added < 2^64) :
    BitVec.ofNat 64 (count / 2^64) +
      (if (addSpec (BitVec.ofNat 64 count) (BitVec.ofNat 64 added)).2.CF then 1 else 0) =
      BitVec.ofNat 64 ((count + added) / 2^64) := by
  have rem : count % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
  have splitCount : count = 2^64 * (count / 2^64) + count % 2^64 := by omega
  have divSum : (count + added) / 2^64 = count / 2^64 + (count % 2^64 + added) / 2^64 := by omega
  have flag : (addSpec (BitVec.ofNat 64 count) (BitVec.ofNat 64 added)).2.CF =
      decide (2^64 ≤ count % 2^64 + added) := by
    simp only [addSpec, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [flag, divSum]
  by_cases carry : 2^64 ≤ count % 2^64 + added
  · have quotient : (count % 2^64 + added) / 2^64 = 1 := by omega
    simp only [carry, decide_true, ite_true, quotient, BitVec.ofNat_add]
    rfl
  · have quotient : (count % 2^64 + added) / 2^64 = 0 := by omega
    simp only [carry, decide_false, Bool.false_eq_true, ite_false, quotient, Nat.add_zero]
    exact BitVec.add_zero _

end Sha2.Proofs.Wrapper512.Absorb.Large
