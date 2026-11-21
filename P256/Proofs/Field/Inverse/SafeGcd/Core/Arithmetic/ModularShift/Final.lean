import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Quotient
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Support

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic

open X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Schoolbook (packFour packFive)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open ModularShift
open P256.Proofs.Field.Inverse.SafeGcd

def finalDifference (p : Inputs) : Limbs :=
  ⟨v1b184f p, (v1b188c p).1, (v1b18c3 p).1, (v1b18fd p).1⟩

theorem final_difference_eq (p : Inputs) :
    P256.Proofs.Field.Subtract.subRaw (quotientLow p) (limbs p.modulus) =
      (finalDifference p, v1b1915 p) := by
  simp only [P256.Proofs.Field.Subtract.subRaw,
    P256.Proofs.Field.Subtract.subWord,
    P256.Proofs.Field.Subtract.borrow,
    quotientLow, finalDifference, v1b184f, v1b1855, v1b185b, v1b185e,
    v1b1861, v1b1864, v1b1867, v1b1878, v1b1885, v1b1888, v1b188c,
    v1b1892, v1b1898, v1b189b, v1b189e, v1b18a1, v1b18a4,
    v1b18af, v1b18bc, v1b18bf, v1b18c3, v1b18c9, v1b18cf,
    v1b18d2, v1b18d5, v1b18d8, v1b18db, v1b18e6, v1b18f6,
    v1b18f9, v1b18fd, v1b1903, v1b1909, v1b190c, v1b190f, v1b1912, v1b1915,
    addSpec, BitVec.reduceSetWidth, BitVec.zero_sub]

theorem final_borrow_one (p : Inputs) (hbound : (quotientLow p).toNat < (limbs p.modulus).toNat) :
    v1b1915 p = 1 := by
  have h := P256.Proofs.Field.Subtract.subRaw_toNat
    (quotientLow p) (limbs p.modulus)
  rw [final_difference_eq] at h
  dsimp only at h
  have hn : (v1b1915 p).toNat = 1 := by omega
  exact BitVec.eq_of_toNat_eq hn

theorem resultWords_eq (p : Inputs) (hbound : (quotientLow p).toNat < (limbs p.modulus).toNat)
    (hhigh : quotientHigh p = 0) :
    resultWords p = words (quotientLow p) := by
  change v1b1923 p = 0 at hhigh
  have hb := final_borrow_one p hbound
  have hflag : v1b193b p = 1 := by
    simp only [v1b193b, Support.byte_merge, v1b1926, hb, hhigh]
    rfl
  have hmask : v1b197a p = -1 := by
    simp only [v1b197a, Support.byte_merge, hflag]
    rfl
  simp only [resultWords, words, quotientLow,
    v1b1980, v1b197d, v1b1977, v1b1995, v1b1992, v1b198c,
    v1b19aa, v1b19a7, v1b19a1, v1b19bf, v1b19bc, v1b19b6,
    show v1b198f p = v1b197a p from rfl,
    show v1b19a4 p = v1b197a p from rfl,
    show v1b19b9 p = v1b197a p from rfl, hmask]
  change #v[(BitVec.allOnes 64 &&& _) ^^^ _, (BitVec.allOnes 64 &&& _) ^^^ _,
    (BitVec.allOnes 64 &&& _) ^^^ _, (BitVec.allOnes 64 &&& _) ^^^ _] = _
  simp only [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic
