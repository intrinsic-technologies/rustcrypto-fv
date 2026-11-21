import AesGcm.Proofs.Machine.GHASH.Montgomery

namespace AesGcm.Proofs.Machine.GHASH

def polyvalKeyWords (lo hi : BitVec 64) : BitVec 64 × BitVec 64 :=
  let c := hi >>> (63 : Nat)
  ((lo <<< (1 : Nat)) ||| c,
    ((hi <<< (1 : Nat)) ||| (lo >>> (63 : Nat))) ^^^ (c * 0xc200000000000000#64))

theorem ushr63_eq_msb (x : BitVec 64) :
    x >>> (63 : Nat) = if x.getLsbD 63 then 1#64 else 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight]
  by_cases he : i = 0
  · subst i
    cases x.getLsbD 63 <;> rfl
  · have hz : x.getLsbD (63 + i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    cases x.getLsbD 63 <;> simp [hz, he]

theorem append_shiftLeft_one (lo hi : BitVec 64) :
    (hi ++ lo) <<< (1 : Nat) =
      ((hi <<< (1 : Nat)) ||| (lo >>> (63 : Nat))) ++ (lo <<< (1 : Nat)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
    BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  grind

theorem shiftLeft_one_or_one (x : BitVec 64) :
    (x <<< (1 : Nat)) ||| 1#64 = (x <<< (1 : Nat)) ^^^ 1#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_one]
  grind

theorem polyvalKeyWords_eq_mulX (lo hi : BitVec 64) :
    let k := polyvalKeyWords lo hi
    k.2 ++ k.1 = polyvalMulX (hi ++ lo) := by
  have hm : 0xc2000000000000000000000000000001#128 =
      0xc200000000000000#64 ++ 1#64 := by decide +kernel
  simp only [polyvalKeyWords, polyvalMulX, ushr63_eq_msb hi,
    BitVec.getLsbD_append, show ¬127 < 64 from by decide,
    show 127 - 64 = 63 from by decide, ite_false, append_shiftLeft_one]
  cases hi.getLsbD 63
  · simp
  · simp only [ite_true, hm, BitVec.one_mul, shiftLeft_one_or_one]
    exact (BitVec.xor_append (x₁ := (hi <<< (1 : Nat)) ||| (lo >>> (63 : Nat)))
      (y₁ := lo <<< (1 : Nat)) (x₂ := 0xc200000000000000#64) (y₂ := 1#64)).symm

end AesGcm.Proofs.Machine.GHASH
