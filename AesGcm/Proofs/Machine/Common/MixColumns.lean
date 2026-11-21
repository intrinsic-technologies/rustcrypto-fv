import Standards.NIST.AES.Transformations

namespace AesGcm.Proofs.Machine
open Standards.NIST.AES

private def bitSelected (a : UInt8) (c : UInt8) (i : Nat) : UInt8 :=
  if (c >>> i.toUInt8) &&& 1 == 1 then a else 0

private theorem byte_bit (c : UInt8) (i : Fin 8) :
    ((c >>> i.val.toUInt8) &&& 1 == 1) = c.toBitVec.getLsbD i.val := by
  have h : ∀ c : Fin 256, ∀ i : Fin 8,
      ((UInt8.ofFin c >>> i.val.toUInt8) &&& 1 == 1) =
        (UInt8.ofFin c).toBitVec.getLsbD i.val := by decide +kernel
  exact h c.toFin i

private theorem bitSelected_xor (a c d : UInt8) (i : Nat) (hi : i < 8) :
    bitSelected a (c ^^^ d) i = bitSelected a c i ^^^ bitSelected a d i := by
  simp only [bitSelected, byte_bit _ ⟨i, hi⟩, UInt8.toBitVec_xor, BitVec.getLsbD_xor]
  cases c.toBitVec.getLsbD i <;> cases d.toBitVec.getLsbD i <;>
    simp only [Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_true, ite_false, UInt8.xor_zero, UInt8.zero_xor, UInt8.xor_self]

private def xtimesN : Nat → UInt8 → UInt8
  | 0, b => b
  | n + 1, b => xtimes (xtimesN n b)

private theorem mul_eq_bits (b c : UInt8) :
    mul b c = bitSelected (xtimesN 0 b) c 0 ^^^ bitSelected (xtimesN 1 b) c 1 ^^^
      bitSelected (xtimesN 2 b) c 2 ^^^ bitSelected (xtimesN 3 b) c 3 ^^^
      bitSelected (xtimesN 4 b) c 4 ^^^ bitSelected (xtimesN 5 b) c 5 ^^^
      bitSelected (xtimesN 6 b) c 6 ^^^ bitSelected (xtimesN 7 b) c 7 := by
  simp only [mul, show List.range 8 = [0,1,2,3,4,5,6,7] from rfl,
    List.foldl_cons, List.foldl_nil, xtimesN, bitSelected, UInt8.zero_xor]

theorem mul_xor_right (a b c : UInt8) : mul a (b ^^^ c) = mul a b ^^^ mul a c := by
  simp only [mul_eq_bits,
    bitSelected_xor _ _ _ 0 (by decide),
    bitSelected_xor _ _ _ 1 (by decide),
    bitSelected_xor _ _ _ 2 (by decide),
    bitSelected_xor _ _ _ 3 (by decide),
    bitSelected_xor _ _ _ 4 (by decide),
    bitSelected_xor _ _ _ 5 (by decide),
    bitSelected_xor _ _ _ 6 (by decide),
    bitSelected_xor _ _ _ 7 (by decide)]
  ac_rfl

end AesGcm.Proofs.Machine
