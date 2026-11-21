import K256.Proofs.Common.Invert.LinearCombination.Wide
import K256.Proofs.Generate.Curve.Decompose

namespace K256.Proofs.Generate.Generator.Multiply.Prepare

open Common.Invert.LinearCombination Standards.SECG.DomainParameters.Secp256k1

def highBit (a b c d : BitVec 64) : BitVec 64 :=
  let x := ((0xdfe92f46681b20a0 - a) &&& a) >>> 63
  let y := (((0 - x).sshiftRight 63 - b + 0x5d576e7357a4501d) ||| b) >>> 63
  let z := ((~~~c + (0 - y).sshiftRight 63) &&& c) >>> 63
  (((0 - z).sshiftRight 63 - d + 0x7fffffffffffffff) ||| d) >>> 63

private def halfOrder : Limbs :=
  ⟨0xdfe92f46681b20a0, 0x5d576e7357a4501d, 0xffffffffffffffff, 0x7fffffffffffffff⟩

private theorem borrow_high {k : BitVec 64} (hk : k.msb = true) (x r : BitVec 64) :
    borrow k x r = (r &&& x) >>> 63 := by
  apply BitVec.eq_of_toNat_eq
  simp only [borrow, shift63_toNat, BitVec.msb_or, BitVec.msb_and, BitVec.msb_not, hk] <;> cases x.msb <;> cases r.msb <;> rfl

private theorem borrow_low {k : BitVec 64} (hk : k.msb = false) (x r : BitVec 64) :
    borrow k x r = (r ||| x) >>> 63 := by
  apply BitVec.eq_of_toNat_eq
  simp only [borrow, shift63_toNat, BitVec.msb_or, BitVec.msb_and, BitVec.msb_not, hk] <;> cases x.msb <;> cases r.msb <;> rfl

private theorem highBit_eq_subRaw (a b c d : BitVec 64) :
    highBit a b c d = (subRaw halfOrder ⟨a,b,c,d⟩).2 := by
  simp only [subRaw, halfOrder, borrow_high (k := 0xdfe92f46681b20a0) (by decide),
    borrow_low (k := 0x5d576e7357a4501d) (by decide),
    borrow_high (k := 0xffffffffffffffff) (by decide),
    borrow_low (k := 0x7fffffffffffffff) (by decide), subWord, highBit]
  have reorder (u v w : BitVec 64) : u - v + w = u + (w - v) := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-v) w]
  have complement (v : BitVec 64) : (0xffffffffffffffff : BitVec 64) - v = ~~~v := by
    simp only [BitVec.not_eq_neg_add, BitVec.sub_eq_add_neg]
    exact BitVec.add_comm _ _
  have neg (v : BitVec 64) : (0 : BitVec 64) - v = -v := by
    exact BitVec.zero_sub _
  simp only [reorder, neg, complement, BitVec.add_comm (~~~c) _]

theorem highBit_correct (a b c d : BitVec 64) :
    highBit a b c d = if domain.n / 2 < a.toNat + 2^64 * (b.toNat + 2^64 * (c.toNat + 2^64*d.toNat)) then 1 else 0 := by
  let x : Limbs := ⟨a,b,c,d⟩
  have h := subRaw_toNat halfOrder x
  have bound (l : Limbs) : l.toNat < 2^256 := by
    have := l.l0.isLt
    have := l.l1.isLt
    have := l.l2.isLt
    have := l.l3.isLt
    unfold Limbs.toNat
    omega
  have hh : halfOrder.toNat = domain.n / 2 := by decide +kernel
  rw [hh] at h
  have := bound (subRaw halfOrder x).1
  have := bound x
  rw [highBit_eq_subRaw]
  change (subRaw halfOrder x).2 = if domain.n / 2 < x.toNat then 1 else 0
  split
  · apply BitVec.eq_of_toNat_eq
    change (subRaw halfOrder x).2.toNat = 1
    omega
  · apply BitVec.eq_of_toNat_eq
    change (subRaw halfOrder x).2.toNat = 0
    omega

end K256.Proofs.Generate.Generator.Multiply.Prepare
