import K256.Proofs.Common.Invert.LinearCombination.Model
import K256.Proofs.Common.Invert.LinearCombination.Signed
import K256.Proofs.Common.Field.WordOps

namespace K256.Proofs.Common.Invert.LinearCombination

open X86Proofs

def leftWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[(v10852e p).1, (v108575 p).1, (v108578 p).1, (v10857b p).1, (v10857e p).1]

def rightWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[(v108585 p).1, (v1085c3 p).1, (v1085c8 p).1, (v1085d5 p).1, (v1085d8 p).1]

private theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (adcSpec c a b).1.toNat + 2^64*(adcSpec c a b).2.CF.toNat = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  simp only [adcSpec, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]
  by_cases h : (a.toNat+b.toNat+c.toNat)%2^64 = a.toNat+b.toNat+c.toNat <;>
    simp only [h, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
      Bool.toNat_true, Bool.toNat_false] <;> omega

private theorem add_carry (a b : BitVec 64) :
    (addSpec a b).1.toNat + 2^64*(addSpec a b).2.CF.toNat = a.toNat + b.toNat := by
  simpa [adcSpec, addSpec] using adc_carry a b false

theorem product_limbs (u a b c d : BitVec 64) :
    let p := mulResult u a
    let q := mulResult u b
    let r := mulResult u c
    let s := mulResult u d
    let e := addSpec q.1 p.2
    let f := adcSpec e.2.CF r.1 q.2
    let g := adcSpec f.2.CF s.1 r.2
    let h := adcSpec g.2.CF s.2 0
    packFive #v[p.1.toNat,e.1.toNat,f.1.toNat,g.1.toNat,h.1.toNat] =
        u.toNat * packFour #v[a.toNat,b.toNat,c.toNat,d.toNat] := by
  intro p q r s e f g h
  have hp := Field.mulResult_toNat_add u a
  have hq := Field.mulResult_toNat_add u b
  have hr := Field.mulResult_toNat_add u c
  have hs := Field.mulResult_toNat_add u d
  have he := add_carry q.1 p.2
  have hf := adc_carry r.1 q.2 e.2.CF
  have hg := adc_carry s.1 r.2 f.2.CF
  have hh := adc_carry s.2 0 g.2.CF
  change p.1.toNat + 2^64*p.2.toNat = _ at hp
  change q.1.toNat + 2^64*q.2.toNat = _ at hq
  change r.1.toNat + 2^64*r.2.toNat = _ at hr
  change s.1.toNat + 2^64*s.2.toNat = _ at hs
  change e.1.toNat + 2^64*e.2.CF.toNat = _ at he
  change f.1.toNat + 2^64*f.2.CF.toNat = _ at hf
  change g.1.toNat + 2^64*g.2.CF.toNat = _ at hg
  change h.1.toNat + 2^64*h.2.CF.toNat = s.2.toNat + 0 + g.2.CF.toNat at hh
  have lim := Nat.mul_le_mul (show u.toNat ≤ 2^64-1 by have := u.isLt; omega)
    (show d.toNat ≤ 2^64-1 by have := d.isLt; omega)
  have hgbit : g.2.CF.toNat ≤ 1 := by cases g.2.CF <;> decide
  simp only [packFive, packFour, Vector.getElem_mk, Array.reduceGetElem, Nat.mul_add,
    Nat.mul_left_comm u.toNat]
  omega

theorem leftWords_product (p : Inputs) :
    wideValue (leftWords p) = (v108516 p).toNat * packFour (p.a.map BitVec.toNat) := by
  simpa only [v10852e, v108540, v108555, v108568, v108575, v108578, v10857b, v10857e, wideValue, leftWords, packFive, packFour, Vector.getElem_map,
    Vector.getElem_mk, Array.reduceGetElem] using
    product_limbs (v108516 p) p.a[0] p.a[1] p.a[2] p.a[3]

theorem rightWords_product (p : Inputs) :
    wideValue (rightWords p) = (v108572 p).toNat * packFour (p.b.map BitVec.toNat) := by
  simpa only [v108585, v108595, v1085a4, v1085bf, v1085c3, v1085c8, v1085d5, v1085d8, wideValue, rightWords, packFive, packFour, Vector.getElem_map,
    Vector.getElem_mk, Array.reduceGetElem] using
    product_limbs (v108572 p) p.b[0] p.b[1] p.b[2] p.b[3]

end K256.Proofs.Common.Invert.LinearCombination
