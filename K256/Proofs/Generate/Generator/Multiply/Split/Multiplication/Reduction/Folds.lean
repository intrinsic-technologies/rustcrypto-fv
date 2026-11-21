import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Columns
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Residue

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction

open X86Proofs K256.Proofs.Common.Arithmetic K256.Proofs.Common.Invert.LinearCombination

def firstFold (w : Vector (BitVec 64) 8) : Vector (BitVec 64) 7 :=
  let l := lowColumns w[0] w[1] w[4] w[5]
  let m := middleColumn w[2] l.carry w[6] w[5] w[4]
  let n := middleColumn w[3] m.carry w[7] w[6] w[5]
  let t := upperColumns n.carry w[6] w[7]
  #v[l.low,l.next,m.low,n.low,t.low,t.next,t.carry]

def sevenValue (w : Vector (BitVec 64) 7) : Nat :=
  w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*(w[3].toNat +
    2^64*(w[4].toNat + 2^64*(w[5].toNat + 2^64*w[6].toNat)))))

theorem firstFold_value (w : Vector (BitVec 64) 8) : sevenValue (firstFold w) = foldHigh (wideValue w) := by
  generalize he : firstFold w = m
  unfold firstFold at he
  extract_lets l p q t at he
  subst m
  have hl := lowColumns_value w[0] w[1] w[4] w[5]
  have hp := middleColumn_value w[2] l.carry w[6] w[5] w[4]
  have hq := middleColumn_value w[3] p.carry w[7] w[6] w[5]
  have ht := upperColumns_value q.carry w[6] w[7]
  change l.low.toNat + 2^64*(l.next.toNat + 2^64*l.carry.toNat) = _ at hl
  change p.low.toNat + 2^64*p.carry.toNat = _ at hp
  change q.low.toNat + 2^64*q.carry.toNat = _ at hq
  change t.low.toNat + 2^64*(t.next.toNat + 2^64*t.carry.toNat) = _ at ht
  have h0 := w[0].isLt
  have h1 := w[1].isLt
  have h2 := w[2].isLt
  have h3 := w[3].isLt
  let low := w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*(w[3].toNat)))
  let high := w[4].toNat + 2^64*(w[5].toNat + 2^64*(w[6].toNat + 2^64*(w[7].toNat)))
  have split : wideValue w = low + 2^256*high := by
    change w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*(w[3].toNat + 2^64*(w[4].toNat + 2^64*(w[5].toNat + 2^64*(w[6].toNat + 2^64*(w[7].toNat))))))) = _
    dsimp only [low, high]
    omega
  rw [split, foldHigh_split low high (by dsimp only [low]; omega)]
  clear split
  clear_value t q p l
  simp only [sevenValue, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, complement, low, high]
  simp only [show complementLo.toNat = 0x402da1732fc9bebf from rfl,
    show complementHi.toNat = 0x4551231950b75fc4 from rfl] at hl hp hq ht
  omega


def upperSmall (a incoming x bit : BitVec 64) : Column :=
  let u := addSpec incoming a
  let h := adcSpec (bit != 0) (carryWord u.2.CF) 0
  let l := addSpec (if bit != 0 then complementHi else 0) u.1
  let r := addSpec l.1 x
  let c := adcSpec r.2.CF (carryWord l.2.CF) h.1
  ⟨r.1,c.1⟩

theorem upperSmall_value (a incoming x bit : BitVec 64) (hb : bit.toNat ≤ 1) :
    let k := upperSmall a incoming x bit
    k.low.toNat + 2^64*k.carry.toNat = a.toNat + incoming.toNat + x.toNat +
      bit.toNat*(complementHi.toNat + 2^64) := by
  generalize he : upperSmall a incoming x bit = k
  unfold upperSmall at he
  extract_lets u h l r c at he
  subst k
  dsimp only
  have hu := Carry.add_carry incoming a
  change u.1.toNat + 2^64*u.2.CF.toNat = _ at hu
  have hh := Carry.adc_carry (carryWord u.2.CF) 0 (bit != 0)
  change h.1.toNat + 2^64*h.2.CF.toNat = _ at hh
  have hl := Carry.add_carry (if bit != 0 then complementHi else 0) u.1
  change l.1.toNat + 2^64*l.2.CF.toNat = _ at hl
  have hr := Carry.add_carry l.1 x
  change r.1.toNat + 2^64*r.2.CF.toNat = _ at hr
  have hc := Carry.adc_carry (carryWord l.2.CF) h.1 r.2.CF
  change c.1.toNat + 2^64*c.2.CF.toNat = _ at hc
  have bu := carry_le_one u.2.CF
  have bl := carry_le_one l.2.CF
  have br := carry_le_one r.2.CF
  rw [carryWord_value] at hh hc
  clear_value c r l h u
  have hn : bit = 0 ∨ bit = 1 := eq_zero_or_one hb
  rcases hn with h0 | h1
  · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ite_false, show (0 : BitVec 64).toNat = 0 from rfl,
      Bool.toNat_false, Nat.zero_mul] at hh hl ⊢
    omega
  · simp only [h1, show ((1 : BitVec 64) != 0) = true from rfl, ite_true, show (0 : BitVec 64).toNat = 0 from rfl,
      show (1 : BitVec 64).toNat = 1 from rfl, Bool.toNat_true, Nat.one_mul] at hh hl ⊢
    omega

def secondFold (w : Vector (BitVec 64) 7) : Vector (BitVec 64) 5 :=
  let l := lowColumns w[0] w[1] w[4] w[5]
  let m := middleColumn w[2] l.carry w[6] w[5] w[4]
  let t := upperSmall w[3] m.carry w[5] w[6]
  #v[l.low,l.next,m.low,t.low,t.carry]

def fiveValue (w : Vector (BitVec 64) 5) : Nat :=
  w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*(w[3].toNat + 2^64*w[4].toNat)))

theorem secondFold_value (w : Vector (BitVec 64) 7) (hb : w[6].toNat ≤ 1) :
    fiveValue (secondFold w) = foldHigh (sevenValue w) := by
  generalize he : secondFold w = m
  unfold secondFold at he
  extract_lets l p t at he
  subst m
  have hl := lowColumns_value w[0] w[1] w[4] w[5]
  have hp := middleColumn_value w[2] l.carry w[6] w[5] w[4]
  have ht := upperSmall_value w[3] p.carry w[5] w[6] hb
  change l.low.toNat + 2^64*(l.next.toNat + 2^64*l.carry.toNat) = _ at hl
  change p.low.toNat + 2^64*p.carry.toNat = _ at hp
  change t.low.toNat + 2^64*t.carry.toNat = _ at ht
  have h0 := w[0].isLt
  have h1 := w[1].isLt
  have h2 := w[2].isLt
  have h3 := w[3].isLt
  let low := w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*(w[3].toNat)))
  let high := w[4].toNat + 2^64*(w[5].toNat + 2^64*(w[6].toNat))
  have split : sevenValue w = low + 2^256*high := by
    change w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*(w[3].toNat + 2^64*(w[4].toNat + 2^64*(w[5].toNat + 2^64*(w[6].toNat)))))) = _
    dsimp only [low, high]
    omega
  rw [split, foldHigh_split low high (by dsimp only [low]; omega)]
  clear split
  clear_value t p l
  simp only [fiveValue, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, complement, low, high]
  simp only [show complementLo.toNat = 0x402da1732fc9bebf from rfl,
    show complementHi.toNat = 0x4551231950b75fc4 from rfl, Nat.reducePow, Nat.reduceAdd] at hl hp ht
  omega

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction
