import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Words
import K256.Proofs.Common.Arithmetic.Carry
import K256.Proofs.Common.Invert.ModularShift.Limbs

namespace K256.Proofs.Generate.Generator.Multiply.Split.Addition

open X86Proofs Common.Invert.LinearCombination Common.Arithmetic
  Standards.SECG.DomainParameters.Secp256k1

private def wordAt (w : Words) (i : Nat) : Nat := (w[i]?.getD 0).toNat

private theorem value_four (w : Words) : Carry.value (wordAt w) 4 = scalarValue w := by
  change 0 + 1*w[0].toNat + 2^64*w[1].toNat + 2^128*w[2].toNat + 2^192*w[3].toNat =
    w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*w[3].toNat))
  omega


theorem limbWords_eq (q : Limbs) : Common.Invert.ModularShift.words q = scalarWords q.toNat := by
  have := q.l0.isLt
  have := q.l1.isLt
  have := q.l2.isLt
  have := q.l3.isLt
  apply Vector.ext
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [scalarWords, Common.Invert.ModularShift.words, Vector.getElem_ofFn, Limbs.toNat,
      BitVec.toNat_ofNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, Nat.reduceMul, Nat.reducePow, Nat.div_one] <;> omega

private theorem flagWord_toNat (c : Bool) : (flagWord c).toNat = c.toNat := by cases c <;> rfl

private theorem sum_value (a b : Words) :
    (sum a b).1.toNat + 2^256 * (sum a b).2.toNat = scalarValue a + scalarValue b := by
  let l := addSpec b[0] a[0]
  let t := adcSpec l.2.CF a[1] 0
  let u := addSpec b[2] a[2]
  let v := addSpec b[3] a[3]
  let s := addSpec t.1 b[1]
  let m := adcSpec s.2.CF u.1 (flagWord t.2.CF)
  let h := adcSpec m.2.CF (flagWord u.2.CF) v.1
  let r : Words := #v[l.1,s.1,m.1,h.1]
  let c := [0, l.2.CF.toNat, t.2.CF.toNat + s.2.CF.toNat,
    u.2.CF.toNat + m.2.CF.toNat, v.2.CF.toNat + h.2.CF.toNat]
  have rows (i : Nat) (hi : i < 4) : wordAt r i + 2^64 * c[i+1]! =
      wordAt a i + wordAt b i + c[i]! := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · change l.1.toNat + 2^64*l.2.CF.toNat = a[0].toNat+b[0].toNat+0
      rw [Nat.add_zero, Nat.add_comm a[0].toNat]
      exact Carry.add_carry _ _
    · have ht := Carry.adc_carry a[1] 0 l.2.CF
      have hs := Carry.add_carry t.1 b[1]
      change t.1.toNat + 2^64*t.2.CF.toNat = a[1].toNat + 0 + l.2.CF.toNat at ht
      change s.1.toNat + 2^64*s.2.CF.toNat = _ at hs
      change s.1.toNat + 2^64*(t.2.CF.toNat+s.2.CF.toNat) = a[1].toNat+b[1].toNat+l.2.CF.toNat
      omega
    · have hu := Carry.add_carry b[2] a[2]
      have hm := Carry.adc_carry u.1 (flagWord t.2.CF) s.2.CF
      rw [flagWord_toNat] at hm
      change u.1.toNat + 2^64*u.2.CF.toNat = _ at hu
      change m.1.toNat + 2^64*m.2.CF.toNat = _ at hm
      change m.1.toNat + 2^64*(u.2.CF.toNat+m.2.CF.toNat) =
        a[2].toNat+b[2].toNat+(t.2.CF.toNat+s.2.CF.toNat)
      omega
    · have hv := Carry.add_carry b[3] a[3]
      have hh := Carry.adc_carry (flagWord u.2.CF) v.1 m.2.CF
      rw [flagWord_toNat] at hh
      change v.1.toNat + 2^64*v.2.CF.toNat = _ at hv
      change h.1.toNat + 2^64*h.2.CF.toNat = _ at hh
      change h.1.toNat + 2^64*(v.2.CF.toNat+h.2.CF.toNat) =
        a[3].toNat+b[3].toNat+(u.2.CF.toNat+m.2.CF.toNat)
      omega
  have eq := Carry.addChain (n := 4) (c := fun i => c[i]!) rows
  rw [value_four, value_four, value_four] at eq
  have top (e f : Bool) : (adcSpec f (flagWord e) 0).1.toNat = e.toNat + f.toNat := by
    cases e <;> cases f <;> decide
  change scalarValue r + 2^256*(adcSpec h.2.CF (flagWord v.2.CF) 0).1.toNat = _
  rw [top]
  exact eq.trans (Nat.add_zero _)

private theorem selected_limbs (s d : Limbs) (b : Bool) :
    let k := flagWord b
    #v[selectWord s.l0 d.l0 k, selectWord s.l1 d.l1 k,
       selectWord s.l2 d.l2 k, selectWord s.l3 d.l3 k] =
      scalarWords (if b then s.toNat else d.toNat) := by
  simp only [flagWord, selectWord, Carry.maskedSelect]
  cases b <;> exact limbWords_eq _

private theorem reduce_value (s d : Limbs) (high borrow : BitVec 64) (n t : Nat)
    (bound : n < 2^256) (range : t < 2*n) (value : s.toNat + 2^256*high.toNat = t)
    (diff : d.toNat + n = s.toNat + 2^256*borrow.toNat) (bit : borrow.toNat ≤ 1) :
    let k := flagWord (high == 0) &&& -borrow
    #v[selectWord s.l0 d.l0 k, selectWord s.l1 d.l1 k,
       selectWord s.l2 d.l2 k, selectWord s.l3 d.l3 k] = scalarWords (t % n) := by
  have sd := Common.Invert.ModularShift.limbs_toNat_lt d
  have ss := Common.Invert.ModularShift.limbs_toNat_lt s
  have reduced (h : n ≤ t) : t % n = t-n := by
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  rcases eq_zero_or_one bit with h | h
  · have hb : borrow.toNat = 0 := h ▸ rfl
    have hk : flagWord (high == 0) &&& -borrow = flagWord false := by
      rw [h]
      exact BitVec.and_zero
    rw [hk, selected_limbs]
    apply congrArg scalarWords
    change d.toNat = _
    rw [reduced (by omega)]
    omega
  · have hb : borrow.toNat = 1 := h ▸ rfl
    have hk : flagWord (high == 0) &&& -borrow = flagWord (high == 0) := by
      rw [h]
      exact BitVec.and_allOnes
    rw [hk, selected_limbs]
    apply congrArg scalarWords
    by_cases hh : high = 0
    · have hz : high.toNat = 0 := hh ▸ rfl
      rw [hh, ite_eq_left (by decide), Nat.mod_eq_of_lt (by omega)]
      omega
    · have hz : high.toNat ≠ 0 := fun e => hh (BitVec.eq_of_toNat_eq e)
      simp only [beq_iff_eq, hh, ite_false]
      rw [reduced (by omega)]
      omega

theorem addWords_eq {x y : Nat} (hx : x < domain.n) (hy : y < domain.n) :
    addWords (scalarWords x) (scalarWords y) (scalarWords domain.n) = scalarWords ((x+y) % domain.n) := by
  have bound : domain.n < 2^256 := by decide +kernel
  let a := scalarWords x
  let b := scalarWords y
  let p := Common.Invert.ModularShift.limbs (scalarWords domain.n)
  let s := sum a b
  let d := subRaw s.1 p
  have hv := sum_value a b
  rw [scalarWords_value x (Nat.lt_trans hx bound), scalarWords_value y (Nat.lt_trans hy bound)] at hv
  have hp : p.toNat = domain.n := scalarWords_value _ bound
  have hd := subRaw_toNat s.1 p
  change d.2.toNat ≤ 1 ∧ d.1.toNat + p.toNat = s.1.toNat + 2^256*d.2.toNat at hd
  rw [hp] at hd
  exact reduce_value s.1 d.1 s.2 d.2 domain.n (x+y) bound (by omega) hv hd.2 hd.1

end K256.Proofs.Generate.Generator.Multiply.Split.Addition
