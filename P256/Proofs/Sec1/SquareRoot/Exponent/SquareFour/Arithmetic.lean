import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Core
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Proofs.Field.Montgomery
open X86Proofs

def ciosRound (t a b : Nat) : Nat := reduceStep (t + a * b)

def squareTop (c0 c1 old0 old1 a b : BitVec 64) : FinalTop :=
  let x := product64 a b
  let l := add64 x.1 old0
  let m := adc64 x.2 old1 l.2
  let h := adc64 0 0 m.2
  let n := add64 m.1 c1
  let j := adc64 h.1 0 n.2
  let o := add64 l.1 c0
  let r := adc64 n.1 0 o.2
  let q := adc64 j.1 0 r.2
  ⟨o.1, r.1, q.1, j.1, r.2⟩

theorem squareTop_value (c0 c1 old0 old1 a b : BitVec 64) :
    let r := squareTop c0 c1 old0 old1 a b
    r.low.toNat + wordBase*r.mid.toNat + wordBase^2*r.high.toNat =
      c0.toNat + wordBase*c1.toNat + old0.toNat + wordBase*old1.toNat + a.toNat*b.toNat := by
  let x := product64 a b
  let l := add64 x.1 old0
  let m := adc64 x.2 old1 l.2
  let h := adc64 0 0 m.2
  let n := add64 m.1 c1
  let j := adc64 h.1 0 n.2
  let o := add64 l.1 c0
  let r := adc64 n.1 0 o.2
  let q := adc64 j.1 0 r.2
  have hx := product64_value a b
  have hl := add64_value x.1 old0
  have hm := adc64_value x.2 old1 l.2
  have hh := adc64_value 0 0 m.2
  have hn := add64_value m.1 c1
  have hj := adc64_value h.1 0 n.2
  have ho := add64_value l.1 c0
  have hr := adc64_value n.1 0 o.2
  have hq := adc64_value j.1 0 r.2
  have hmcarry := Bool.toNat_le m.2
  have hncarry := Bool.toNat_le n.2
  have hrcarry := Bool.toNat_le r.2
  change x.1.toNat + 18446744073709551616*x.2.toNat = a.toNat*b.toNat at hx
  change l.1.toNat + 18446744073709551616*l.2.toNat = x.1.toNat+old0.toNat at hl
  change m.1.toNat + 18446744073709551616*m.2.toNat = x.2.toNat+old1.toNat+l.2.toNat at hm
  change h.1.toNat + 18446744073709551616*h.2.toNat = 0+0+m.2.toNat at hh
  change n.1.toNat + 18446744073709551616*n.2.toNat = m.1.toNat+c1.toNat at hn
  change j.1.toNat + 18446744073709551616*j.2.toNat = h.1.toNat+0+n.2.toNat at hj
  change o.1.toNat + 18446744073709551616*o.2.toNat = l.1.toNat+c0.toNat at ho
  change r.1.toNat + 18446744073709551616*r.2.toNat = n.1.toNat+0+o.2.toNat at hr
  change q.1.toNat + 18446744073709551616*q.2.toNat = j.1.toNat+0+r.2.toNat at hq
  change o.1.toNat + 18446744073709551616*r.1.toNat + 18446744073709551616^2*q.1.toNat =
    c0.toNat + 18446744073709551616*c1.toNat + old0.toNat + 18446744073709551616*old1.toNat + a.toNat*b.toNat
  clear_value x l m h n j o r q
  omega

def squareRound (t : FinalWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) : FinalWords :=
  let c := coreWords t.first t.second t.top.low a b
  ⟨c.first, c.second, squareTop c.low c.high t.top.mid t.top.high a b[3]⟩

theorem squareRound_value (t : FinalWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) :
    (squareRound t a b).value = ciosRound t.value a.toNat (wordsValue b) := by
  let c := coreWords t.first t.second t.top.low a b
  let r := squareTop c.low c.high t.top.mid t.top.high a b[3]
  have hc : c.value = reduceStep
      (t.first.toNat + wordBase*t.second.toNat + wordBase^2*t.top.low.toNat + a.toNat*lowerWordsValue b) :=
    coreWords_value t.first t.second t.top.low a b
  have ht : r.low.toNat + wordBase*r.mid.toNat + wordBase^2*r.high.toNat =
      c.low.toNat + wordBase*c.high.toNat + t.top.mid.toNat + wordBase*t.top.high.toNat + a.toNat*b[3].toNat :=
    squareTop_value c.low c.high t.top.mid t.top.high a b[3]
  have hb : a.toNat * wordsValue b = a.toNat * lowerWordsValue b +
      wordBase^3 * (a.toNat*b[3].toNat) := by
    simp only [wordsValue, lowerWordsValue,
      Nat.pow_succ, Nat.pow_zero, Nat.mul_add]
    ac_rfl
  have he : t.value + a.toNat * wordsValue b =
      (t.first.toNat + wordBase*t.second.toNat + wordBase^2*t.top.low.toNat +
        a.toNat*lowerWordsValue b) + wordBase *
          (wordBase^2 * (t.top.mid.toNat + wordBase*t.top.high.toNat + a.toNat*b[3].toNat)) := by
    rw [hb]
    simp only [FinalWords.value, wordBase]
    omega
  rw [ciosRound, he, P256.Proofs.Field.Montgomery.reduceStep_add_wordMultiple, ← hc]
  change c.first.toNat + wordBase*c.second.toNat + wordBase^2*r.low.toNat +
    wordBase^3*r.mid.toNat + wordBase^4*r.high.toNat = _
  clear_value c r
  simp only [CoreWords.value, wordBase] at ht ⊢
  omega

def squareWords (a : Vector (BitVec 64) 4) : FinalWords :=
  let z : FinalWords := ⟨0, 0, ⟨0, 0, 0, 0, false⟩⟩
  let t0 := squareRound z a[0] a
  let t1 := squareRound t0 a[1] a
  let t2 := squareRound t1 a[2] a
  squareRound t2 a[3] a

theorem squareWords_value (a : Vector (BitVec 64) 4) :
    (squareWords a).value = P256.Proofs.Field.Montgomery.reduceFour (wordsValue a * wordsValue a) := by
  unfold squareWords
  rw [squareRound_value, squareRound_value, squareRound_value, squareRound_value]
  change ciosRound (ciosRound (ciosRound (ciosRound 0 a[0].toNat (wordsValue a))
    a[1].toNat (wordsValue a)) a[2].toNat (wordsValue a)) a[3].toNat (wordsValue a) = _
  simp only [ciosRound, reduceFour, wordsValue, Nat.add_mul, Nat.mul_assoc,
    reduceStep_add_wordMultiple, Nat.zero_add,
    show wordBase^2 = wordBase*wordBase by rfl,
    show wordBase^3 = wordBase*(wordBase*wordBase) by rfl]

theorem squareWords_lt (a : Vector (BitVec 64) 4) (ha : wordsValue a < p) :
    (squareWords a).value < 2*p := by
  rw [squareWords_value]
  apply P256.Proofs.Field.Montgomery.reduceFour_lt_two_mul_p
  exact Nat.mul_lt_mul_of_lt_of_lt ha (Nat.lt_trans ha P256.Proofs.Field.Montgomery.p_lt_radix)

def squareReduced (a : Vector (BitVec 64) 4) : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs :=
  let t := squareWords a
  P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.reduce ⟨t.first, t.second, t.top.low, t.top.mid⟩ t.top.high

theorem squareReduced_value (a : Vector (BitVec 64) 4) (ha : wordsValue a < p) :
    (squareReduced a).toNat = P256.Proofs.Field.Montgomery.subtractP
      (P256.Proofs.Field.Montgomery.reduceFour (wordsValue a * wordsValue a)) := by
  have hlt := squareWords_lt a ha
  have he : (P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.mk (squareWords a).first (squareWords a).second
      (squareWords a).top.low (squareWords a).top.mid).toNat +
      2^256*(squareWords a).top.high.toNat = (squareWords a).value := by
    simp only [P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat, FinalWords.value, wordBase]
    omega
  unfold squareReduced
  rw [P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.reduce_toNat _ _ (he ▸ hlt), he, squareWords_value]

theorem squareReduced_montgomery (a : Vector (BitVec 64) 4) (y : Nat)
    (ha : wordsValue a = y * 2^256 % p) :
    (squareReduced a).toNat = y*y*2^256 % p := by
  rw [squareReduced_value a (ha ▸ Nat.mod_lt _ P256.Proofs.Field.Montgomery.p_pos), ha,
    P256.Proofs.Field.Montgomery.subtractP_reduceFour_montgomery_mul]


end P256.Proofs.Sec1.SquareRoot.SquareFour
