import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Folds
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Arithmetic

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction

open X86Proofs Common.Arithmetic Common.Invert.LinearCombination Standards.SECG.DomainParameters.Secp256k1

def lastFold (w : Vector (BitVec 64) 5) : Limbs × Bool :=
  let p := mulResult w[4] complementLo
  let q := mulResult w[4] complementHi
  let u := addSpec q.1 w[1]
  let h := adcSpec u.2.CF q.2 0
  let s := addSpec w[4] w[2]
  let r₀ := addSpec p.1 w[0]
  let r₁ := adcSpec r₀.2.CF u.1 p.2
  let r₂ := adcSpec r₁.2.CF s.1 h.1
  let r₃ := adcSpec r₂.2.CF (carryWord s.2.CF) w[3]
  (⟨r₀.1,r₁.1,r₂.1,r₃.1⟩, r₃.2.CF)

theorem lastFold_value (w : Vector (BitVec 64) 5) :
    (lastFold w).1.toNat + 2^256 * (lastFold w).2.toNat = foldHigh (fiveValue w) := by
  generalize he : lastFold w = k
  unfold lastFold at he
  extract_lets p q u h s r₀ r₁ r₂ r₃ at he
  subst k
  dsimp only [Limbs.toNat]
  have hp : p.1.toNat + 2^64*p.2.toNat = w[4].toNat * complementLo.toNat := Common.Field.mulResult_toNat_add _ _
  have hq : q.1.toNat + 2^64*q.2.toNat = w[4].toNat * complementHi.toNat := Common.Field.mulResult_toNat_add _ _
  have hu := Carry.add_carry q.1 w[1]
  have hh := Carry.adc_carry q.2 0 u.2.CF
  have hs := Carry.add_carry w[4] w[2]
  have h₀ := Carry.add_carry p.1 w[0]
  have h₁ := Carry.adc_carry u.1 p.2 r₀.2.CF
  have h₂ := Carry.adc_carry s.1 h.1 r₁.2.CF
  have h₃ := Carry.adc_carry (carryWord s.2.CF) w[3] r₂.2.CF
  change u.1.toNat + 2^64*u.2.CF.toNat = _ at hu
  change h.1.toNat + 2^64*h.2.CF.toNat = q.2.toNat + 0 + u.2.CF.toNat at hh
  change s.1.toNat + 2^64*s.2.CF.toNat = _ at hs
  change r₀.1.toNat + 2^64*r₀.2.CF.toNat = _ at h₀
  change r₁.1.toNat + 2^64*r₁.2.CF.toNat = _ at h₁
  change r₂.1.toNat + 2^64*r₂.2.CF.toNat = _ at h₂
  change r₃.1.toNat + 2^64*r₃.2.CF.toNat = _ at h₃
  rw [carryWord_value] at h₃
  have hb := carry_le_one u.2.CF
  have h0 := w[0].isLt
  have h1 := w[1].isLt
  have h2 := w[2].isLt
  have h3 := w[3].isLt
  have h4 := w[4].isLt
  clear_value r₃ r₂ r₁ r₀ s h u q p
  let lo := w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*w[3].toNat))
  have split : fiveValue w = lo + 2^256*w[4].toNat := by unfold fiveValue lo; omega
  rw [split, foldHigh_split lo _ (by unfold lo; omega)]
  simp only [show complementLo.toNat = 0x402da1732fc9bebf from rfl,
    show complementHi.toNat = 0x4551231950b75fc4 from rfl] at hp hq
  unfold complement lo
  have safe : h.2.CF.toNat = 0 := by omega
  omega

def orderLimbs : Limbs := ⟨0xbfd25e8cd0364141,0xbaaedce6af48a03b,0xfffffffffffffffe,0xffffffffffffffff⟩

def resultWords (w : Vector (BitVec 64) 8) : Vector (BitVec 64) 4 :=
  let r := lastFold (secondFold (firstFold w))
  let d := subRaw r.1 orderLimbs
  Common.Invert.ModularShift.words (if d.2 = 0 ∨ r.2 then d.1 else r.1)

theorem resultWords_eq (w : Vector (BitVec 64) 8) : resultWords w = scalarWords (wideValue w % domain.n) := by
  let m := firstFold w
  let p := secondFold m
  let r := lastFold p
  let d := subRaw r.1 orderLimbs
  have bit : m[6].toNat ≤ 1 := by change (carryWord _).toNat ≤ 1; rw [carryWord_value]; apply carry_le_one
  have folded := lastFold_value p
  change r.1.toNat + 2^256*r.2.toNat = foldHigh (fiveValue p) at folded
  rw [secondFold_value m bit, firstFold_value] at folded
  have sub := subRaw_toNat r.1 orderLimbs
  change d.2.toNat ≤ 1 ∧ d.1.toNat + domain.n = r.1.toNat + 2^256*d.2.toNat at sub
  have wide : wideValue w < 2^512 := by
    have h0 := w[0].isLt
    have h1 := w[1].isLt
    have h2 := w[2].isLt
    have h3 := w[3].isLt
    have h4 := w[4].isLt
    have h5 := w[5].isLt
    have h6 := w[6].isLt
    have h7 := w[7].isLt
    change w[0].toNat + 2^64*(w[1].toNat + 2^64*(w[2].toNat + 2^64*(w[3].toNat + 2^64*(w[4].toNat + 2^64*(w[5].toNat + 2^64*(w[6].toNat + 2^64*w[7].toNat)))))) < _
    omega
  have value := selectResidue (Common.Invert.ModularShift.limbs_toNat_lt r.1)
    (Common.Invert.ModularShift.limbs_toNat_lt d.1) sub.1 sub.2 folded wide
  change Common.Invert.ModularShift.words (if d.2 = 0 ∨ r.2 then d.1 else r.1) = _
  rw [Addition.limbWords_eq, ← value]
  apply congrArg scalarWords
  clear_value d r p m
  have hz : d.2.toNat = 0 ↔ d.2 = 0 := by constructor <;> intro h; exact BitVec.eq_of_toNat_eq h; rw [h]; rfl
  cases r.2 <;> simp [hz]
  split <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction
