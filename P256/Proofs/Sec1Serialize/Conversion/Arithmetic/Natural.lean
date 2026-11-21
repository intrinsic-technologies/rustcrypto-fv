import P256.Proofs.Field.Montgomery.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Conversion.Montgomery

export P256.Proofs.Field.Montgomery (p wordBase reduceStep reduceFour p_pos p_lt_radix reduceStep_eq reduceStep_mul reduceStep_mod reduceStep_add_wordMultiple reduceStep_limbs_sparse)

theorem reduceStep_lt (a : Nat) (ha : a < p) : reduceStep a < p := by
  have h := reduceStep_mul a
  have hm : a % wordBase < wordBase := Nat.mod_lt _ (by decide +kernel)
  dsimp [wordBase, p, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at *
  omega

theorem wordBase_mul_inverse : wordBase * ((p + 1) / wordBase) = p + 1 := by
  decide +kernel

theorem mul_wordBase_mod_cancel (a b : Nat)
    (h : a * wordBase % p = b * wordBase % p) : a % p = b % p := by
  have hi := congrArg (fun n => n * ((p + 1) / wordBase) % p) h
  simpa only [Nat.mod_mul_mod, Nat.mul_assoc, wordBase_mul_inverse, Nat.mul_add,
    Nat.mul_one, Nat.mul_add_mod_self_right] using hi

theorem reduceStep_mul_wordBase (a : Nat) : reduceStep (a * wordBase % p) = a % p := by
  have h := mul_wordBase_mod_cancel (reduceStep (a * wordBase % p)) a
    (by simpa only [Nat.mod_mod] using reduceStep_mod (a * wordBase % p))
  rwa [Nat.mod_eq_of_lt (reduceStep_lt _ (Nat.mod_lt _ p_pos))] at h

theorem reduceStep_mul_pow (a n : Nat) :
    reduceStep (a * wordBase ^ (n + 1) % p) = a * wordBase ^ n % p := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, reduceStep_mul_wordBase]

theorem reduceFour_montgomery (x : Nat) (hx : x < p) :
    reduceFour (x * 2 ^ 256 % p) = x := by
  rw [show 2 ^ 256 = wordBase ^ 4 by decide +kernel]
  unfold reduceFour
  rw [reduceStep_mul_pow, reduceStep_mul_pow, reduceStep_mul_pow, reduceStep_mul_pow]
  simp only [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx]

def limbsToNat (a0 a1 a2 a3 : Nat) : Nat :=
  a0 + wordBase * (a1 + wordBase * (a2 + wordBase * a3))

theorem limbsToNat_digits_eq (a0 a1 a2 a3 : Nat)
    (h0 : a0 < wordBase) (h1 : a1 < wordBase)
    (h2 : a2 < wordBase) (h3 : a3 < wordBase) :
    let a := limbsToNat a0 a1 a2 a3
    a % wordBase = a0 ∧ a / wordBase % wordBase = a1 ∧
      a / wordBase ^ 2 % wordBase = a2 ∧ a / wordBase ^ 3 % wordBase = a3 := by
  dsimp [limbsToNat, wordBase] at *
  omega

abbrev halfBase : Nat := 2 ^ 32

abbrev modulusHigh : Nat := 0xffffffff00000001

def compilerRound (a b c d z : Nat) : Nat × Nat × Nat × Nat :=
  let q := (a + z) % wordBase
  let e := (a + z) / wordBase
  let neglo := q * (wordBase - 1) % wordBase
  let neghi := q * (wordBase - 1) / wordBase
  let carryNeg := (neglo + q) / wordBase
  let ec := (e + neghi + carryNeg) % wordBase
  let l := q * (halfBase - 1) % wordBase + b
  let h := q * (halfBase - 1) / wordBase + l / wordBase
  let k := q * modulusHigh % wordBase + d
  let j := q * modulusHigh / wordBase + k / wordBase
  let o0 := l % wordBase + ec
  let o1 := h + c + o0 / wordBase
  let o2 := k % wordBase + o1 / wordBase
  let o3 := j + o2 / wordBase
  (o0 % wordBase, o1 % wordBase, o2 % wordBase, o3 % wordBase)

theorem mul_wordBase_sub_one_carry (q : Nat) :
    q * (wordBase - 1) / wordBase +
      (q * (wordBase - 1) % wordBase + q) / wordBase = q := by
  dsimp [wordBase] at *
  omega

theorem compilerRound_intermediates (a b c d z : Nat)
    (ha : a < wordBase) (hb : b < wordBase) (_hc : c < wordBase)
    (hd : d < wordBase) (hz : z < wordBase) :
    let q := (a + z) % wordBase
    let e := (a + z) / wordBase
    let neglo := q * (wordBase - 1) % wordBase
    let neghi := q * (wordBase - 1) / wordBase
    let carryNeg := (neglo + q) / wordBase
    let ec := (e + neghi + carryNeg) % wordBase
    let l := q * (halfBase - 1) % wordBase + b
    let h := q * (halfBase - 1) / wordBase + l / wordBase
    let k := q * modulusHigh % wordBase + d
    let j := q * modulusHigh / wordBase + k / wordBase
    h < wordBase ∧ j < wordBase ∧ ec = q + e ∧ ec < wordBase := by
  have hq : (a + z) % wordBase < wordBase := Nat.mod_lt _ (by decide +kernel)
  have hn := mul_wordBase_sub_one_carry ((a + z) % wordBase)
  dsimp [wordBase, halfBase, modulusHigh] at *
  omega

theorem reduceStep_limbs_add (a b c d z : Nat) :
    reduceStep (limbsToNat a b c d + z) =
      (a + z) / wordBase + b + wordBase * (c + wordBase * d) +
        ((a + z) % wordBase) * ((p + 1) / wordBase) := by
  have h : limbsToNat a b c d + z = (a + z) + wordBase * (b + wordBase * (c + wordBase * d)) := by
    unfold limbsToNat
    omega
  rw [h, reduceStep_add_wordMultiple, reduceStep_eq]
  omega

theorem compilerRound_eq_reduceStep (a b c d z : Nat)
    (ha : a < wordBase) (hb : b < wordBase) (hc : c < wordBase)
    (hd : d < wordBase) (hz : z < wordBase)
    (hn : limbsToNat a b c d + z < p) :
    let r := compilerRound a b c d z
    limbsToNat r.1 r.2.1 r.2.2.1 r.2.2.2 = reduceStep (limbsToNat a b c d + z) := by
  have hi := compilerRound_intermediates a b c d z ha hb hc hd hz
  have hlt := reduceStep_lt (limbsToNat a b c d + z) hn
  rw [reduceStep_limbs_add] at hlt ⊢
  dsimp [compilerRound, limbsToNat, wordBase, halfBase, modulusHigh,
    p, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at *
  omega

end P256.Proofs.Sec1Serialize.Conversion.Montgomery
