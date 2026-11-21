import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Representation

set_option autoImplicit false

open P256.Proofs.Field.Montgomery (p p_pos reduceFour reduceFour_lt_two_mul_p reduceStep reduceStep_add_wordMultiple reduceStep_mul wordBase)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

def ciosRound (t a b : Nat) : Nat := reduceStep (t + a * b)

def ciosFour (a0 a1 a2 a3 b : Nat) : Nat :=
  ciosRound (ciosRound (ciosRound (ciosRound 0 a0 b) a1 b) a2 b) a3 b

theorem ciosFour_eq_reduceFour (a0 a1 a2 a3 b : Nat) :
    ciosFour a0 a1 a2 a3 b = reduceFour (limbsToNat a0 a1 a2 a3 * b) := by
  simp only [ciosFour, ciosRound, reduceFour, limbsToNat, Nat.add_mul,
    Nat.mul_assoc, Nat.zero_add, ← Nat.add_assoc, reduceStep_add_wordMultiple]

theorem ciosRound_lt_add_p (t a b : Nat)
    (ht : t < b + p) (ha : a < wordBase) : ciosRound t a b < b + p := by
  have hab : a * b + b ≤ wordBase * b := by
    have h := Nat.mul_le_mul_right b (Nat.succ_le_of_lt ha)
    rwa [Nat.succ_mul] at h
  have hm : (t + a * b) % wordBase < wordBase :=
    Nat.mod_lt _ (by decide +kernel)
  have hs := reduceStep_mul (t + a * b)
  change reduceStep (t + a * b) < b + p
  dsimp only [wordBase, p, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at *
  omega

end P256.Proofs.Sec1.SquareRoot.Montgomery
