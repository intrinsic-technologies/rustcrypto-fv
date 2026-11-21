import P256.Proofs.Sec1.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec
open Standards.SECG.ECC.Curve (Point)

theorem decompact_ne_infinity (x : Nat) : Points.decompact x ≠ some .infinity := by
  simp only [Points.decompact, Points.decompress]
  split
  · simp
  · cases Operations.sqrtMod (Points.curveRhs x) <;> simp

theorem decodePoint_infinity_iff (bytes : ByteArray) :
    Points.decodePoint bytes = some .infinity ↔ bytes = ⟨#[0]⟩ := by
  constructor
  · intro decoded
    unfold Points.decodePoint at decoded
    split at decoded
    · exact (decompact_ne_infinity _ decoded).elim
    · generalize Operations.domain = domain at decoded
      generalize Operations.sqrtMod = sqrt at decoded
      simp only [Standards.SECG.ECC.Points.decodePoint] at decoded
      split at decoded
      · rename_i identity
        change (bytes.data == #[0]) = true at identity
        exact ByteArray.ext (eq_of_beq identity)
      · split at decoded
        · split at decoded <;> simp only [pure, Option.some.injEq, reduceCtorEq] at decoded
        · split at decoded
          · split at decoded
            · contradiction
            · generalize sqrt _ = root at decoded
              cases root with
              | none => simp only [bind, Option.bind, reduceCtorEq] at decoded
              | some root =>
                simp only [bind, Option.bind] at decoded
                split at decoded
                all_goals split at decoded <;> simp only [pure, Option.some.injEq, reduceCtorEq] at decoded
          · contradiction
  · rintro rfl
    exact decodePoint_identity

theorem shape_zero_iff {bytes : ByteArray} (shape : EncodingShape bytes) :
    bytes.data[0]?.getD 0 = 0 ↔ bytes = ⟨#[0]⟩ := by
  rcases shape with rfl | ⟨_, h | h | h⟩ | ⟨_, h⟩
  · simp
  all_goals
    constructor
    · intro zero
      simp [h] at zero
    · intro identity
      rw [identity] at h
      contradiction

end P256.Proofs.Sec1.Decode.Result
