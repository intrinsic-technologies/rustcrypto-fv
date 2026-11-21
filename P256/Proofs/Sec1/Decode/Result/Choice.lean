import P256.Proofs.Sec1.Decode.Result.Model
import P256.Proofs.Sec1.Decode.Result.Select

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec
open Standards.SECG.ECC.Curve (Point)

def validityFlag : Option Point → UInt8
  | none => 0
  | some _ => 1

theorem choice_correct {bytes : ByteArray} (shape : EncodingShape bytes) :
    choice (bytes.data[0]?.getD 0).toBitVec (validityFlag (Points.decodePoint bytes)).toBitVec =
      if (Points.decodePublicKey bytes).isSome then 1 else 0 := by
  cases decoded : Points.decodePoint bytes with
  | none =>
    simp [Points.decodePublicKey, decoded, validityFlag, choice]
  | some point =>
    cases point with
    | infinity =>
      have identity := (decodePoint_infinity_iff bytes).mp decoded
      subst bytes
      simp only [Points.decodePublicKey, decodePoint_identity, validityFlag]
      decide +kernel
    | affine x y =>
      have nonzero : (bytes.data[0]?.getD 0).toBitVec ≠ 0#8 := by
        intro zero
        have tag : bytes.data[0]?.getD 0 = 0 := UInt8.eq_of_toBitVec_eq zero
        have identity := (shape_zero_iff shape).mp tag
        rw [identity, decodePoint_identity] at decoded
        simp only [Option.some.injEq, reduceCtorEq] at decoded
      simp [Points.decodePublicKey, decoded, validityFlag, choice, nonzero]

end P256.Proofs.Sec1.Decode.Result
