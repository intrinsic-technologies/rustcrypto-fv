import P256.Proofs.SignatureFromDer.Model

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec

theorem signatureFromSlice_result_size {input output : ByteArray}
    (model : Ecdsa.signatureFromSlice #[input] = some output) : output.size = 64 := by
  change (Ecdsa.decodeSignature input).map Ecdsa.encodeFixed = some output at model
  cases h : Ecdsa.decodeSignature input with
  | none => simp only [h, Option.map_none, reduceCtorEq] at model
  | some value =>
    have eq : Ecdsa.encodeFixed value = output := by
      simpa only [h, Option.map_some, Option.some.injEq] using model
    rw [← eq]
    exact P256.Proofs.SignatureFromDer.encodeFixed_size value

end P256.Proofs.SignatureFromSlice.Wrapper
