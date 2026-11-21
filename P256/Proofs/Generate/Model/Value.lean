import P256.Proofs.Generate.Model.Trace
import P256.Proofs.SecretKeyFromBytes.Model
import P256.Proofs.PublicPoint.Encoding

set_option autoImplicit false

namespace P256.Proofs.Generate

open P256.Spec

theorem decodeSecret_some_iff {bytes : ByteArray} {d : Nat} :
    Standards.SECG.ECC.Keys.decodeSecret Operations.domain bytes = some d ↔
      bytes.size = 32 ∧ 0 < d ∧ d < Operations.domain.n ∧ Arith.uint bytes = d := by
  change Keys.secretOfBytes bytes = some d ↔ _
  rw [SecretKeyFromBytes.secretOfBytes_eq]
  by_cases valid : bytes.size = 32 ∧ 0 < Arith.uint bytes ∧ Arith.uint bytes < Operations.domain.n
  · rw [ite_eq_left valid]
    simp only [Option.some.injEq]
    constructor
    · intro h
      exact ⟨valid.1, h ▸ valid.2.1, h ▸ valid.2.2, h⟩
    · exact fun h => h.2.2.2
  · rw [ite_eq_right valid]
    constructor
    · intro h
      cases h
    · intro h
      apply False.elim
      apply valid
      rw [h.2.2.2]
      exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem DrawTrace.value {bytes : ByteArray} {offset d : Nat}
    (trace : DrawTrace bytes offset d) : 0 < d ∧ d < Operations.domain.n := by
  induction trace with
  | accept available decoded =>
    have result := decodeSecret_some_iff.mp decoded
    exact ⟨result.2.1, result.2.2.1⟩
  | reject available decoded trace ih => exact ih

theorem DrawTrace.encoded_value {bytes : ByteArray} {offset d : Nat}
    (trace : DrawTrace bytes offset d) :
    Arith.uint (Standards.SECG.ECC.Encoding.natToOctets 32 d) = d := by
  obtain ⟨k, bound, accepted, prior⟩ := trace.terminal
  obtain ⟨size, positive, below, decoded⟩ := decodeSecret_some_iff.mp accepted
  have encoded : Standards.SECG.ECC.Encoding.natToOctets 32 d =
      bytes.extract (offset + 32*k) (offset + 32*(k+1)) := by
    have result := SecretKeyFromBytes.Encoding.natToOctets_octetsToNat
      (bytes.extract (offset + 32*k) (offset + 32*(k+1)))
    change Standards.SECG.ECC.Encoding.natToOctets
      (bytes.extract (offset + 32*k) (offset + 32*(k+1))).size
      (Arith.uint (bytes.extract (offset + 32*k) (offset + 32*(k+1)))) = _ at result
    rw [size, decoded] at result
    exact result
  rw [encoded]
  exact decoded

theorem generated_scalar_eq {bytes : ByteArray} {d : Nat}
    (accepted : Ecdh.drawNonzeroScalar bytes = some d) :
    Spec.Generate.generatedNonZeroScalar #[bytes] = Standards.SECG.ECC.Encoding.natToOctets 32 d := by
  change ((Ecdh.drawNonzeroScalar bytes).map (Standards.SECG.ECC.Encoding.natToOctets 32)).getD _ = _
  rw [accepted]
  rfl

theorem generated_key_eq {bytes : ByteArray} {d : Nat}
    (accepted : Ecdh.drawNonzeroScalar bytes = some d) :
    Spec.Generate.generatedSigningKey #[bytes] =
      Standards.SECG.ECC.Encoding.natToOctets 32 d ++
        Sec1Serialize.encodedPoint (Points.mul d Operations.domain.G) := by
  have trace := draw_some_iff_trace.mp accepted
  obtain ⟨positive, bound⟩ := trace.value
  rw [Spec.Generate.generatedSigningKey, generated_scalar_eq accepted]
  congr 1
  have enc := PublicPoint.publicKeyOfSecret_encoding
    (Standards.SECG.ECC.Encoding.natToOctets 32 d)
    (by rw [trace.encoded_value]; exact positive)
    (by rw [trace.encoded_value]; exact bound)
  rw [trace.encoded_value] at enc
  exact enc.symm

theorem generated_key_size {bytes : ByteArray} {d : Nat}
    (accepted : Ecdh.drawNonzeroScalar bytes = some d) :
    (Spec.Generate.generatedSigningKey #[bytes]).size = 97 := by
  have trace := draw_some_iff_trace.mp accepted
  obtain ⟨positive, bound⟩ := trace.value
  rw [generated_key_eq accepted, ByteArray.size_append,
    SecretKeyFromBytes.Encoding.natToOctets_size,
    PublicPoint.encodedPoint_publicPoint d positive bound,
    PublicPoint.publicPoint_encoding_size d positive bound]

theorem arguments_iff (bytes : ByteArray) :
    Program.Routines.signingKeyGenerateFromRng.arguments #[bytes] = true ↔
      ∃ d, DrawTrace bytes 0 d := by
  change (Ecdh.drawNonzeroScalar bytes).isSome = true ↔ _
  rw [Option.isSome_iff_exists]
  exact exists_congr fun d => draw_some_iff_trace

end P256.Proofs.Generate
