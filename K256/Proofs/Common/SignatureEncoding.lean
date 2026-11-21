import K256.Proofs.Common.Encoding
import K256.Spec.Ecdsa

namespace K256.Proofs.Common

open K256.Spec Standards.SECG.ECC

theorem signatureBytes_of_signatureScalars {bytes : ByteArray} {r s : Nat}
    (h : Ecdsa.signatureScalars bytes = some (r, s)) :
    Ecdsa.signatureBytes r s = bytes := by
  unfold Ecdsa.signatureScalars at h
  dsimp only at h
  split at h
  next valid =>
    cases h
    obtain ⟨length, _⟩ := valid
    have first := Encoding.natToOctets_octetsToNat (bytes.extract 0 32)
    have last := Encoding.natToOctets_octetsToNat (bytes.extract 32 64)
    simp only [ByteArray.size_extract, length] at first last
    change Standards.SECG.ECC.Encoding.natToOctets 32 _ = _ at first last
    unfold Ecdsa.signatureBytes
    rw [first, last, ByteArray.extract_append_extract]
    show bytes.extract 0 64 = bytes
    rw [← length, ByteArray.extract_zero_size]
  next => contradiction

end K256.Proofs.Common
