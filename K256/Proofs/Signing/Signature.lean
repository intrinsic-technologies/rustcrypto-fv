import K256.Proofs.Signing.SearchBound

namespace K256.Proofs.Signing
open K256.Spec Standards.SECG.ECC Standards.SECG.DomainParameters

private theorem normalize_found (message : ByteArray) (cap : Nat) (key : Option Nat) (d r s : Nat) :
    key = some d → Ecdsa.signatureWithin d message cap = some (r,s) →
    Ecdsa.signature.match_3 (fun _ => ByteArray) key (fun _ => ByteArray.empty)
      (fun x => Ecdsa.signature.match_1 (fun _ => ByteArray) (Ecdsa.signatureWithin x message cap)
        (fun a b => Ecdsa.normalizeS a b) (fun _ => ByteArray.empty)) = Ecdsa.normalizeS r s := by
  rintro rfl found
  change Ecdsa.signature.match_1 _ (Ecdsa.signatureWithin d message cap) _ _ = _
  rw [found]

theorem signature_of_found {secret message : ByteArray} {d r s attempts : Nat}
    (key : Keys.decodeSecret Secp256k1.domain secret = some d)
    (found : Ecdsa.signatureWithin d message attempts = some (r, s)) :
    Ecdsa.signature secret message = Ecdsa.normalizeS r s := by
  unfold Ecdsa.signature
  have result := normalize_found message (2 ^ 512) _ d r s key
    (@signatureWithin_bound d attempts message (r, s) found)
  exact result

end K256.Proofs.Signing
