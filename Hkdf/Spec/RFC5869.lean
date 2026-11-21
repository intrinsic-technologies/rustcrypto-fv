import Standards.RFC.HKDF

/-!
# HKDF as `hkdf` 0.13.0 computes it

The crate's operations, built on RFC 5869 in `Standards.RFC.HKDF`: its optional salt, the
`at least HashLen octets` rule for a PRK that `from_prk` checks, the `255 * HashLen` limit of
`expand_multi_info`, and the errors it reports, with one error type per operation. Each function
takes the hash as a parameter; the entry points instantiate `Standards.RFC.HKDF.Hash.sha256`.

Source: https://www.rfc-editor.org/rfc/rfc5869.html
-/

namespace Hkdf.Spec.RFC5869

open Standards.RFC

/--
The errors of `GenericHkdf::from_prk` followed by `expand_multi_info`, the crate's
`InvalidPrkLength` and `InvalidLength`
-/
inductive ExpandError where
  /-- `InvalidPrkLength`, which `from_prk` returns for a PRK shorter than `HashLen` octets -/
  | invalidPrkLength
  /-- `InvalidLength`, which `expand_multi_info` returns above `255 * HashLen` output octets -/
  | invalidLength
  deriving DecidableEq, Repr

/--
The salt HKDF-Extract uses when none is provided, a string of `HashLen` zeros (RFC 5869, §2.2); the
crate's `Output::<H>::default()`
-/
def defaultSalt (H : HKDF.Hash) : ByteArray := ⟨Array.replicate H.hashLen 0⟩

/--
HKDF-Extract with an optional salt (RFC 5869, §2.2): `PRK = HMAC-Hash(salt, IKM)`, with
`defaultSalt` when `salt` is `none`. It is what `GenericHkdfExtract::new(salt)`, `input_ikm`
over parts whose concatenation is `ikm`, and `finalize` return as the PRK.
-/
def extract (H : HKDF.Hash) (salt : Option ByteArray) (ikm : ByteArray) : ByteArray :=
  HKDF.extract H (salt.getD (defaultSalt H)) ikm

/--
`GenericHkdf::from_prk` followed by `expand_multi_info` with info components whose
concatenation is `info` and an output of `okmLength` octets: `InvalidPrkLength` for a PRK shorter
than `HashLen` octets (RFC 5869, §2.3: "a pseudorandom key of at least HashLen octets"), checked
first, then `InvalidLength` above `255 * HashLen` octets, and otherwise HKDF-Expand (§2.3)
-/
def expandFromPrk (H : HKDF.Hash) (prk info : ByteArray) (okmLength : Nat) :
    Except ExpandError ByteArray :=
  if prk.size < H.hashLen then .error .invalidPrkLength else
  match HKDF.expand H prk info okmLength with
  | some okm => .ok okm
  | none => .error .invalidLength

end Hkdf.Spec.RFC5869
