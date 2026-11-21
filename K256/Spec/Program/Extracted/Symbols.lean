/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import X86.UserProcess.CodeImage

namespace K256.Spec.Program.Extracted

/-- The link-time address of the symbol `k256_ecdh_diffie_hellman` -/
def ecdhDiffieHellmanAddress : BitVec 64 := 0x101660

/-- No stack budget estimated for the symbol `k256_ecdh_diffie_hellman`: unresolved call or branch at 0x128e6d -/
def ecdhDiffieHellmanStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_projective_point_add` -/
def projectivePointAddAddress : BitVec 64 := 0x101c70

/-- No stack budget estimated for the symbol `k256_projective_point_add`: unresolved call or branch at 0x128e6d -/
def projectivePointAddStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_public_key_from_sec1_bytes` -/
def publicKeyFromSec1BytesAddress : BitVec 64 := 0x101dd0

/-- No stack budget estimated for the symbol `k256_public_key_from_sec1_bytes`: unresolved call or branch at 0x128e6d -/
def publicKeyFromSec1BytesStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_public_key_to_sec1_bytes` -/
def publicKeyToSec1BytesAddress : BitVec 64 := 0x101e70

/-- No stack budget estimated for the symbol `k256_public_key_to_sec1_bytes`: unresolved call or branch at 0x101f60 -/
def publicKeyToSec1BytesStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_schnorr_sign_raw` -/
def schnorrSignRawAddress : BitVec 64 := 0x101ee0

/-- No stack budget estimated for the symbol `k256_schnorr_sign_raw`: unresolved call or branch at 0x101f60 -/
def schnorrSignRawStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_schnorr_verify_raw` -/
def schnorrVerifyRawAddress : BitVec 64 := 0x102020

/-- No stack budget estimated for the symbol `k256_schnorr_verify_raw`: unresolved call or branch at 0x1020bb -/
def schnorrVerifyRawStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_secret_key_from_bytes` -/
def secretKeyFromBytesAddress : BitVec 64 := 0x1020f0

/-- An estimated stack budget for the symbol `k256_secret_key_from_bytes`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def secretKeyFromBytesStackBytes : Option Nat := some 560

/-- The link-time address of the symbol `k256_secret_key_from_sec1_der` -/
def secretKeyFromSec1DerAddress : BitVec 64 := 0x1021a0

/-- No stack budget estimated for the symbol `k256_secret_key_from_sec1_der`: stack allocation in a loop at 0x109240 -/
def secretKeyFromSec1DerStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_secret_key_public_key` -/
def secretKeyPublicKeyAddress : BitVec 64 := 0x102240

/-- No stack budget estimated for the symbol `k256_secret_key_public_key`: unresolved call or branch at 0x1023d5 -/
def secretKeyPublicKeyStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_signature_from_der` -/
def signatureFromDerAddress : BitVec 64 := 0x1023a0

/-- No stack budget estimated for the symbol `k256_signature_from_der`: unresolved call or branch at 0x1023d5 -/
def signatureFromDerStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_signature_from_slice` -/
def signatureFromSliceAddress : BitVec 64 := 0x102450

/-- No stack budget estimated for the symbol `k256_signature_from_slice`: unresolved call or branch at 0x1024fb -/
def signatureFromSliceStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_signing_key_generate_from_rng` -/
def signingKeyGenerateFromRngAddress : BitVec 64 := 0x102510

/-- No stack budget estimated for the symbol `k256_signing_key_generate_from_rng`: stack allocation in a loop at 0x109240 -/
def signingKeyGenerateFromRngStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_signing_key_try_sign` -/
def signingKeyTrySignAddress : BitVec 64 := 0x102630

/-- No stack budget estimated for the symbol `k256_signing_key_try_sign`: unresolved call or branch at 0x1027b3 -/
def signingKeyTrySignStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_verifying_key_recover_from_prehash` -/
def verifyingKeyRecoverFromPrehashAddress : BitVec 64 := 0x1028b0

/-- No stack budget estimated for the symbol `k256_verifying_key_recover_from_prehash`: unresolved call or branch at 0x10019d -/
def verifyingKeyRecoverFromPrehashStackBytes : Option Nat := none

/-- The link-time address of the symbol `k256_verifying_key_verify` -/
def verifyingKeyVerifyAddress : BitVec 64 := 0x102fc0

/-- No stack budget estimated for the symbol `k256_verifying_key_verify`: unresolved call or branch at 0x1033f4 -/
def verifyingKeyVerifyStackBytes : Option Nat := none

end K256.Spec.Program.Extracted
