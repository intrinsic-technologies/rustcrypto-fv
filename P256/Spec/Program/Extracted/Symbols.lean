/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import X86.UserProcess.CodeImage

namespace P256.Spec.Program.Extracted

/-- The link-time address of the symbol `p256_ecdh_diffie_hellman` -/
def ecdhDiffieHellmanAddress : BitVec 64 := 0x1067c0

/-- No stack budget estimated for the symbol `p256_ecdh_diffie_hellman`: stack allocation in a loop at 0x11999d -/
def ecdhDiffieHellmanStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_projective_point_add` -/
def projectivePointAddAddress : BitVec 64 := 0x10b370

/-- No stack budget estimated for the symbol `p256_projective_point_add`: stack allocation in a loop at 0x11999d -/
def projectivePointAddStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_public_key_from_sec1_bytes` -/
def publicKeyFromSec1BytesAddress : BitVec 64 := 0x1017d0

/-- No stack budget estimated for the symbol `p256_public_key_from_sec1_bytes`: stack allocation in a loop at 0x11999d -/
def publicKeyFromSec1BytesStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_public_key_to_sec1_bytes` -/
def publicKeyToSec1BytesAddress : BitVec 64 := 0x101900

/-- No stack budget estimated for the symbol `p256_public_key_to_sec1_bytes`: recursive call through 0x1198bc -/
def publicKeyToSec1BytesStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_secret_key_from_bytes` -/
def secretKeyFromBytesAddress : BitVec 64 := 0x1019f0

/-- An estimated stack budget for the symbol `p256_secret_key_from_bytes`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def secretKeyFromBytesStackBytes : Option Nat := some 560

/-- The link-time address of the symbol `p256_secret_key_public_key` -/
def secretKeyPublicKeyAddress : BitVec 64 := 0x101d10

/-- No stack budget estimated for the symbol `p256_secret_key_public_key`: stack allocation in a loop at 0x11999d -/
def secretKeyPublicKeyStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_signature_from_der` -/
def signatureFromDerAddress : BitVec 64 := 0x1020f0

/-- No stack budget estimated for the symbol `p256_signature_from_der`: unresolved call or branch at 0x102172 -/
def signatureFromDerStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_signature_from_slice` -/
def signatureFromSliceAddress : BitVec 64 := 0x102220

/-- No stack budget estimated for the symbol `p256_signature_from_slice`: unresolved call or branch at 0x1022a2 -/
def signatureFromSliceStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_signing_key_generate_from_rng` -/
def signingKeyGenerateFromRngAddress : BitVec 64 := 0x106d30

/-- No stack budget estimated for the symbol `p256_signing_key_generate_from_rng`: stack allocation in a loop at 0x11999d -/
def signingKeyGenerateFromRngStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_signing_key_try_sign` -/
def signingKeyTrySignAddress : BitVec 64 := 0x102350

/-- No stack budget estimated for the symbol `p256_signing_key_try_sign`: unresolved call or branch at 0x10d370 -/
def signingKeyTrySignStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_verifying_key_from_public_key_der` -/
def verifyingKeyFromPublicKeyDerAddress : BitVec 64 := 0x102ba0

/-- No stack budget estimated for the symbol `p256_verifying_key_from_public_key_der`: stack allocation in a loop at 0x11999d -/
def verifyingKeyFromPublicKeyDerStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_verifying_key_recover_from_msg` -/
def verifyingKeyRecoverFromMsgAddress : BitVec 64 := 0x102cd0

/-- No stack budget estimated for the symbol `p256_verifying_key_recover_from_msg`: unresolved call or branch at 0x102f33 -/
def verifyingKeyRecoverFromMsgStackBytes : Option Nat := none

/-- The link-time address of the symbol `p256_verifying_key_verify` -/
def verifyingKeyVerifyAddress : BitVec 64 := 0x103010

/-- No stack budget estimated for the symbol `p256_verifying_key_verify`: unresolved call or branch at 0x103207 -/
def verifyingKeyVerifyStackBytes : Option Nat := none

end P256.Spec.Program.Extracted
