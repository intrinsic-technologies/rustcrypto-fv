/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import X86.UserProcess.CodeImage

namespace AesGcm.Spec.Program.Extracted

/-- The link-time address of the symbol `aes128gcm_decrypt_in_place` -/
def aes128gcmDecryptInPlaceAddress : BitVec 64 := 0x101240

/-- An estimated stack budget for the symbol `aes128gcm_decrypt_in_place`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def aes128gcmDecryptInPlaceStackBytes : Option Nat := some 2976

/-- The link-time address of the symbol `aes128gcm_decrypt_inout_detached` -/
def aes128gcmDecryptInoutDetachedAddress : BitVec 64 := 0x1012f0

/-- An estimated stack budget for the symbol `aes128gcm_decrypt_inout_detached`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def aes128gcmDecryptInoutDetachedStackBytes : Option Nat := some 2976

/-- The link-time address of the symbol `aes128gcm_encrypt_in_place` -/
def aes128gcmEncryptInPlaceAddress : BitVec 64 := 0x101380

/-- An estimated stack budget for the symbol `aes128gcm_encrypt_in_place`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def aes128gcmEncryptInPlaceStackBytes : Option Nat := some 2976

/-- The link-time address of the symbol `aes128gcm_encrypt_inout_detached` -/
def aes128gcmEncryptInoutDetachedAddress : BitVec 64 := 0x101470

/-- An estimated stack budget for the symbol `aes128gcm_encrypt_inout_detached`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def aes128gcmEncryptInoutDetachedStackBytes : Option Nat := some 2976

/-- The link-time address of the symbol `aes256gcm_decrypt_in_place` -/
def aes256gcmDecryptInPlaceAddress : BitVec 64 := 0x101520

/-- An estimated stack budget for the symbol `aes256gcm_decrypt_in_place`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def aes256gcmDecryptInPlaceStackBytes : Option Nat := some 3632

/-- The link-time address of the symbol `aes256gcm_decrypt_inout_detached` -/
def aes256gcmDecryptInoutDetachedAddress : BitVec 64 := 0x1015d0

/-- An estimated stack budget for the symbol `aes256gcm_decrypt_inout_detached`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def aes256gcmDecryptInoutDetachedStackBytes : Option Nat := some 3632

/-- The link-time address of the symbol `aes256gcm_encrypt_in_place` -/
def aes256gcmEncryptInPlaceAddress : BitVec 64 := 0x101660

/-- An estimated stack budget for the symbol `aes256gcm_encrypt_in_place`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def aes256gcmEncryptInPlaceStackBytes : Option Nat := some 3632

/-- The link-time address of the symbol `aes256gcm_encrypt_inout_detached` -/
def aes256gcmEncryptInoutDetachedAddress : BitVec 64 := 0x101750

/-- An estimated stack budget for the symbol `aes256gcm_encrypt_inout_detached`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def aes256gcmEncryptInoutDetachedStackBytes : Option Nat := some 3632

end AesGcm.Spec.Program.Extracted
