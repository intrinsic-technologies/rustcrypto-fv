/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import X86.UserProcess.CodeImage

namespace ChaCha20Poly1305.Spec.Program.Extracted

/-- The link-time address of the symbol `chacha20poly1305_decrypt` -/
def decryptAddress : BitVec 64 := 0x1014c0

/-- No stack budget estimated for the symbol `chacha20poly1305_decrypt`: unresolved call or branch at 0x10267e -/
def decryptStackBytes : Option Nat := none

/-- The link-time address of the symbol `chacha20poly1305_decrypt_in_place` -/
def decryptInPlaceAddress : BitVec 64 := 0x101650

/-- No stack budget estimated for the symbol `chacha20poly1305_decrypt_in_place`: unresolved call or branch at 0x10267e -/
def decryptInPlaceStackBytes : Option Nat := none

/-- The link-time address of the symbol `chacha20poly1305_decrypt_inout_detached` -/
def decryptInoutDetachedAddress : BitVec 64 := 0x1016d0

/-- No stack budget estimated for the symbol `chacha20poly1305_decrypt_inout_detached`: unresolved call or branch at 0x10267e -/
def decryptInoutDetachedStackBytes : Option Nat := none

/-- The link-time address of the symbol `chacha20poly1305_encrypt` -/
def encryptAddress : BitVec 64 := 0x101740

/-- No stack budget estimated for the symbol `chacha20poly1305_encrypt`: recursive call through 0x10207c -/
def encryptStackBytes : Option Nat := none

/-- The link-time address of the symbol `chacha20poly1305_encrypt_in_place` -/
def encryptInPlaceAddress : BitVec 64 := 0x101930

/-- No stack budget estimated for the symbol `chacha20poly1305_encrypt_in_place`: unresolved call or branch at 0x10267e -/
def encryptInPlaceStackBytes : Option Nat := none

/-- The link-time address of the symbol `chacha20poly1305_encrypt_inout_detached` -/
def encryptInoutDetachedAddress : BitVec 64 := 0x101a00

/-- No stack budget estimated for the symbol `chacha20poly1305_encrypt_inout_detached`: unresolved call or branch at 0x10267e -/
def encryptInoutDetachedStackBytes : Option Nat := none

end ChaCha20Poly1305.Spec.Program.Extracted
