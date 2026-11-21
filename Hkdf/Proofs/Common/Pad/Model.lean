import Hkdf.Proofs.Common.HMAC

namespace Hkdf.Proofs.Common.Pad

open Hkdf.Proofs.Common.HMAC

theorem xorPad_xorPad (block : ByteArray) (left right : UInt8) :
    xorPad (xorPad block left) right = xorPad block (left ^^^ right) := by
  apply ByteArray.ext
  simp only [xorPad, Array.map_map]
  congr 1
  funext byte
  exact UInt8.xor_assoc byte left right

theorem xorPad_inner_to_outer (block : ByteArray) :
    xorPad (xorPad block 0x36) 0x6a = xorPad block 0x5c := by
  rw [xorPad_xorPad]
  rfl

theorem xorPad_outer_to_inner (block : ByteArray) :
    xorPad (xorPad block 0x5c) 0x6a = xorPad block 0x36 := by
  rw [xorPad_xorPad]
  rfl

theorem xorPad_zero (block : ByteArray) : xorPad block 0 = block := by
  apply ByteArray.ext
  simp only [xorPad, UInt8.xor_zero, Array.map_id_fun', id_eq]

theorem xorPad_involutive (block : ByteArray) (pad : UInt8) :
    xorPad (xorPad block pad) pad = block := by
  rw [xorPad_xorPad, UInt8.xor_self, xorPad_zero]

end Hkdf.Proofs.Common.Pad
