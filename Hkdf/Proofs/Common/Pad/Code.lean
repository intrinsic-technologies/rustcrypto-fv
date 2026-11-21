import Hkdf.Proofs.Common.Pad.Layout

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine

structure LayoutValid (v : Variant) : Prop where
  first : (layout v).first ≤ 3
  initial : (layout v).positions[0] = 0
  positions : ∀ i : Fin 5, (layout v).positions[i] ≤ (layout v).positions[4]
  next : ∀ i : Fin 4,
    (layout v).positions[i.val + 1] = (layout v).positions[i.val] + v.xorLength i
  displacement : ∀ i : Fin 4,
    (layout v).displacement[i].value + BitVec.ofNat 64 (layout v).first =
      BitVec.ofNat 64 ((layout v).bufferOffset + i.val)
  bound : (layout v).offset + (layout v).positions[4] + 10 < 115149
  branch : branchTarget v.branchPC 2 ((layout v).branchDisp.signExtend 64) = v.entry
  xorCode : ∀ i : Fin 4,
    Extracted.textBytes.toListFrom ((layout v).offset + (layout v).positions[i.val])
      (v.xorBytes i).length = v.xorBytes i
  addCode : Extracted.textBytes.toListFrom
    ((layout v).offset + (layout v).positions[4]) 4 = [0x48, 0x83, 0xc0, 4]
  cmpCode : Extracted.textBytes.toListFrom
    ((layout v).offset + (layout v).positions[4] + 4) 4 =
      [0x48, 0x83, 0xf8, UInt8.ofNat ((layout v).first + 64)]
  branchCode : Extracted.textBytes.toListFrom
    ((layout v).offset + (layout v).positions[4] + 8) 2 =
      [0x75, UInt8.ofBitVec (layout v).branchDisp]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem layout_valid (v : Variant) : LayoutValid v := by
  cases v <;> constructor <;> decide +kernel

end Hkdf.Proofs.Common.Pad
