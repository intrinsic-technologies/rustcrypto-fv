import Hkdf.Proofs.Common.HMAC
import Hkdf.Proofs.Common.CallFrame
import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Layout where
  offset : Nat
  displacement : Vector Disp 4
  positions : Vector Nat 5
  first : Nat
  bufferOffset : Nat
  mask : UInt8
  branchDisp : BitVec 8

inductive Variant where
  | v100070
  | v1000e0
  | v100270
  | v1002e0
  | v1004a0
  | v100510
  | v1008c0
  | v100930
  | v100c50
  | v100cc0
  | v101050
  | v1010d0
  | v101270
  | v1012f0
  | v1014a0
  | v101510
  | v101920
  | v101990
  | v101ce0
  | v101d50
  | v104780
  | v104810
  | v104940
  | v1049c0
  | v104b00
  | v104b90
  | v104de0
  | v104e60
  | v105020
  | v1050b0
  | v105320
  | v1053b0
  | v105550
  | v1055e0
  | v105930
  | v1059d0
  | v105b00
  | v105b90
  | v105d00
  | v105d90
  | v106000
  | v106090
  | v106280
  | v106310
  | v106580
  | v106610
  | v1067b0
  | v106850
  | v10e0d0
  | v10e160
  | v10f0b0
  | v10f120
  | v10faf0
  | v10fb70
  | v111b10
  | v111b80
  | v1122e0
  | v112390
  | v1125c0
  | v112660
  | v1143b0
  | v114440
  | v1146f0
  | v114770
  | v1153f0
  | v115490
  | v116180
  | v116210
  deriving DecidableEq

def layout : Variant → Layout
  | .v100070 => ⟨0x70, #v[.d8 0x65, .d8 0x66, .d8 0x67, .d8 0x68], #v[0, 5, 10, 15, 20], 3, 104, 0x36, 0xe2⟩
  | .v1000e0 => ⟨0xe0, #v[.d8 0x65, .d8 0x66, .d8 0x67, .d8 0x68], #v[0, 5, 10, 15, 20], 3, 104, 0x6a, 0xe2⟩
  | .v100270 => ⟨0x270, #v[.d32 0x85, .d32 0x86, .d32 0x87, .d32 0x88], #v[0, 8, 16, 24, 32], 3, 136, 0x36, 0xd6⟩
  | .v1002e0 => ⟨0x2e0, #v[.d32 0x85, .d32 0x86, .d32 0x87, .d32 0x88], #v[0, 8, 16, 24, 32], 3, 136, 0x6a, 0xd6⟩
  | .v1004a0 => ⟨0x4a0, #v[.d8 0x65, .d8 0x66, .d8 0x67, .d8 0x68], #v[0, 5, 10, 15, 20], 3, 104, 0x36, 0xe2⟩
  | .v100510 => ⟨0x510, #v[.d8 0x65, .d8 0x66, .d8 0x67, .d8 0x68], #v[0, 5, 10, 15, 20], 3, 104, 0x6a, 0xe2⟩
  | .v1008c0 => ⟨0x8c0, #v[.d8 0x45, .d8 0x46, .d8 0x47, .d8 0x48], #v[0, 5, 10, 15, 20], 3, 72, 0x36, 0xe2⟩
  | .v100930 => ⟨0x930, #v[.d8 0x45, .d8 0x46, .d8 0x47, .d8 0x48], #v[0, 5, 10, 15, 20], 3, 72, 0x6a, 0xe2⟩
  | .v100c50 => ⟨0xc50, #v[.d8 0x6d, .d8 0x6e, .d8 0x6f, .d8 0x70], #v[0, 5, 10, 15, 20], 3, 112, 0x36, 0xe2⟩
  | .v100cc0 => ⟨0xcc0, #v[.d8 0x6d, .d8 0x6e, .d8 0x6f, .d8 0x70], #v[0, 5, 10, 15, 20], 3, 112, 0x6a, 0xe2⟩
  | .v101050 => ⟨0x1050, #v[.d32 0xd5, .d32 0xd6, .d32 0xd7, .d32 0xd8], #v[0, 8, 16, 24, 32], 3, 216, 0x36, 0xd6⟩
  | .v1010d0 => ⟨0x10d0, #v[.d32 0xd5, .d32 0xd6, .d32 0xd7, .d32 0xd8], #v[0, 8, 16, 24, 32], 3, 216, 0x6a, 0xd6⟩
  | .v101270 => ⟨0x1270, #v[.d32 0xb5, .d32 0xb6, .d32 0xb7, .d32 0xb8], #v[0, 8, 16, 24, 32], 3, 184, 0x36, 0xd6⟩
  | .v1012f0 => ⟨0x12f0, #v[.d32 0xb5, .d32 0xb6, .d32 0xb7, .d32 0xb8], #v[0, 8, 16, 24, 32], 3, 184, 0x6a, 0xd6⟩
  | .v1014a0 => ⟨0x14a0, #v[.d8 0x75, .d8 0x76, .d8 0x77, .d8 0x78], #v[0, 5, 10, 15, 20], 3, 120, 0x36, 0xe2⟩
  | .v101510 => ⟨0x1510, #v[.d8 0x75, .d8 0x76, .d8 0x77, .d8 0x78], #v[0, 5, 10, 15, 20], 3, 120, 0x6a, 0xe2⟩
  | .v101920 => ⟨0x1920, #v[.d8 0x45, .d8 0x46, .d8 0x47, .d8 0x48], #v[0, 5, 10, 15, 20], 3, 72, 0x36, 0xe2⟩
  | .v101990 => ⟨0x1990, #v[.d8 0x45, .d8 0x46, .d8 0x47, .d8 0x48], #v[0, 5, 10, 15, 20], 3, 72, 0x6a, 0xe2⟩
  | .v101ce0 => ⟨0x1ce0, #v[.d8 0x75, .d8 0x76, .d8 0x77, .d8 0x78], #v[0, 5, 10, 15, 20], 3, 120, 0x36, 0xe2⟩
  | .v101d50 => ⟨0x1d50, #v[.d8 0x75, .d8 0x76, .d8 0x77, .d8 0x78], #v[0, 5, 10, 15, 20], 3, 120, 0x6a, 0xe2⟩
  | .v104780 => ⟨0x4780, #v[.d8 0xd, .d8 0xe, .d8 0xf, .d8 0x10], #v[0, 5, 10, 15, 20], 3, 16, 0x36, 0xe2⟩
  | .v104810 => ⟨0x4810, #v[.d8 0xd, .d8 0xe, .d8 0xf, .d8 0x10], #v[0, 5, 10, 15, 20], 3, 16, 0x6a, 0xe2⟩
  | .v104940 => ⟨0x4940, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x36, 0xe3⟩
  | .v1049c0 => ⟨0x49c0, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x6a, 0xe3⟩
  | .v104b00 => ⟨0x4b00, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x36, 0xe2⟩
  | .v104b90 => ⟨0x4b90, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x6a, 0xe2⟩
  | .v104de0 => ⟨0x4de0, #v[.d8 0x65, .d8 0x66, .d8 0x67, .d8 0x68], #v[0, 5, 10, 15, 20], 3, 104, 0x36, 0xe2⟩
  | .v104e60 => ⟨0x4e60, #v[.d8 0x68, .d8 0x69, .d8 0x6a, .d8 0x6b], #v[0, 5, 10, 15, 20], 0, 104, 0x6a, 0xe2⟩
  | .v105020 => ⟨0x5020, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x36, 0xe2⟩
  | .v1050b0 => ⟨0x50b0, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x6a, 0xe2⟩
  | .v105320 => ⟨0x5320, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x36, 0xe2⟩
  | .v1053b0 => ⟨0x53b0, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x6a, 0xe2⟩
  | .v105550 => ⟨0x5550, #v[.d8 0x15, .d8 0x16, .d8 0x17, .d8 0x18], #v[0, 5, 10, 15, 20], 3, 24, 0x36, 0xe2⟩
  | .v1055e0 => ⟨0x55e0, #v[.d8 0x15, .d8 0x16, .d8 0x17, .d8 0x18], #v[0, 5, 10, 15, 20], 3, 24, 0x6a, 0xe2⟩
  | .v105930 => ⟨0x5930, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x36, 0xe2⟩
  | .v1059d0 => ⟨0x59d0, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x6a, 0xe2⟩
  | .v105b00 => ⟨0x5b00, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x36, 0xe3⟩
  | .v105b90 => ⟨0x5b90, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x6a, 0xe3⟩
  | .v105d00 => ⟨0x5d00, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x36, 0xe3⟩
  | .v105d90 => ⟨0x5d90, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x6a, 0xe3⟩
  | .v106000 => ⟨0x6000, #v[.d8 0x3d, .d8 0x3e, .d8 0x3f, .d8 0x40], #v[0, 5, 10, 15, 20], 3, 64, 0x36, 0xe2⟩
  | .v106090 => ⟨0x6090, #v[.d8 0x40, .d8 0x41, .d8 0x42, .d8 0x43], #v[0, 5, 10, 15, 20], 0, 64, 0x6a, 0xe2⟩
  | .v106280 => ⟨0x6280, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x36, 0xe3⟩
  | .v106310 => ⟨0x6310, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x6a, 0xe3⟩
  | .v106580 => ⟨0x6580, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x36, 0xe3⟩
  | .v106610 => ⟨0x6610, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x6a, 0xe3⟩
  | .v1067b0 => ⟨0x67b0, #v[.d8 0xd, .d8 0xe, .d8 0xf, .d8 0x10], #v[0, 5, 10, 15, 20], 3, 16, 0x36, 0xe2⟩
  | .v106850 => ⟨0x6850, #v[.d8 0xd, .d8 0xe, .d8 0xf, .d8 0x10], #v[0, 5, 10, 15, 20], 3, 16, 0x6a, 0xe2⟩
  | .v10e0d0 => ⟨0xe0d0, #v[.d8 0x45, .d8 0x46, .d8 0x47, .d8 0x48], #v[0, 5, 10, 15, 20], 3, 72, 0x36, 0xe2⟩
  | .v10e160 => ⟨0xe160, #v[.d8 0x45, .d8 0x46, .d8 0x47, .d8 0x48], #v[0, 5, 10, 15, 20], 3, 72, 0x6a, 0xe2⟩
  | .v10f0b0 => ⟨0xf0b0, #v[.d8 0x25, .d8 0x26, .d8 0x27, .d8 0x28], #v[0, 5, 10, 15, 20], 3, 40, 0x36, 0xe2⟩
  | .v10f120 => ⟨0xf120, #v[.d8 0x25, .d8 0x26, .d8 0x27, .d8 0x28], #v[0, 5, 10, 15, 20], 3, 40, 0x6a, 0xe2⟩
  | .v10faf0 => ⟨0xfaf0, #v[.d8 0x75, .d8 0x76, .d8 0x77, .d8 0x78], #v[0, 5, 10, 15, 20], 3, 120, 0x36, 0xe2⟩
  | .v10fb70 => ⟨0xfb70, #v[.d8 0x75, .d8 0x76, .d8 0x77, .d8 0x78], #v[0, 5, 10, 15, 20], 3, 120, 0x6a, 0xe2⟩
  | .v111b10 => ⟨0x11b10, #v[.d8 0x45, .d8 0x46, .d8 0x47, .d8 0x48], #v[0, 5, 10, 15, 20], 3, 72, 0x36, 0xe2⟩
  | .v111b80 => ⟨0x11b80, #v[.d8 0x45, .d8 0x46, .d8 0x47, .d8 0x48], #v[0, 5, 10, 15, 20], 3, 72, 0x6a, 0xe2⟩
  | .v1122e0 => ⟨0x122e0, #v[.d8 0x3d, .d8 0x3e, .d8 0x3f, .d8 0x40], #v[0, 5, 10, 15, 20], 3, 64, 0x36, 0xe2⟩
  | .v112390 => ⟨0x12390, #v[.d8 0x3d, .d8 0x3e, .d8 0x3f, .d8 0x40], #v[0, 5, 10, 15, 20], 3, 64, 0x6a, 0xe2⟩
  | .v1125c0 => ⟨0x125c0, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x36, 0xe3⟩
  | .v112660 => ⟨0x12660, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x6a, 0xe3⟩
  | .v1143b0 => ⟨0x143b0, #v[.d8 0x3d, .d8 0x3e, .d8 0x3f, .d8 0x40], #v[0, 5, 10, 15, 20], 3, 64, 0x36, 0xe2⟩
  | .v114440 => ⟨0x14440, #v[.d8 0x3d, .d8 0x3e, .d8 0x3f, .d8 0x40], #v[0, 5, 10, 15, 20], 3, 64, 0x6a, 0xe2⟩
  | .v1146f0 => ⟨0x146f0, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x36, 0xe3⟩
  | .v114770 => ⟨0x14770, #v[.d8 0xfd, .d8 0xfe, .d8 0xff, .none], #v[0, 5, 10, 15, 19], 3, 0, 0x6a, 0xe3⟩
  | .v1153f0 => ⟨0x153f0, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x36, 0xe2⟩
  | .v115490 => ⟨0x15490, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x6a, 0xe2⟩
  | .v116180 => ⟨0x16180, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x36, 0xe2⟩
  | .v116210 => ⟨0x16210, #v[.d8 0x5, .d8 0x6, .d8 0x7, .d8 0x8], #v[0, 5, 10, 15, 20], 3, 8, 0x6a, 0xe2⟩

def Variant.pc (v : Variant) (index : Fin 5) : BitVec 64 :=
  Hkdf.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 ((layout v).offset + (layout v).positions[index])

def Variant.am (v : Variant) (index : Fin 4) : AddrMode :=
  .sib 4 (some 0) 0 (layout v).displacement[index]

def Variant.xorBytes (v : Variant) (index : Fin 4) : List UInt8 :=
  0x80 :: (v.am index).modrm 6 :: ((v.am index).tail ++ [(layout v).mask])

def Variant.xorLength (v : Variant) (index : Fin 4) : Nat :=
  3 + (v.am index).tail.length

def Variant.entry (v : Variant) : BitVec 64 := v.pc 0

def Variant.addPC (v : Variant) : BitVec 64 := v.pc 4

def Variant.cmpPC (v : Variant) : BitVec 64 := v.addPC + 4

def Variant.branchPC (v : Variant) : BitVec 64 := v.addPC + 8

def Variant.exit (v : Variant) : BitVec 64 := v.addPC + 10

def Variant.limit (v : Variant) : BitVec 8 := BitVec.ofNat 8 ((layout v).first + 64)

def components (pointer : BitVec 64) : List Component :=
  [.reg 0, .flags, .mem pointer 64, .rip]

end Hkdf.Proofs.Common.Pad
