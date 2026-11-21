import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part01 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1096db 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1096dd 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1096df 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1096e1 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1096e4 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1096e7 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1096ea 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x1096ec 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1096ee 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1096f6 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1096f9 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x1096fb 6 (.sib 1 (some 7) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1096fe 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109700 0xc7 0x71374491 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109706 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109708 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10970b 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10970e 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109712 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109715 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109718 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10971c 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10971f 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109722 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109725 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109727 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10972a 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109732 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109734 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109737 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10973a 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10973c 0x45 (by simp [RexNoWPrefix]) 0 (.sib 14 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x109740 0x41 0xc0 0x71374491 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109747 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10974a 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10974d 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109750 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109753 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109755 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109758 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10975b 0xfe rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10975d 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x109762 0x44 (by simp [RexNoWPrefix]) 1 (.base 7 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109766 9) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109769 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10976e 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109771 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109773 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109776 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109779 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x10977c 0x41 0xd1 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10977f 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109787 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10978a 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10978d 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109790 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109794 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109797 0x41 0xc2 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10979b 0x44 (by simp [RexNoWPrefix]) 3 (.sib 7 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10979f 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x1097a1 0xc7 0xb5c0fbcf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1097a7 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1097aa 0xcb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1097ac 0xc3 0xa rfl rfl) (by x86_local)]

def part01Bytes : List UInt8 :=
  [0x31,0xce,0x31,0xf7,0x89,0xd1,0x44,0x21,0xe1,0x44,0x1,0xc9,0x44,0x1,0xe9,0x89,0xd6,0xf7,0xd6,0x4c,0x89,0x94,0x24,0x0,0x1,0x0,0x0,0x44,0x21,0xd6,0x1,0xf1,0x8d,0x34,0x39,0x1,0xcf,0x81,0xc7,0x91,0x44,0x37,0x71,0x89,0xc1,0xc1,0xc1,0x1e,0x41,0x89,0xc0,0x41,0xc1,0xc0,0x13,0x41,0x31,0xc8,0x41,0x89,0xc1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xc1,0x41,0x89,0xd8,0x45,0x21,0xf8,0x89,0xd9,0x44,0x31,0xf9,0x4c,0x89,0xbc,0x24,0xf8,0x0,0x0,0x0,0x21,0xc1,0x44,0x31,0xc1,0x44,0x1,0xc9,0x1,0xf9,0x45,0x8d,0x4,0x36,0x41,0x81,0xc0,0x91,0x44,0x37,0x71,0x44,0x89,0xc6,0xc1,0xc6,0x1a,0x44,0x89,0xc7,0xc1,0xc7,0x15,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xc6,0x7,0x31,0xfe,0x48,0x8b,0x7c,0x24,0x18,0x44,0x8b,0x4f,0x8,0x41,0xf,0xc9,0x4c,0x89,0x4c,0x24,0x68,0x44,0x89,0xc7,0x21,0xd7,0x45,0x1,0xd1,0x44,0x1,0xcf,0x45,0x89,0xc1,0x41,0xf7,0xd1,0x4c,0x89,0xa4,0x24,0xf0,0x0,0x0,0x0,0x45,0x21,0xe1,0x44,0x1,0xcf,0x41,0x89,0xc9,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xca,0x41,0xc1,0xc2,0x13,0x44,0x8d,0x1c,0x37,0x1,0xf7,0x81,0xc7,0xcf,0xfb,0xc0,0xb5,0x48,0x89,0xde,0x89,0xcb,0xc1,0xc3,0xa]

set_option maxRecDepth 4096 in
theorem part01_bytes [Bindings] : part01.flatMap CheckedInstruction.bytes = part01Bytes  := by
  rfl

def part01Layout : List (BitVec 64 × Nat) :=
  [(0x1096db, 2), (0x1096dd, 2), (0x1096df, 2), (0x1096e1, 3), (0x1096e4, 3), (0x1096e7, 3), (0x1096ea, 2), (0x1096ec, 2), (0x1096ee, 8), (0x1096f6, 3), (0x1096f9, 2), (0x1096fb, 3), (0x1096fe, 2), (0x109700, 6), (0x109706, 2), (0x109708, 3), (0x10970b, 3), (0x10970e, 4), (0x109712, 3), (0x109715, 3), (0x109718, 4), (0x10971c, 3), (0x10971f, 3), (0x109722, 3), (0x109725, 2), (0x109727, 3), (0x10972a, 8), (0x109732, 2), (0x109734, 3), (0x109737, 3), (0x10973a, 2), (0x10973c, 4), (0x109740, 7), (0x109747, 3), (0x10974a, 3), (0x10974d, 3), (0x109750, 3), (0x109753, 2), (0x109755, 3), (0x109758, 3), (0x10975b, 2), (0x10975d, 5), (0x109762, 4), (0x109766, 3), (0x109769, 5), (0x10976e, 3), (0x109771, 2), (0x109773, 3), (0x109776, 3), (0x109779, 3), (0x10977c, 3), (0x10977f, 8), (0x109787, 3), (0x10978a, 3), (0x10978d, 3), (0x109790, 4), (0x109794, 3), (0x109797, 4), (0x10979b, 4), (0x10979f, 2), (0x1097a1, 6), (0x1097a7, 3), (0x1097aa, 2), (0x1097ac, 3)]

theorem part01_layout [Bindings] : InstructionTrace.layout part01 = part01Layout := by
  rfl

theorem part01_ordered [Bindings] : InstructionTrace.ordered 0x1096db part01 = true := by
  rw [InstructionTrace.ordered_eq_layout, part01_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part01_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x96db 212 = part01Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
