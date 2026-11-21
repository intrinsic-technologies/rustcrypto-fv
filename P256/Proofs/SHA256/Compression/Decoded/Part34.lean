import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part34 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1173f8 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173fb 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1173fe 0x41 0xc0 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117402 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117405 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117408 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11740b 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11740e 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117411 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117414 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117417 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11741a 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11741e 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117421 0xc1 0xa2bfe8a1 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117427 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11742a 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11742e 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117431 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117434 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117438 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11743b 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11743e 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117441 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117443 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117445 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117448 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11744b 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11744e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117450 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117453 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117457 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117459 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11745b 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11745e 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117461 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117464 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117468 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11746b 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11746f 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117472 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x117475 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117479 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x11747c 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117480 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x117483 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117488 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x11748b 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11748f 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117492 5 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117495 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117498 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11749a 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11749d 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1174a0 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1174a4 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1174a7 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1174a9 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1174ac 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1174af 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1174b2 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1174b5 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1174b8 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1174bb 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1174be 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part34Bytes : List UInt8 :=
  [0x45,0x31,0xc1,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x7,0x45,0x31,0xc8,0x45,0x89,0xf1,0x45,0x31,0xd1,0x41,0x21,0xf9,0x45,0x31,0xd1,0x44,0x1,0xe1,0x44,0x1,0xc9,0x45,0x89,0xd9,0x41,0xc1,0xc1,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xa1,0xe8,0xbf,0xa2,0x45,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x45,0x31,0xc8,0x45,0x89,0xd9,0x41,0xc1,0xc1,0xa,0x45,0x31,0xc1,0x41,0x89,0xd0,0x41,0x21,0xf0,0x89,0xd3,0x31,0xf3,0x44,0x21,0xdb,0x44,0x31,0xc3,0x44,0x1,0xcb,0x1,0xc8,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xf,0x1,0xcb,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc1,0x45,0x89,0xe0,0x41,0xc1,0xc0,0x19,0x45,0x89,0xe1,0x41,0xc1,0xc1,0xe,0x45,0x31,0xc1,0x45,0x89,0xe0,0x41,0xc1,0xe8,0x3,0x45,0x31,0xc8,0x1,0x6c,0x24,0x4,0x41,0x1,0xe8,0x44,0x89,0x44,0x24,0x70,0x41,0x89,0xe8,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x8b,0x2c,0x24,0x44,0x1,0xc5,0x89,0xc1,0xc1,0xc1,0x1a,0x41,0x89,0xc0,0x41,0xc1,0xc0,0x15,0x41,0x31,0xc8,0x89,0xc1,0xc1,0xc1,0x7,0x44,0x31,0xc1,0x41,0x89,0xf8,0x45,0x31,0xf0,0x41,0x21,0xc0,0x45,0x31,0xf0,0x41,0x1,0xea,0x41,0x89,0xd9]

set_option maxRecDepth 4096 in
theorem part34_bytes [Bindings] : part34.flatMap CheckedInstruction.bytes = part34Bytes  := by
  rfl

def part34Layout : List (BitVec 64 × Nat) :=
  [(0x1173f8, 3), (0x1173fb, 3), (0x1173fe, 4), (0x117402, 3), (0x117405, 3), (0x117408, 3), (0x11740b, 3), (0x11740e, 3), (0x117411, 3), (0x117414, 3), (0x117417, 3), (0x11741a, 4), (0x11741e, 3), (0x117421, 6), (0x117427, 3), (0x11742a, 4), (0x11742e, 3), (0x117431, 3), (0x117434, 4), (0x117438, 3), (0x11743b, 3), (0x11743e, 3), (0x117441, 2), (0x117443, 2), (0x117445, 3), (0x117448, 3), (0x11744b, 3), (0x11744e, 2), (0x117450, 3), (0x117453, 4), (0x117457, 2), (0x117459, 2), (0x11745b, 3), (0x11745e, 3), (0x117461, 3), (0x117464, 4), (0x117468, 3), (0x11746b, 4), (0x11746f, 3), (0x117472, 3), (0x117475, 4), (0x117479, 3), (0x11747c, 4), (0x117480, 3), (0x117483, 5), (0x117488, 3), (0x11748b, 4), (0x11748f, 3), (0x117492, 3), (0x117495, 3), (0x117498, 2), (0x11749a, 3), (0x11749d, 3), (0x1174a0, 4), (0x1174a4, 3), (0x1174a7, 2), (0x1174a9, 3), (0x1174ac, 3), (0x1174af, 3), (0x1174b2, 3), (0x1174b5, 3), (0x1174b8, 3), (0x1174bb, 3), (0x1174be, 3)]

theorem part34_layout [Bindings] : InstructionTrace.layout part34 = part34Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part34_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x173f8 201 = part34Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
