import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu
import P256.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part14 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (store32_legacy_effect_step 0x1164ac 0 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x1164b3 0x41 0xeb 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_effect_step 0x1164b7 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d32 156)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1164bf 0 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1164c3 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x1164c6 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1164ca 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_legacy_effect_step 0x1164cd 0 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1164d4 2 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1164d8 0xd0 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x1164da 0 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1164de 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1164e0 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_legacy_effect_step 0x1164e3 0 (.sib 4 none 0 (.d32 164)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1164ea 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1164ed 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1164f2 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1164f4 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1164f7 0xfe rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1164f9 0xc6 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1164fc 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1164fe 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116500 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116503 0xf0 rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x116505 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11650a 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x11650d 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116512 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116515 0 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116519 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11651c 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_legacy_effect_step 0x11651f 2 (.sib 4 none 0 (.d32 180)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116526 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11652b 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11652e 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x116531 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x116534 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11653c 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11653f 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116542 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116545 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116548 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11654b 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11654d 0xc2 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11654f 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 224)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116557 0xd8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116559 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116561 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116563 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116566 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116568 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11656b 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x11656e 0x42 (by simp [RexNoWPrefix]) 0 (.sib 2 (some 15) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x116572 0xfc19dc6) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116577 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11657f 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116582 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116585 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116588 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11658b 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11658d 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116590 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116593 0xf2 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116595 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part14Bytes : List UInt8 :=
  [0x89,0x84,0x24,0x88,0x0,0x0,0x0,0x41,0xc1,0xeb,0x3,0x44,0x33,0x9c,0x24,0x9c,0x0,0x0,0x0,0x8b,0x44,0x24,0x8,0x41,0x1,0xc3,0x44,0x89,0x1c,0x24,0xc1,0xe8,0x3,0x33,0x84,0x24,0xa0,0x0,0x0,0x0,0x8b,0x54,0x24,0x60,0x1,0xd0,0x89,0x44,0x24,0x34,0x89,0xd0,0xc1,0xe8,0x3,0x33,0x84,0x24,0xa4,0x0,0x0,0x0,0x41,0x89,0xc1,0x48,0x8b,0x7c,0x24,0x38,0x89,0xfa,0xc1,0xc2,0x19,0x89,0xfe,0xc1,0xc6,0xe,0x31,0xd6,0x89,0xf8,0xc1,0xe8,0x3,0x31,0xf0,0x44,0x3,0x4c,0x24,0x14,0x45,0x1,0xc1,0x44,0x89,0x4c,0x24,0x60,0x44,0x1,0xc0,0x89,0x44,0x24,0xc,0x44,0x89,0xc2,0xc1,0xea,0xa,0x33,0x94,0x24,0xb4,0x0,0x0,0x0,0x4c,0x8b,0x5c,0x24,0x58,0x44,0x89,0xde,0xc1,0xc6,0x1a,0x49,0x89,0xd8,0x44,0x3,0x84,0x24,0xb8,0x0,0x0,0x0,0x44,0x89,0xd8,0xc1,0xc0,0x15,0x41,0x1,0xd0,0x44,0x89,0xda,0xc1,0xc2,0x7,0x31,0xf0,0x31,0xc2,0x48,0x8b,0x9c,0x24,0xe0,0x0,0x0,0x0,0x89,0xd8,0x48,0x8b,0xb4,0x24,0x80,0x0,0x0,0x0,0x31,0xf0,0x44,0x21,0xd8,0x31,0xf0,0x45,0x1,0xc7,0x41,0x1,0xc7,0x42,0x8d,0x4,0x3a,0x5,0xc6,0x9d,0xc1,0xf,0x4c,0x8b,0x8c,0x24,0xd0,0x0,0x0,0x0,0x44,0x89,0xca,0xc1,0xc2,0x1e,0x44,0x89,0xce,0xc1,0xc6,0x13,0x31,0xd6,0x44,0x89,0xca,0xc1,0xc2,0xa,0x31,0xf2,0x48,0x8b,0x74,0x24,0x70]

set_option maxRecDepth 4096 in
theorem part14_bytes [Bindings] : part14.flatMap CheckedInstruction.bytes = part14Bytes  := by
  rfl

def part14Layout : List (BitVec 64 × Nat) :=
  [(0x1164ac, 7), (0x1164b3, 4), (0x1164b7, 8), (0x1164bf, 4), (0x1164c3, 3), (0x1164c6, 4), (0x1164ca, 3), (0x1164cd, 7), (0x1164d4, 4), (0x1164d8, 2), (0x1164da, 4), (0x1164de, 2), (0x1164e0, 3), (0x1164e3, 7), (0x1164ea, 3), (0x1164ed, 5), (0x1164f2, 2), (0x1164f4, 3), (0x1164f7, 2), (0x1164f9, 3), (0x1164fc, 2), (0x1164fe, 2), (0x116500, 3), (0x116503, 2), (0x116505, 5), (0x11650a, 3), (0x11650d, 5), (0x116512, 3), (0x116515, 4), (0x116519, 3), (0x11651c, 3), (0x11651f, 7), (0x116526, 5), (0x11652b, 3), (0x11652e, 3), (0x116531, 3), (0x116534, 8), (0x11653c, 3), (0x11653f, 3), (0x116542, 3), (0x116545, 3), (0x116548, 3), (0x11654b, 2), (0x11654d, 2), (0x11654f, 8), (0x116557, 2), (0x116559, 8), (0x116561, 2), (0x116563, 3), (0x116566, 2), (0x116568, 3), (0x11656b, 3), (0x11656e, 4), (0x116572, 5), (0x116577, 8), (0x11657f, 3), (0x116582, 3), (0x116585, 3), (0x116588, 3), (0x11658b, 2), (0x11658d, 3), (0x116590, 3), (0x116593, 2), (0x116595, 5)]

theorem part14_layout [Bindings] : InstructionTrace.layout part14 = part14Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part14_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x164ac 238 = part14Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
