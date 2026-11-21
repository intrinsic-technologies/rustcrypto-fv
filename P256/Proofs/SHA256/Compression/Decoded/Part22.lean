import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part22 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116afb 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116afd 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116aff 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116b02 5 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116b09 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b0b 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116b0e 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b12 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116b15 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116b17 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b1a 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b1d 0x45 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b20 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116b23 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b26 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116b29 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116b2c 0x45 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x116b2f 0x46 (by simp [RexNoWPrefix]) 1 (.sib 1 (some 15) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x116b33 0x41 0xc1 0xb00327c8 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b3a 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116b3d 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b40 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116b43 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116b46 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b48 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116b4b 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116b4e 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116b50 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b55 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116b58 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b5b 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b5e 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116b61 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b64 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b67 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116b6a 0x41 0xc2 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116b6e 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116b70 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116b72 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116b75 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b78 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116b7b 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116b7f 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b82 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116b85 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b89 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b8c 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116b8f 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x116b92 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116b96 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x116b99 0 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116b9d 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x116ba0 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116ba4 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x116ba7 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116bab 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116bae 0x41 0xc2 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116bb2 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116bb5 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116bb7 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116bba 0 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116bbe 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116bc1 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116bc4 0x41 0xc1 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part22Bytes : List UInt8 :=
  [0x31,0xca,0x89,0xf9,0xc1,0xc1,0x1a,0x8b,0xac,0x24,0x88,0x0,0x0,0x0,0x1,0xd5,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x15,0x41,0x31,0xc9,0x89,0xf9,0xc1,0xc1,0x7,0x44,0x31,0xc9,0x45,0x89,0xe9,0x45,0x31,0xe1,0x41,0x21,0xf9,0x45,0x31,0xe1,0x41,0x1,0xef,0x45,0x1,0xcf,0x46,0x8d,0xc,0x39,0x41,0x81,0xc1,0xc8,0x27,0x3,0xb0,0x44,0x89,0xf1,0xc1,0xc1,0x1e,0x44,0x89,0xf6,0xc1,0xc6,0x13,0x31,0xce,0x44,0x89,0xf1,0xc1,0xc1,0xa,0x31,0xf1,0x4c,0x8b,0x7c,0x24,0x28,0x45,0x89,0xfa,0x45,0x21,0xc2,0x44,0x89,0xfe,0x44,0x31,0xc6,0x44,0x21,0xf6,0x44,0x31,0xd6,0x41,0x89,0xc2,0x41,0xc1,0xc2,0xf,0x1,0xce,0x89,0xc1,0xc1,0xc1,0xd,0x44,0x1,0xcb,0x41,0x89,0xeb,0x41,0xc1,0xc3,0x19,0x44,0x1,0xce,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xe,0x44,0x31,0xd1,0x45,0x31,0xd9,0x41,0x89,0xea,0x41,0xc1,0xea,0x3,0x45,0x31,0xca,0x1,0x44,0x24,0xc,0x41,0x1,0xc2,0x44,0x89,0x14,0x24,0x41,0x89,0xc1,0x41,0xc1,0xe9,0xa,0x41,0x89,0xda,0x41,0xc1,0xc2,0x1a,0x41,0x31,0xc9,0x89,0xd9,0xc1,0xc1,0x15,0x8b,0x44,0x24,0x64,0x44,0x1,0xc8,0x41,0x89,0xd9,0x41,0xc1,0xc1,0x7]

set_option maxRecDepth 4096 in
theorem part22_bytes [Bindings] : part22.flatMap CheckedInstruction.bytes = part22Bytes  := by
  rfl

def part22Layout : List (BitVec 64 × Nat) :=
  [(0x116afb, 2), (0x116afd, 2), (0x116aff, 3), (0x116b02, 7), (0x116b09, 2), (0x116b0b, 3), (0x116b0e, 4), (0x116b12, 3), (0x116b15, 2), (0x116b17, 3), (0x116b1a, 3), (0x116b1d, 3), (0x116b20, 3), (0x116b23, 3), (0x116b26, 3), (0x116b29, 3), (0x116b2c, 3), (0x116b2f, 4), (0x116b33, 7), (0x116b3a, 3), (0x116b3d, 3), (0x116b40, 3), (0x116b43, 3), (0x116b46, 2), (0x116b48, 3), (0x116b4b, 3), (0x116b4e, 2), (0x116b50, 5), (0x116b55, 3), (0x116b58, 3), (0x116b5b, 3), (0x116b5e, 3), (0x116b61, 3), (0x116b64, 3), (0x116b67, 3), (0x116b6a, 4), (0x116b6e, 2), (0x116b70, 2), (0x116b72, 3), (0x116b75, 3), (0x116b78, 3), (0x116b7b, 4), (0x116b7f, 3), (0x116b82, 3), (0x116b85, 4), (0x116b89, 3), (0x116b8c, 3), (0x116b8f, 3), (0x116b92, 4), (0x116b96, 3), (0x116b99, 4), (0x116b9d, 3), (0x116ba0, 4), (0x116ba4, 3), (0x116ba7, 4), (0x116bab, 3), (0x116bae, 4), (0x116bb2, 3), (0x116bb5, 2), (0x116bb7, 3), (0x116bba, 4), (0x116bbe, 3), (0x116bc1, 3), (0x116bc4, 4)]

theorem part22_layout [Bindings] : InstructionTrace.layout part22 = part22Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part22_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16afb 205 = part22Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
