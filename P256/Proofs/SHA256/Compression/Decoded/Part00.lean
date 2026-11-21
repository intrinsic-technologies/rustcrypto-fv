import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part00 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1159e0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1159e5 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1159e8 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1159eb 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1159ee 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 280)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1159f6 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1159f9 0xcf rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x1159fb 1 (.sib 4 none 0 (.d32 188)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x115a02 0 (.base 6 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x115a04 1 (.base 6 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115a07 0) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x115a09 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (bswap_r32_effect_step 0x115a0c 1) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x115a0e 0x49 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115a11 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115a16 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115a19 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115a1c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115a1f 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115a22 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115a24 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115a27 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115a2a 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115a2c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115a2f 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115a32 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x115a35 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115a37 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115a3a 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 272)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115a42 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115a44 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115a46 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115a48 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115a4a 0xda rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115a4c 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x115a4f 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115a52 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115a57 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115a59 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115a5b 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115a5e 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115a60 0xc7 0x428a2f98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x115a66 0x4d 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115a69 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115a6c 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115a70 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115a72 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115a75 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115a78 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115a7b 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115a7d 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115a80 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x115a83 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 264)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115a8b 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x115a8d 0x41 (by simp [RexNoWPrefix]) 2 (.sib 11 (some 1) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115a91 0xc2 0x428a2f98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115a97 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115a99 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115a9c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115a9f 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115aa1 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115aa4 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115aa6 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115aa8 0xc7 0x7 rfl rfl) (by x86_local)]

def part00Bytes : List UInt8 :=
  [0x48,0x89,0x74,0x24,0x18,0x45,0x89,0xf7,0x41,0x89,0xc6,0x45,0x89,0xcb,0x4c,0x89,0x9c,0x24,0x18,0x1,0x0,0x0,0x41,0x89,0xd1,0x89,0xcf,0x89,0x8c,0x24,0xbc,0x0,0x0,0x0,0x8b,0x6,0x8b,0x4e,0x4,0xf,0xc8,0x48,0x89,0xc6,0xf,0xc9,0x49,0x89,0xcd,0x48,0x89,0x4c,0x24,0x38,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xc1,0x44,0x21,0xd1,0x44,0x89,0xc2,0xf7,0xd2,0x44,0x21,0xca,0x4c,0x89,0x8c,0x24,0x10,0x1,0x0,0x0,0x1,0xf9,0x1,0xd1,0x1,0xc1,0x89,0xc8,0x89,0xda,0xc1,0xc2,0x1e,0x48,0x89,0xf7,0x48,0x89,0x74,0x24,0x50,0x1,0xf9,0x89,0xde,0xc1,0xc6,0x13,0x1,0xc7,0x81,0xc7,0x98,0x2f,0x8a,0x42,0x4d,0x89,0xc4,0x41,0x89,0xd8,0x41,0xc1,0xc0,0xa,0x31,0xd6,0x41,0x31,0xf0,0x44,0x89,0xfa,0x44,0x31,0xf2,0x21,0xda,0x44,0x89,0xf8,0x44,0x21,0xf0,0x4c,0x89,0xb4,0x24,0x8,0x1,0x0,0x0,0x31,0xd0,0x41,0x8d,0x14,0xb,0x81,0xc2,0x98,0x2f,0x8a,0x42,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x1,0xc0,0x89,0xd6,0xc1,0xc6,0x15,0x1,0xf8,0x89,0xd7,0xc1,0xc7,0x7]

set_option maxRecDepth 4096 in
theorem part00_bytes [Bindings] : part00.flatMap CheckedInstruction.bytes = part00Bytes  := by
  rfl

def part00Layout : List (BitVec 64 × Nat) :=
  [(0x1159e0, 5), (0x1159e5, 3), (0x1159e8, 3), (0x1159eb, 3), (0x1159ee, 8), (0x1159f6, 3), (0x1159f9, 2), (0x1159fb, 7), (0x115a02, 2), (0x115a04, 3), (0x115a07, 2), (0x115a09, 3), (0x115a0c, 2), (0x115a0e, 3), (0x115a11, 5), (0x115a16, 3), (0x115a19, 3), (0x115a1c, 3), (0x115a1f, 3), (0x115a22, 2), (0x115a24, 3), (0x115a27, 3), (0x115a2a, 2), (0x115a2c, 3), (0x115a2f, 3), (0x115a32, 3), (0x115a35, 2), (0x115a37, 3), (0x115a3a, 8), (0x115a42, 2), (0x115a44, 2), (0x115a46, 2), (0x115a48, 2), (0x115a4a, 2), (0x115a4c, 3), (0x115a4f, 3), (0x115a52, 5), (0x115a57, 2), (0x115a59, 2), (0x115a5b, 3), (0x115a5e, 2), (0x115a60, 6), (0x115a66, 3), (0x115a69, 3), (0x115a6c, 4), (0x115a70, 2), (0x115a72, 3), (0x115a75, 3), (0x115a78, 3), (0x115a7b, 2), (0x115a7d, 3), (0x115a80, 3), (0x115a83, 8), (0x115a8b, 2), (0x115a8d, 4), (0x115a91, 6), (0x115a97, 2), (0x115a99, 3), (0x115a9c, 3), (0x115a9f, 2), (0x115aa1, 3), (0x115aa4, 2), (0x115aa6, 2), (0x115aa8, 3)]

theorem part00_layout [Bindings] : InstructionTrace.layout part00 = part00Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part00_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x159e0 203 = part00Bytes := by
  decide +kernel

end P256.Proofs.SHA256.Compression.Decoded
