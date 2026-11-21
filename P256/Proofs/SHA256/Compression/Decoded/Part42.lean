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

def part42 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1179fc 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x117a00 0x42 (by simp [RexNoWPrefix]) 1 (.sib 0 (some 15) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117a04 0xc1 0x1e376c08 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a0a 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117a0d 0x41 0xc7 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117a11 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117a14 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a16 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117a19 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a1c 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117a1f 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a22 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117a25 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117a28 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117a2b 0x45 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117a2e 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117a31 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117a34 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a37 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a3a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117a3d 0xfe rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117a3f 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117a42 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a44 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a47 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117a4a 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117a4e 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a50 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a53 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117a56 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a58 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a5b 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117a5e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a60 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117a63 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117a66 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117a69 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x117a6c 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117a6f 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117a71 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117a73 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x117a75 0x2748774c) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a7a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a7d 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a80 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a83 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117a86 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a88 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117a8b 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117a8e 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117a90 0xda rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117a92 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117a95 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117a98 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117a9b 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117a9e 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117aa1 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117aa4 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117aa7 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117aaa 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117aac 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117aaf 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ab1 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117ab4 0xc1 rfl) (by x86_local)]

def part42Bytes : List UInt8 :=
  [0x41,0xc1,0xc3,0x1e,0x42,0x8d,0xc,0x38,0x81,0xc1,0x8,0x6c,0x37,0x1e,0x41,0x89,0xdf,0x41,0xc1,0xc7,0x13,0x45,0x31,0xdf,0x89,0xd8,0xc1,0xc0,0xa,0x44,0x31,0xf8,0x45,0x89,0xc7,0x45,0x21,0xf7,0x45,0x89,0xc3,0x45,0x31,0xf3,0x41,0x21,0xdb,0x45,0x31,0xfb,0x41,0x1,0xc3,0x41,0x1,0xcc,0x41,0x1,0xcb,0xc1,0xc7,0xf,0xc1,0xc6,0xd,0x31,0xfe,0xc1,0xea,0xa,0x31,0xf2,0x44,0x89,0xe0,0xc1,0xc0,0x1a,0x8b,0x74,0x24,0x8,0x1,0xd6,0x44,0x89,0xe1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xe0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xe9,0x44,0x31,0xc9,0x44,0x21,0xe1,0x44,0x31,0xc9,0x4c,0x89,0xd2,0x1,0xf2,0x1,0xca,0x1,0xd0,0x5,0x4c,0x77,0x48,0x27,0x44,0x89,0xd9,0xc1,0xc1,0x1e,0x44,0x89,0xda,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xd9,0xc1,0xc1,0xa,0x31,0xd1,0x89,0xda,0x44,0x21,0xc2,0x41,0x89,0xda,0x45,0x31,0xc2,0x45,0x21,0xda,0x41,0x31,0xd2,0x41,0x1,0xca,0x41,0x1,0xc6,0x41,0x1,0xc2,0x89,0xe8,0xc1,0xc0,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xc1]

set_option maxRecDepth 4096 in
theorem part42_bytes [Bindings] : part42.flatMap CheckedInstruction.bytes = part42Bytes  := by
  rfl

def part42Layout : List (BitVec 64 × Nat) :=
  [(0x1179fc, 4), (0x117a00, 4), (0x117a04, 6), (0x117a0a, 3), (0x117a0d, 4), (0x117a11, 3), (0x117a14, 2), (0x117a16, 3), (0x117a19, 3), (0x117a1c, 3), (0x117a1f, 3), (0x117a22, 3), (0x117a25, 3), (0x117a28, 3), (0x117a2b, 3), (0x117a2e, 3), (0x117a31, 3), (0x117a34, 3), (0x117a37, 3), (0x117a3a, 3), (0x117a3d, 2), (0x117a3f, 3), (0x117a42, 2), (0x117a44, 3), (0x117a47, 3), (0x117a4a, 4), (0x117a4e, 2), (0x117a50, 3), (0x117a53, 3), (0x117a56, 2), (0x117a58, 3), (0x117a5b, 3), (0x117a5e, 2), (0x117a60, 3), (0x117a63, 3), (0x117a66, 3), (0x117a69, 3), (0x117a6c, 3), (0x117a6f, 2), (0x117a71, 2), (0x117a73, 2), (0x117a75, 5), (0x117a7a, 3), (0x117a7d, 3), (0x117a80, 3), (0x117a83, 3), (0x117a86, 2), (0x117a88, 3), (0x117a8b, 3), (0x117a8e, 2), (0x117a90, 2), (0x117a92, 3), (0x117a95, 3), (0x117a98, 3), (0x117a9b, 3), (0x117a9e, 3), (0x117aa1, 3), (0x117aa4, 3), (0x117aa7, 3), (0x117aaa, 2), (0x117aac, 3), (0x117aaf, 2), (0x117ab1, 3), (0x117ab4, 2)]

theorem part42_layout [Bindings] : InstructionTrace.layout part42 = part42Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part42_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x179fc 186 = part42Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
