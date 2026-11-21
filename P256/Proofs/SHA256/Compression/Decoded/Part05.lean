import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part05 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115de0 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115de3 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x115de6 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115dea 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115dec 0xc2 0xab1c5ed5 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115df2 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115df5 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115df8 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115dfb 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115dfe 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115e01 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e03 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115e06 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e09 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115e0c 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115e0f 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115e12 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115e15 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115e18 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115e1a 0xfb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e1c 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115e1f 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115e22 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e24 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115e27 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115e29 0xfb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e2b 0xc3 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115e2e 0xd3 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x115e30 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x115e35 5 (.base 2 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x115e38 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x115e3a 5 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115e3e 0xfa rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115e40 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115e42 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115e44 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x115e46 0xfa rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x115e48 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x115e4a 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115e4c 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x115e4e 2 (.sib 3 (some 0) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x115e51 0xc2 0xd807aa98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e57 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e5a 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e5d 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e60 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115e63 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e65 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e68 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115e6b 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e6d 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115e70 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e73 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x115e76 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x115e79 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115e7c 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115e7e 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x115e80 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x115e83 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e85 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e88 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x115e8b 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x115e8e 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x115e91 0xd3 rfl) (by x86_local)]

def part05Bytes : List UInt8 :=
  [0x44,0x1,0xd3,0x45,0x89,0xda,0x41,0xc1,0xc2,0x1e,0x1,0xda,0x81,0xc2,0xd5,0x5e,0x1c,0xab,0x44,0x89,0xdb,0xc1,0xc3,0x13,0x44,0x31,0xd3,0x44,0x89,0xdd,0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xc3,0x44,0x21,0xcb,0x45,0x89,0xc2,0x45,0x31,0xca,0x45,0x21,0xda,0x41,0x31,0xda,0x41,0x1,0xea,0x1,0xd7,0x89,0xfb,0xc1,0xc3,0x1a,0x41,0x1,0xd2,0x89,0xfa,0xc1,0xc2,0x15,0x31,0xda,0x89,0xfb,0xc1,0xc3,0x7,0x31,0xd3,0x48,0x8b,0x54,0x24,0x18,0x8b,0x6a,0x20,0xf,0xcd,0x89,0x6c,0x24,0x60,0x89,0xfa,0x21,0xf2,0x1,0xe8,0x1,0xd0,0x89,0xfa,0xf7,0xd2,0x21,0xca,0x1,0xd0,0x8d,0x14,0x3,0x81,0xc2,0x98,0xaa,0x7,0xd8,0x44,0x89,0xd0,0xc1,0xc0,0x1e,0x44,0x89,0xd3,0xc1,0xc3,0x13,0x31,0xc3,0x44,0x89,0xd5,0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xdb,0x44,0x21,0xc3,0x44,0x89,0xd8,0x44,0x31,0xc0,0x44,0x21,0xd0,0x31,0xd8,0x1,0xe8,0x41,0x1,0xd1,0x1,0xd0,0x44,0x89,0xca,0xc1,0xc2,0x1a,0x44,0x89,0xcb,0xc1,0xc3,0x15,0x31,0xd3]

set_option maxRecDepth 4096 in
theorem part05_bytes [Bindings] : part05.flatMap CheckedInstruction.bytes = part05Bytes  := by
  rfl

def part05Layout : List (BitVec 64 × Nat) :=
  [(0x115de0, 3), (0x115de3, 3), (0x115de6, 4), (0x115dea, 2), (0x115dec, 6), (0x115df2, 3), (0x115df5, 3), (0x115df8, 3), (0x115dfb, 3), (0x115dfe, 3), (0x115e01, 2), (0x115e03, 3), (0x115e06, 3), (0x115e09, 3), (0x115e0c, 3), (0x115e0f, 3), (0x115e12, 3), (0x115e15, 3), (0x115e18, 2), (0x115e1a, 2), (0x115e1c, 3), (0x115e1f, 3), (0x115e22, 2), (0x115e24, 3), (0x115e27, 2), (0x115e29, 2), (0x115e2b, 3), (0x115e2e, 2), (0x115e30, 5), (0x115e35, 3), (0x115e38, 2), (0x115e3a, 4), (0x115e3e, 2), (0x115e40, 2), (0x115e42, 2), (0x115e44, 2), (0x115e46, 2), (0x115e48, 2), (0x115e4a, 2), (0x115e4c, 2), (0x115e4e, 3), (0x115e51, 6), (0x115e57, 3), (0x115e5a, 3), (0x115e5d, 3), (0x115e60, 3), (0x115e63, 2), (0x115e65, 3), (0x115e68, 3), (0x115e6b, 2), (0x115e6d, 3), (0x115e70, 3), (0x115e73, 3), (0x115e76, 3), (0x115e79, 3), (0x115e7c, 2), (0x115e7e, 2), (0x115e80, 3), (0x115e83, 2), (0x115e85, 3), (0x115e88, 3), (0x115e8b, 3), (0x115e8e, 3), (0x115e91, 2)]

theorem part05_layout [Bindings] : InstructionTrace.layout part05 = part05Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part05_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x15de0 179 = part05Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
