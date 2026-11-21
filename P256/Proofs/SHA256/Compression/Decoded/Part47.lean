import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part47 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_effect_step 0x117d89 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117d8b 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117d8e 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d90 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d93 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d96 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d99 0xc7 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d9c 0xd7 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x117d9e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117da3 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x117da6 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117dab 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117dae 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117db1 0xfa rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117db3 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117dbb 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117dbe 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117dc1 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117dc4 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117dc7 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117dca 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117dcc 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117dcf 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117dd2 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117dd4 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117dd7 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117dda 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117ddd 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117de0 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117de3 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117de6 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117de8 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117deb 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x117dee 0x41 0xc3 0x78a5636f (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117df5 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117df7 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117dfa 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117dfc 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117dfe 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117e01 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e03 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117e06 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e08 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117e0b 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117e0d 0xca rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117e0f 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117e11 0xfa rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117e13 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117e16 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117e18 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117e1b 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e1e 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117e21 0x41 0xc3 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e25 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x117e28 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117e2d 0xef rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x117e2f 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117e34 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117e36 0xef 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e39 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e3c 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117e3f 0x41 0xc3 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117e43 5 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117e47 0xfd rfl) (by x86_local)]

def part47Bytes : List UInt8 :=
  [0x1,0xd9,0x41,0x1,0xd5,0x1,0xd1,0x44,0x89,0xf2,0xc1,0xc2,0xf,0x44,0x89,0xf7,0xc1,0xc7,0xd,0x31,0xd7,0x48,0x8b,0x54,0x24,0x40,0x44,0x1,0xf2,0x48,0x89,0x54,0x24,0x40,0x44,0x89,0xf2,0xc1,0xea,0xa,0x31,0xfa,0x44,0x8b,0xb4,0x24,0x80,0x0,0x0,0x0,0x41,0x1,0xd6,0x44,0x89,0xea,0xc1,0xc2,0x1a,0x44,0x89,0xef,0xc1,0xc7,0x15,0x31,0xd7,0x44,0x89,0xea,0xc1,0xc2,0x7,0x31,0xfa,0x44,0x89,0xcf,0x44,0x31,0xd7,0x44,0x21,0xef,0x44,0x31,0xd7,0x45,0x1,0xf3,0x41,0x1,0xfb,0x89,0xcf,0xc1,0xc7,0x1e,0x41,0x1,0xd3,0x41,0x81,0xc3,0x6f,0x63,0xa5,0x78,0x89,0xca,0xc1,0xc2,0x13,0x31,0xfa,0x89,0xcf,0xc1,0xc7,0xa,0x31,0xd7,0x44,0x89,0xc3,0x21,0xf3,0x44,0x89,0xc2,0x31,0xf2,0x21,0xca,0x31,0xda,0x1,0xfa,0x44,0x1,0xd8,0x89,0xef,0xc1,0xc7,0xf,0x44,0x1,0xda,0x41,0x89,0xeb,0x41,0xc1,0xc3,0xd,0x41,0x31,0xfb,0x48,0x8b,0x7c,0x24,0x28,0x1,0xef,0x48,0x89,0x7c,0x24,0x28,0x89,0xef,0xc1,0xef,0xa,0x44,0x31,0xdf,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x1a,0x8b,0x6c,0x24,0x58,0x1,0xfd]

set_option maxRecDepth 4096 in
theorem part47_bytes [Bindings] : part47.flatMap CheckedInstruction.bytes = part47Bytes  := by
  rfl

def part47Layout : List (BitVec 64 × Nat) :=
  [(0x117d89, 2), (0x117d8b, 3), (0x117d8e, 2), (0x117d90, 3), (0x117d93, 3), (0x117d96, 3), (0x117d99, 3), (0x117d9c, 2), (0x117d9e, 5), (0x117da3, 3), (0x117da6, 5), (0x117dab, 3), (0x117dae, 3), (0x117db1, 2), (0x117db3, 8), (0x117dbb, 3), (0x117dbe, 3), (0x117dc1, 3), (0x117dc4, 3), (0x117dc7, 3), (0x117dca, 2), (0x117dcc, 3), (0x117dcf, 3), (0x117dd2, 2), (0x117dd4, 3), (0x117dd7, 3), (0x117dda, 3), (0x117ddd, 3), (0x117de0, 3), (0x117de3, 3), (0x117de6, 2), (0x117de8, 3), (0x117deb, 3), (0x117dee, 7), (0x117df5, 2), (0x117df7, 3), (0x117dfa, 2), (0x117dfc, 2), (0x117dfe, 3), (0x117e01, 2), (0x117e03, 3), (0x117e06, 2), (0x117e08, 3), (0x117e0b, 2), (0x117e0d, 2), (0x117e0f, 2), (0x117e11, 2), (0x117e13, 3), (0x117e16, 2), (0x117e18, 3), (0x117e1b, 3), (0x117e1e, 3), (0x117e21, 4), (0x117e25, 3), (0x117e28, 5), (0x117e2d, 2), (0x117e2f, 5), (0x117e34, 2), (0x117e36, 3), (0x117e39, 3), (0x117e3c, 3), (0x117e3f, 4), (0x117e43, 4), (0x117e47, 2)]

theorem part47_layout [Bindings] : InstructionTrace.layout part47 = part47Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part47_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17d89 192 = part47Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
