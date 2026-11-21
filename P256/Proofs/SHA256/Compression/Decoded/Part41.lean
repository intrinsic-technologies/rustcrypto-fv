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

def part41 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11793f 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117941 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117944 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117947 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11794a 0xcb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11794c 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11794e 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117951 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117954 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x117956 0x19a4c116) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11795b 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11795e 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117961 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117963 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117966 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117969 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11796b 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11796e 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117971 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117974 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117977 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11797a 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11797c 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11797e 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117981 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117984 0xc6 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117987 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117989 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11798c 0x41 0xc3 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117990 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117993 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117995 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117998 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11799a 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11799d 0xd0 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x11799f 1 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1179a3 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1179a5 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1179a7 0xca rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1179a9 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1179ac 0xc1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x1179ae 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1179b3 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1179b6 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x1179bb 0x41 0xea 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1179bf 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1179c2 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1179c6 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1179c9 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1179cc 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1179cf 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1179d2 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1179d6 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1179d9 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1179dc 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1179df 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1179e2 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1179e5 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1179ea 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1179ed 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1179f0 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1179f3 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1179f6 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1179f9 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part41Bytes : List UInt8 :=
  [0x89,0xd6,0x44,0x31,0xfe,0x44,0x21,0xce,0x44,0x31,0xfe,0x1,0xcb,0x1,0xf3,0x44,0x89,0xc6,0xc1,0xc6,0x1e,0x1,0xd8,0x5,0x16,0xc1,0xa4,0x19,0x44,0x89,0xc7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xf7,0x44,0x21,0xe7,0x44,0x89,0xf3,0x44,0x31,0xe3,0x44,0x21,0xc3,0x31,0xfb,0x1,0xf3,0x41,0x1,0xc5,0x44,0x89,0xd6,0xc1,0xc6,0xf,0x1,0xc3,0x45,0x89,0xd3,0x41,0xc1,0xc3,0xd,0x41,0x31,0xf3,0x89,0xca,0xc1,0xc2,0x19,0x89,0xc8,0xc1,0xc0,0xe,0x31,0xd0,0x1,0x4c,0x24,0x70,0x89,0xcf,0x89,0xce,0x89,0xca,0xc1,0xe9,0x3,0x31,0xc1,0x44,0x1,0x54,0x24,0x48,0x44,0x1,0xd1,0x48,0x89,0x4c,0x24,0x28,0x41,0xc1,0xea,0xa,0x45,0x31,0xda,0x8b,0x6c,0x24,0xc,0x44,0x1,0xd5,0x44,0x89,0xe8,0xc1,0xc0,0x1a,0x45,0x89,0xeb,0x41,0xc1,0xc3,0x15,0x41,0x31,0xc3,0x44,0x89,0xe8,0xc1,0xc0,0x7,0x44,0x31,0xd8,0x45,0x89,0xcb,0x4c,0x8b,0x54,0x24,0x38,0x45,0x31,0xd3,0x45,0x21,0xeb,0x45,0x31,0xd3,0x41,0x1,0xef,0x45,0x1,0xdf,0x41,0x89,0xdb]

set_option maxRecDepth 4096 in
theorem part41_bytes [Bindings] : part41.flatMap CheckedInstruction.bytes = part41Bytes  := by
  rfl

def part41Layout : List (BitVec 64 × Nat) :=
  [(0x11793f, 2), (0x117941, 3), (0x117944, 3), (0x117947, 3), (0x11794a, 2), (0x11794c, 2), (0x11794e, 3), (0x117951, 3), (0x117954, 2), (0x117956, 5), (0x11795b, 3), (0x11795e, 3), (0x117961, 2), (0x117963, 3), (0x117966, 3), (0x117969, 2), (0x11796b, 3), (0x11796e, 3), (0x117971, 3), (0x117974, 3), (0x117977, 3), (0x11797a, 2), (0x11797c, 2), (0x11797e, 3), (0x117981, 3), (0x117984, 3), (0x117987, 2), (0x117989, 3), (0x11798c, 4), (0x117990, 3), (0x117993, 2), (0x117995, 3), (0x117998, 2), (0x11799a, 3), (0x11799d, 2), (0x11799f, 4), (0x1179a3, 2), (0x1179a5, 2), (0x1179a7, 2), (0x1179a9, 3), (0x1179ac, 2), (0x1179ae, 5), (0x1179b3, 3), (0x1179b6, 5), (0x1179bb, 4), (0x1179bf, 3), (0x1179c2, 4), (0x1179c6, 3), (0x1179c9, 3), (0x1179cc, 3), (0x1179cf, 3), (0x1179d2, 4), (0x1179d6, 3), (0x1179d9, 3), (0x1179dc, 3), (0x1179df, 3), (0x1179e2, 3), (0x1179e5, 5), (0x1179ea, 3), (0x1179ed, 3), (0x1179f0, 3), (0x1179f3, 3), (0x1179f6, 3), (0x1179f9, 3)]

theorem part41_layout [Bindings] : InstructionTrace.layout part41 = part41Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part41_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x1793f 189 = part41Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
