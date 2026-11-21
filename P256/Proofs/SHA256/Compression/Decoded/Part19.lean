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

def part19 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1168a8 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1168ab 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1168ad 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1168b0 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1168b3 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1168b6 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1168b9 0x44 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1168bc 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1168bf 0xfb rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1168c1 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1168c4 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1168c7 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1168cb 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1168cd 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1168cf 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1168d2 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1168d5 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1168d8 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1168dc 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1168de 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1168e0 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1168e3 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1168e6 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1168e9 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x1168ec 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1168f0 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x1168f3 2 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1168f7 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x1168fa 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1168ff 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116902 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116905 0x41 0xc0 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116909 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11690b 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11690e 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x116911 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116916 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116919 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11691c 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11691f 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116922 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116924 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116927 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116929 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11692c 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11692e 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116931 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x116934 0x42 (by simp [RexNoWPrefix]) 0 (.sib 1 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x116938 0x76f988da) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11693d 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11693f 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116942 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116945 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116949 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11694c 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11694e 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116951 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116954 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116957 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11695a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11695d 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116960 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116963 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116966 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part19Bytes : List UInt8 :=
  [0x41,0x31,0xc0,0x89,0xf8,0xc1,0xc0,0xa,0x44,0x31,0xc0,0x45,0x89,0xe8,0x45,0x21,0xe0,0x44,0x89,0xeb,0x44,0x31,0xe3,0x21,0xfb,0x44,0x31,0xc3,0x41,0x89,0xd0,0x41,0xc1,0xc0,0xf,0x1,0xc3,0x89,0xd0,0xc1,0xc0,0xd,0x41,0x1,0xcf,0x41,0x89,0xeb,0x41,0xc1,0xc3,0x19,0x1,0xcb,0x89,0xe9,0xc1,0xc1,0xe,0x44,0x31,0xc0,0x44,0x31,0xd9,0x41,0x89,0xe8,0x41,0xc1,0xe8,0x3,0x41,0x31,0xc8,0x1,0x54,0x24,0x10,0x41,0x1,0xd0,0x44,0x89,0x44,0x24,0x68,0xc1,0xea,0xa,0x45,0x89,0xf8,0x41,0xc1,0xc0,0x1a,0x31,0xc2,0x44,0x89,0xf8,0xc1,0xc0,0x15,0x44,0x8b,0x74,0x24,0x60,0x41,0x1,0xd6,0x44,0x89,0xf9,0xc1,0xc1,0x7,0x44,0x31,0xc0,0x31,0xc1,0x44,0x89,0xc8,0x31,0xf0,0x44,0x21,0xf8,0x31,0xf0,0x45,0x1,0xf2,0x41,0x1,0xc2,0x42,0x8d,0x4,0x11,0x5,0xda,0x88,0xf9,0x76,0x89,0xd9,0xc1,0xc1,0x1e,0x41,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x41,0x31,0xc8,0x89,0xd9,0xc1,0xc1,0xa,0x44,0x31,0xc1,0x41,0x89,0xfa,0x45,0x21,0xea,0x41,0x89,0xf8,0x45,0x31,0xe8,0x41,0x21,0xd8,0x45,0x31,0xd0,0x41,0x1,0xc8]

set_option maxRecDepth 4096 in
theorem part19_bytes [Bindings] : part19.flatMap CheckedInstruction.bytes = part19Bytes  := by
  rfl

def part19Layout : List (BitVec 64 × Nat) :=
  [(0x1168a8, 3), (0x1168ab, 2), (0x1168ad, 3), (0x1168b0, 3), (0x1168b3, 3), (0x1168b6, 3), (0x1168b9, 3), (0x1168bc, 3), (0x1168bf, 2), (0x1168c1, 3), (0x1168c4, 3), (0x1168c7, 4), (0x1168cb, 2), (0x1168cd, 2), (0x1168cf, 3), (0x1168d2, 3), (0x1168d5, 3), (0x1168d8, 4), (0x1168dc, 2), (0x1168de, 2), (0x1168e0, 3), (0x1168e3, 3), (0x1168e6, 3), (0x1168e9, 3), (0x1168ec, 4), (0x1168f0, 3), (0x1168f3, 4), (0x1168f7, 3), (0x1168fa, 5), (0x1168ff, 3), (0x116902, 3), (0x116905, 4), (0x116909, 2), (0x11690b, 3), (0x11690e, 3), (0x116911, 5), (0x116916, 3), (0x116919, 3), (0x11691c, 3), (0x11691f, 3), (0x116922, 2), (0x116924, 3), (0x116927, 2), (0x116929, 3), (0x11692c, 2), (0x11692e, 3), (0x116931, 3), (0x116934, 4), (0x116938, 5), (0x11693d, 2), (0x11693f, 3), (0x116942, 3), (0x116945, 4), (0x116949, 3), (0x11694c, 2), (0x11694e, 3), (0x116951, 3), (0x116954, 3), (0x116957, 3), (0x11695a, 3), (0x11695d, 3), (0x116960, 3), (0x116963, 3), (0x116966, 3)]

theorem part19_layout [Bindings] : InstructionTrace.layout part19 = part19Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part19_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x168a8 193 = part19Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
