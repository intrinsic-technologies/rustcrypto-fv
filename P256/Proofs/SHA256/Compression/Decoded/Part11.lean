import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part11 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11621c 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11621e 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x116220 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x116223 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116228 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11622a 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11622d 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116230 0xfe rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116232 0xc6 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116235 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116238 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11623a 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11623c 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11623f 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116241 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116244 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116247 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11624a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11624d 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11624f 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116252 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116255 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x116257 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11625c 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11625f 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 224)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116267 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11626a 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11626d 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x116270 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116275 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116278 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11627b 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11627d 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116280 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116283 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116285 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116287 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11628a 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11628d 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116290 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116293 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116295 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116297 0xc2 0xefbe4786 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11629d 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1162a0 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1162a3 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1162a6 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1162a9 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1162ab 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1162ae 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1162b1 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1162b6 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1162b9 0xce rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1162bb 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1162c0 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1162c2 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1162ca 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1162cd 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1162d2 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1162d4 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1162d7 0xdf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1162d9 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1162dc 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1162df 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part11Bytes : List UInt8 :=
  [0x31,0xf7,0x1,0xcf,0x49,0x89,0xf8,0x48,0x8b,0x7c,0x24,0x68,0x89,0xf9,0xc1,0xc1,0x19,0x41,0x1,0xc1,0x89,0xfe,0xc1,0xc6,0xe,0x41,0x1,0xc0,0x31,0xce,0x89,0xf8,0xc1,0xe8,0x3,0x31,0xf0,0x44,0x89,0xe9,0xc1,0xc1,0xf,0x44,0x89,0xee,0xc1,0xc6,0xd,0x31,0xce,0x44,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xf1,0x44,0x3,0x64,0x24,0xc,0x41,0x1,0xc4,0x4c,0x89,0x8c,0x24,0xe0,0x0,0x0,0x0,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x41,0x1,0xcc,0x4c,0x89,0x64,0x24,0x38,0x44,0x89,0xc9,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xc8,0x89,0xd9,0x44,0x31,0xf9,0x44,0x21,0xc9,0x44,0x31,0xf9,0x44,0x1,0xe2,0x1,0xca,0x1,0xc2,0x81,0xc2,0x86,0x47,0xbe,0xef,0x44,0x89,0xc0,0xc1,0xc0,0x1e,0x44,0x89,0xc1,0xc1,0xc1,0x13,0x31,0xc1,0x44,0x89,0xc6,0x4d,0x89,0xc1,0x4c,0x89,0x44,0x24,0x70,0xc1,0xc6,0xa,0x31,0xce,0x48,0x89,0x6c,0x24,0x78,0x89,0xe9,0x4c,0x89,0x9c,0x24,0xd8,0x0,0x0,0x0,0x44,0x21,0xd9,0x48,0x8b,0x5c,0x24,0x48,0x89,0xd8,0xc1,0xc0,0x19,0x89,0xdf,0xc1,0xc7,0xe,0x44,0x31,0xdd,0x4c,0x89,0x54,0x24,0x50]

set_option maxRecDepth 4096 in
theorem part11_bytes [Bindings] : part11.flatMap CheckedInstruction.bytes = part11Bytes  := by
  rfl

def part11Layout : List (BitVec 64 × Nat) :=
  [(0x11621c, 2), (0x11621e, 2), (0x116220, 3), (0x116223, 5), (0x116228, 2), (0x11622a, 3), (0x11622d, 3), (0x116230, 2), (0x116232, 3), (0x116235, 3), (0x116238, 2), (0x11623a, 2), (0x11623c, 3), (0x11623f, 2), (0x116241, 3), (0x116244, 3), (0x116247, 3), (0x11624a, 3), (0x11624d, 2), (0x11624f, 3), (0x116252, 3), (0x116255, 2), (0x116257, 5), (0x11625c, 3), (0x11625f, 8), (0x116267, 3), (0x11626a, 3), (0x11626d, 3), (0x116270, 5), (0x116275, 3), (0x116278, 3), (0x11627b, 2), (0x11627d, 3), (0x116280, 3), (0x116283, 2), (0x116285, 2), (0x116287, 3), (0x11628a, 3), (0x11628d, 3), (0x116290, 3), (0x116293, 2), (0x116295, 2), (0x116297, 6), (0x11629d, 3), (0x1162a0, 3), (0x1162a3, 3), (0x1162a6, 3), (0x1162a9, 2), (0x1162ab, 3), (0x1162ae, 3), (0x1162b1, 5), (0x1162b6, 3), (0x1162b9, 2), (0x1162bb, 5), (0x1162c0, 2), (0x1162c2, 8), (0x1162ca, 3), (0x1162cd, 5), (0x1162d2, 2), (0x1162d4, 3), (0x1162d7, 2), (0x1162d9, 3), (0x1162dc, 3), (0x1162df, 5)]

theorem part11_layout [Bindings] : InstructionTrace.layout part11 = part11Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part11_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x1621c 200 = part11Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
