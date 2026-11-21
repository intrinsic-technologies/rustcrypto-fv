import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part33 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x117321 0x41 0xeb 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117325 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117328 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11732b 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11732e 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117331 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x117335 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11733a 0x45 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11733d 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117340 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117344 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117347 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11734a 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11734d 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117350 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117353 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117356 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117359 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11735c 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x11735f 0x41 0xc0 0x92722c85 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117366 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117369 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11736d 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117370 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117374 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117377 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11737a 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11737e 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117381 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117383 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117385 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117388 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11738b 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11738e 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117391 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117394 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117397 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11739a 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11739d 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173a1 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173a4 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1173a7 0x41 0xc0 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1173ab 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173ae 0x44 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173b1 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1173b4 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173b8 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1173bb 0xc3 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1173be 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173c1 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x1173c4 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1173c8 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x1173cb 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1173d0 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x1173d3 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173d8 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x1173db 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1173df 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x1173e2 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1173e7 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173ea 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1173ed 0x41 0xc0 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1173f1 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x1173f4 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part33Bytes : List UInt8 :=
  [0x41,0xc1,0xeb,0xa,0x44,0x89,0xf3,0xc1,0xc3,0x1a,0x45,0x31,0xcb,0x45,0x89,0xf1,0x41,0xc1,0xc1,0x15,0x44,0x8b,0x64,0x24,0x48,0x45,0x1,0xdc,0x45,0x89,0xf3,0x41,0xc1,0xc3,0x7,0x41,0x31,0xd9,0x45,0x31,0xcb,0x45,0x89,0xd1,0x41,0x31,0xc9,0x45,0x21,0xf1,0x41,0x31,0xc9,0x45,0x1,0xe0,0x45,0x1,0xc8,0x45,0x1,0xd8,0x41,0x81,0xc0,0x85,0x2c,0x72,0x92,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x41,0x89,0xd1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xd9,0x89,0xf3,0x21,0xc3,0x41,0x89,0xf3,0x41,0x31,0xc3,0x41,0x21,0xd3,0x41,0x31,0xdb,0x45,0x1,0xcb,0x44,0x1,0xc7,0x45,0x1,0xc3,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x41,0x89,0xe8,0x41,0x89,0xef,0x41,0xc1,0xc0,0xd,0x45,0x31,0xc8,0x44,0x89,0xe5,0x45,0x89,0xe1,0x41,0xc1,0xc1,0x19,0x44,0x89,0xe3,0xc1,0xc3,0xe,0x44,0x31,0xcb,0x45,0x89,0xe1,0x41,0xc1,0xe9,0x3,0x41,0x31,0xd9,0x44,0x1,0x7c,0x24,0x24,0x45,0x1,0xf9,0x44,0x89,0x4c,0x24,0x48,0x45,0x89,0xf9,0x41,0xc1,0xe9,0xa,0x45,0x31,0xc1,0x44,0x8b,0x64,0x24,0x70,0x45,0x1,0xcc,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x1a,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x15]

set_option maxRecDepth 4096 in
theorem part33_bytes [Bindings] : part33.flatMap CheckedInstruction.bytes = part33Bytes  := by
  rfl

def part33Layout : List (BitVec 64 × Nat) :=
  [(0x117321, 4), (0x117325, 3), (0x117328, 3), (0x11732b, 3), (0x11732e, 3), (0x117331, 4), (0x117335, 5), (0x11733a, 3), (0x11733d, 3), (0x117340, 4), (0x117344, 3), (0x117347, 3), (0x11734a, 3), (0x11734d, 3), (0x117350, 3), (0x117353, 3), (0x117356, 3), (0x117359, 3), (0x11735c, 3), (0x11735f, 7), (0x117366, 3), (0x117369, 4), (0x11736d, 3), (0x117370, 4), (0x117374, 3), (0x117377, 3), (0x11737a, 4), (0x11737e, 3), (0x117381, 2), (0x117383, 2), (0x117385, 3), (0x117388, 3), (0x11738b, 3), (0x11738e, 3), (0x117391, 3), (0x117394, 3), (0x117397, 3), (0x11739a, 3), (0x11739d, 4), (0x1173a1, 3), (0x1173a4, 3), (0x1173a7, 4), (0x1173ab, 3), (0x1173ae, 3), (0x1173b1, 3), (0x1173b4, 4), (0x1173b8, 3), (0x1173bb, 3), (0x1173be, 3), (0x1173c1, 3), (0x1173c4, 4), (0x1173c8, 3), (0x1173cb, 5), (0x1173d0, 3), (0x1173d3, 5), (0x1173d8, 3), (0x1173db, 4), (0x1173df, 3), (0x1173e2, 5), (0x1173e7, 3), (0x1173ea, 3), (0x1173ed, 4), (0x1173f1, 3), (0x1173f4, 4)]

theorem part33_layout [Bindings] : InstructionTrace.layout part33 = part33Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part33_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17321 215 = part33Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
