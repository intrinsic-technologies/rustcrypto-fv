import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part33 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10ce71 0x41 0xeb 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce75 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ce78 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce7b 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce7e 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ce81 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10ce85 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ce8a 0x45 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce8d 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ce90 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce94 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce97 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce9a 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce9d 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cea0 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cea3 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cea6 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cea9 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ceac 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10ceaf 0x41 0xc0 0x92722c85 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ceb6 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ceb9 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cebd 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cec0 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cec4 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cec7 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ceca 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cece 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ced1 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ced3 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ced5 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ced8 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cedb 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cede 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cee1 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cee4 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cee7 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ceea 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ceed 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cef1 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cef4 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cef7 0x41 0xc0 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cefb 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cefe 0x44 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf01 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cf04 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf08 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cf0b 0xc3 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf0e 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf11 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10cf14 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf18 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10cf1b 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cf20 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10cf23 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf28 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10cf2b 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf2f 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10cf32 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cf37 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf3a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cf3d 0x41 0xc0 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf41 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cf44 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part33Bytes : List UInt8 :=
  [0x41,0xc1,0xeb,0xa,0x44,0x89,0xf3,0xc1,0xc3,0x1a,0x45,0x31,0xcb,0x45,0x89,0xf1,0x41,0xc1,0xc1,0x15,0x44,0x8b,0x64,0x24,0x48,0x45,0x1,0xdc,0x45,0x89,0xf3,0x41,0xc1,0xc3,0x7,0x41,0x31,0xd9,0x45,0x31,0xcb,0x45,0x89,0xd1,0x41,0x31,0xc9,0x45,0x21,0xf1,0x41,0x31,0xc9,0x45,0x1,0xe0,0x45,0x1,0xc8,0x45,0x1,0xd8,0x41,0x81,0xc0,0x85,0x2c,0x72,0x92,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x41,0x89,0xd1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xd9,0x89,0xf3,0x21,0xc3,0x41,0x89,0xf3,0x41,0x31,0xc3,0x41,0x21,0xd3,0x41,0x31,0xdb,0x45,0x1,0xcb,0x44,0x1,0xc7,0x45,0x1,0xc3,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x41,0x89,0xe8,0x41,0x89,0xef,0x41,0xc1,0xc0,0xd,0x45,0x31,0xc8,0x44,0x89,0xe5,0x45,0x89,0xe1,0x41,0xc1,0xc1,0x19,0x44,0x89,0xe3,0xc1,0xc3,0xe,0x44,0x31,0xcb,0x45,0x89,0xe1,0x41,0xc1,0xe9,0x3,0x41,0x31,0xd9,0x44,0x1,0x7c,0x24,0x24,0x45,0x1,0xf9,0x44,0x89,0x4c,0x24,0x48,0x45,0x89,0xf9,0x41,0xc1,0xe9,0xa,0x45,0x31,0xc1,0x44,0x8b,0x64,0x24,0x70,0x45,0x1,0xcc,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x1a,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x15]

set_option maxRecDepth 4096 in
theorem part33_bytes [Bindings] : part33.flatMap CheckedInstruction.bytes = part33Bytes  := by
  rfl

def part33Layout : List (BitVec 64 × Nat) :=
  [(0x10ce71, 4), (0x10ce75, 3), (0x10ce78, 3), (0x10ce7b, 3), (0x10ce7e, 3), (0x10ce81, 4), (0x10ce85, 5), (0x10ce8a, 3), (0x10ce8d, 3), (0x10ce90, 4), (0x10ce94, 3), (0x10ce97, 3), (0x10ce9a, 3), (0x10ce9d, 3), (0x10cea0, 3), (0x10cea3, 3), (0x10cea6, 3), (0x10cea9, 3), (0x10ceac, 3), (0x10ceaf, 7), (0x10ceb6, 3), (0x10ceb9, 4), (0x10cebd, 3), (0x10cec0, 4), (0x10cec4, 3), (0x10cec7, 3), (0x10ceca, 4), (0x10cece, 3), (0x10ced1, 2), (0x10ced3, 2), (0x10ced5, 3), (0x10ced8, 3), (0x10cedb, 3), (0x10cede, 3), (0x10cee1, 3), (0x10cee4, 3), (0x10cee7, 3), (0x10ceea, 3), (0x10ceed, 4), (0x10cef1, 3), (0x10cef4, 3), (0x10cef7, 4), (0x10cefb, 3), (0x10cefe, 3), (0x10cf01, 3), (0x10cf04, 4), (0x10cf08, 3), (0x10cf0b, 3), (0x10cf0e, 3), (0x10cf11, 3), (0x10cf14, 4), (0x10cf18, 3), (0x10cf1b, 5), (0x10cf20, 3), (0x10cf23, 5), (0x10cf28, 3), (0x10cf2b, 4), (0x10cf2f, 3), (0x10cf32, 5), (0x10cf37, 3), (0x10cf3a, 3), (0x10cf3d, 4), (0x10cf41, 3), (0x10cf44, 4)]

theorem part33_layout [Bindings] : InstructionTrace.layout part33 = part33Layout := by
  rfl

theorem part33_ordered [Bindings] : InstructionTrace.ordered 0x10ce71 part33 = true := by
  rw [InstructionTrace.ordered_eq_layout, part33_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part33_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xce71 215 = part33Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
