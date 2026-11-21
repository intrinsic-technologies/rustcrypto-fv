import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part41 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d48f 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d491 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d494 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d497 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d49a 0xcb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d49c 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d49e 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d4a1 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d4a4 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10d4a6 0x19a4c116) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d4ab 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d4ae 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d4b1 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d4b3 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d4b6 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d4b9 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d4bb 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d4be 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d4c1 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d4c4 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d4c7 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d4ca 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d4cc 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d4ce 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d4d1 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d4d4 0xc6 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d4d7 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d4d9 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d4dc 0x41 0xc3 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d4e0 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d4e3 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d4e5 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d4e8 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d4ea 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d4ed 0xd0 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10d4ef 1 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d4f3 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d4f5 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d4f7 0xca rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d4f9 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d4fc 0xc1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10d4fe 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d503 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10d506 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10d50b 0x41 0xea 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d50f 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d512 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d516 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d519 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d51c 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d51f 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d522 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d526 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d529 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d52c 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d52f 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d532 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10d535 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d53a 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d53d 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d540 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d543 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d546 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d549 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part41Bytes : List UInt8 :=
  [0x89,0xd6,0x44,0x31,0xfe,0x44,0x21,0xce,0x44,0x31,0xfe,0x1,0xcb,0x1,0xf3,0x44,0x89,0xc6,0xc1,0xc6,0x1e,0x1,0xd8,0x5,0x16,0xc1,0xa4,0x19,0x44,0x89,0xc7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xf7,0x44,0x21,0xe7,0x44,0x89,0xf3,0x44,0x31,0xe3,0x44,0x21,0xc3,0x31,0xfb,0x1,0xf3,0x41,0x1,0xc5,0x44,0x89,0xd6,0xc1,0xc6,0xf,0x1,0xc3,0x45,0x89,0xd3,0x41,0xc1,0xc3,0xd,0x41,0x31,0xf3,0x89,0xca,0xc1,0xc2,0x19,0x89,0xc8,0xc1,0xc0,0xe,0x31,0xd0,0x1,0x4c,0x24,0x70,0x89,0xcf,0x89,0xce,0x89,0xca,0xc1,0xe9,0x3,0x31,0xc1,0x44,0x1,0x54,0x24,0x48,0x44,0x1,0xd1,0x48,0x89,0x4c,0x24,0x28,0x41,0xc1,0xea,0xa,0x45,0x31,0xda,0x8b,0x6c,0x24,0xc,0x44,0x1,0xd5,0x44,0x89,0xe8,0xc1,0xc0,0x1a,0x45,0x89,0xeb,0x41,0xc1,0xc3,0x15,0x41,0x31,0xc3,0x44,0x89,0xe8,0xc1,0xc0,0x7,0x44,0x31,0xd8,0x45,0x89,0xcb,0x4c,0x8b,0x54,0x24,0x38,0x45,0x31,0xd3,0x45,0x21,0xeb,0x45,0x31,0xd3,0x41,0x1,0xef,0x45,0x1,0xdf,0x41,0x89,0xdb]

set_option maxRecDepth 4096 in
theorem part41_bytes [Bindings] : part41.flatMap CheckedInstruction.bytes = part41Bytes  := by
  rfl

def part41Layout : List (BitVec 64 × Nat) :=
  [(0x10d48f, 2), (0x10d491, 3), (0x10d494, 3), (0x10d497, 3), (0x10d49a, 2), (0x10d49c, 2), (0x10d49e, 3), (0x10d4a1, 3), (0x10d4a4, 2), (0x10d4a6, 5), (0x10d4ab, 3), (0x10d4ae, 3), (0x10d4b1, 2), (0x10d4b3, 3), (0x10d4b6, 3), (0x10d4b9, 2), (0x10d4bb, 3), (0x10d4be, 3), (0x10d4c1, 3), (0x10d4c4, 3), (0x10d4c7, 3), (0x10d4ca, 2), (0x10d4cc, 2), (0x10d4ce, 3), (0x10d4d1, 3), (0x10d4d4, 3), (0x10d4d7, 2), (0x10d4d9, 3), (0x10d4dc, 4), (0x10d4e0, 3), (0x10d4e3, 2), (0x10d4e5, 3), (0x10d4e8, 2), (0x10d4ea, 3), (0x10d4ed, 2), (0x10d4ef, 4), (0x10d4f3, 2), (0x10d4f5, 2), (0x10d4f7, 2), (0x10d4f9, 3), (0x10d4fc, 2), (0x10d4fe, 5), (0x10d503, 3), (0x10d506, 5), (0x10d50b, 4), (0x10d50f, 3), (0x10d512, 4), (0x10d516, 3), (0x10d519, 3), (0x10d51c, 3), (0x10d51f, 3), (0x10d522, 4), (0x10d526, 3), (0x10d529, 3), (0x10d52c, 3), (0x10d52f, 3), (0x10d532, 3), (0x10d535, 5), (0x10d53a, 3), (0x10d53d, 3), (0x10d540, 3), (0x10d543, 3), (0x10d546, 3), (0x10d549, 3)]

theorem part41_layout [Bindings] : InstructionTrace.layout part41 = part41Layout := by
  rfl

theorem part41_ordered [Bindings] : InstructionTrace.ordered 0x10d48f part41 = true := by
  rw [InstructionTrace.ordered_eq_layout, part41_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part41_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd48f 189 = part41Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
