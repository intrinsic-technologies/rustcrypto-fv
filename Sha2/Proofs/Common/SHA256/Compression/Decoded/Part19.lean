import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part19 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c3f8 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c3fb 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c3fd 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c400 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c403 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c406 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c409 0x44 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c40c 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10c40f 0xfb rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c411 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c414 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c417 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c41b 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c41d 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c41f 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c422 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c425 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c428 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c42c 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c42e 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c430 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c433 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c436 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c439 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c43c 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c440 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c443 2 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c447 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10c44a 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c44f 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c452 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c455 0x41 0xc0 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c459 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c45b 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c45e 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10c461 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c466 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c469 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c46c 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c46f 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c472 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c474 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c477 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c479 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c47c 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c47e 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c481 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10c484 0x42 (by simp [RexNoWPrefix]) 0 (.sib 1 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10c488 0x76f988da) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c48d 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c48f 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c492 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c495 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c499 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c49c 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c49e 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c4a1 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c4a4 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c4a7 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c4aa 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c4ad 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c4b0 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c4b3 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c4b6 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part19Bytes : List UInt8 :=
  [0x41,0x31,0xc0,0x89,0xf8,0xc1,0xc0,0xa,0x44,0x31,0xc0,0x45,0x89,0xe8,0x45,0x21,0xe0,0x44,0x89,0xeb,0x44,0x31,0xe3,0x21,0xfb,0x44,0x31,0xc3,0x41,0x89,0xd0,0x41,0xc1,0xc0,0xf,0x1,0xc3,0x89,0xd0,0xc1,0xc0,0xd,0x41,0x1,0xcf,0x41,0x89,0xeb,0x41,0xc1,0xc3,0x19,0x1,0xcb,0x89,0xe9,0xc1,0xc1,0xe,0x44,0x31,0xc0,0x44,0x31,0xd9,0x41,0x89,0xe8,0x41,0xc1,0xe8,0x3,0x41,0x31,0xc8,0x1,0x54,0x24,0x10,0x41,0x1,0xd0,0x44,0x89,0x44,0x24,0x68,0xc1,0xea,0xa,0x45,0x89,0xf8,0x41,0xc1,0xc0,0x1a,0x31,0xc2,0x44,0x89,0xf8,0xc1,0xc0,0x15,0x44,0x8b,0x74,0x24,0x60,0x41,0x1,0xd6,0x44,0x89,0xf9,0xc1,0xc1,0x7,0x44,0x31,0xc0,0x31,0xc1,0x44,0x89,0xc8,0x31,0xf0,0x44,0x21,0xf8,0x31,0xf0,0x45,0x1,0xf2,0x41,0x1,0xc2,0x42,0x8d,0x4,0x11,0x5,0xda,0x88,0xf9,0x76,0x89,0xd9,0xc1,0xc1,0x1e,0x41,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x41,0x31,0xc8,0x89,0xd9,0xc1,0xc1,0xa,0x44,0x31,0xc1,0x41,0x89,0xfa,0x45,0x21,0xea,0x41,0x89,0xf8,0x45,0x31,0xe8,0x41,0x21,0xd8,0x45,0x31,0xd0,0x41,0x1,0xc8]

set_option maxRecDepth 4096 in
theorem part19_bytes [Bindings] : part19.flatMap CheckedInstruction.bytes = part19Bytes  := by
  rfl

def part19Layout : List (BitVec 64 × Nat) :=
  [(0x10c3f8, 3), (0x10c3fb, 2), (0x10c3fd, 3), (0x10c400, 3), (0x10c403, 3), (0x10c406, 3), (0x10c409, 3), (0x10c40c, 3), (0x10c40f, 2), (0x10c411, 3), (0x10c414, 3), (0x10c417, 4), (0x10c41b, 2), (0x10c41d, 2), (0x10c41f, 3), (0x10c422, 3), (0x10c425, 3), (0x10c428, 4), (0x10c42c, 2), (0x10c42e, 2), (0x10c430, 3), (0x10c433, 3), (0x10c436, 3), (0x10c439, 3), (0x10c43c, 4), (0x10c440, 3), (0x10c443, 4), (0x10c447, 3), (0x10c44a, 5), (0x10c44f, 3), (0x10c452, 3), (0x10c455, 4), (0x10c459, 2), (0x10c45b, 3), (0x10c45e, 3), (0x10c461, 5), (0x10c466, 3), (0x10c469, 3), (0x10c46c, 3), (0x10c46f, 3), (0x10c472, 2), (0x10c474, 3), (0x10c477, 2), (0x10c479, 3), (0x10c47c, 2), (0x10c47e, 3), (0x10c481, 3), (0x10c484, 4), (0x10c488, 5), (0x10c48d, 2), (0x10c48f, 3), (0x10c492, 3), (0x10c495, 4), (0x10c499, 3), (0x10c49c, 2), (0x10c49e, 3), (0x10c4a1, 3), (0x10c4a4, 3), (0x10c4a7, 3), (0x10c4aa, 3), (0x10c4ad, 3), (0x10c4b0, 3), (0x10c4b3, 3), (0x10c4b6, 3)]

theorem part19_layout [Bindings] : InstructionTrace.layout part19 = part19Layout := by
  rfl

theorem part19_ordered [Bindings] : InstructionTrace.ordered 0x10c3f8 part19 = true := by
  rw [InstructionTrace.ordered_eq_layout, part19_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part19_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc3f8 193 = part19Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
