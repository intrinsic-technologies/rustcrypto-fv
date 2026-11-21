import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part10 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcb1 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcb4 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcb6 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bcb9 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcbc 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bcbf 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bcc2 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bcc5 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bcc8 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bccb 0xcb rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bccd 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcd2 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcd5 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bcd8 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcdb 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcde 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bce1 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bce3 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bce6 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bce9 0xce rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bceb 5 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bcef 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcf1 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bcf4 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bcf6 0xc7 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcf9 0xcf rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bcfb 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcfe 0xfd rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bd00 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10bd05 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd0a 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd0d 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd10 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd12 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd15 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd17 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd1a 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd1c 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd1e 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd21 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd23 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd26 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bd28 0xde rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10bd2a 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd32 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd34 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd37 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd3a 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bd3d 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd3f 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd42 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bd45 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10bd47 0xe49b69c1) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd4c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10bd4f 0x4c 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd52 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd55 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd57 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd59 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10bd5c 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bd61 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd64 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bd67 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bd6a 0xef rfl) (by x86_local)]

def part10Bytes : List UInt8 :=
  [0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xf7,0x44,0x21,0xcf,0x45,0x89,0xf0,0x45,0x31,0xc8,0x45,0x21,0xd8,0x41,0x31,0xf8,0x41,0x1,0xf0,0x1,0xcb,0x4c,0x8b,0x64,0x24,0x38,0x44,0x89,0xe6,0xc1,0xc6,0x19,0x41,0x1,0xc8,0x44,0x89,0xe1,0xc1,0xc1,0xe,0x31,0xf1,0x44,0x89,0xe6,0xc1,0xee,0x3,0x31,0xce,0x89,0x6c,0x24,0x64,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xef,0xc1,0xc7,0xd,0x31,0xcf,0xc1,0xed,0xa,0x31,0xfd,0x4c,0x8b,0x54,0x24,0x50,0x44,0x3,0x54,0x24,0x8,0x41,0x1,0xf2,0x41,0x1,0xea,0x89,0xd9,0xc1,0xc1,0x1a,0x89,0xde,0xc1,0xc6,0x15,0x31,0xce,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf1,0x44,0x89,0xfe,0x31,0xd6,0x21,0xde,0x48,0x89,0x9c,0x24,0x80,0x0,0x0,0x0,0x31,0xd6,0x44,0x1,0xd0,0x44,0x89,0xc7,0xc1,0xc7,0x1e,0x1,0xf0,0x44,0x89,0xc6,0xc1,0xc6,0x13,0x1,0xc8,0x5,0xc1,0x69,0x9b,0xe4,0x44,0x89,0xc1,0x4c,0x89,0xc5,0xc1,0xc1,0xa,0x31,0xfe,0x31,0xf1,0x44,0x89,0xde,0x4c,0x89,0x74,0x24,0x58,0x44,0x21,0xf6,0x44,0x89,0xdf,0x44,0x31,0xf7,0x21,0xef]

set_option maxRecDepth 4096 in
theorem part10_bytes [Bindings] : part10.flatMap CheckedInstruction.bytes = part10Bytes  := by
  rfl

def part10Layout : List (BitVec 64 × Nat) :=
  [(0x10bcb1, 3), (0x10bcb4, 2), (0x10bcb6, 3), (0x10bcb9, 3), (0x10bcbc, 3), (0x10bcbf, 3), (0x10bcc2, 3), (0x10bcc5, 3), (0x10bcc8, 3), (0x10bccb, 2), (0x10bccd, 5), (0x10bcd2, 3), (0x10bcd5, 3), (0x10bcd8, 3), (0x10bcdb, 3), (0x10bcde, 3), (0x10bce1, 2), (0x10bce3, 3), (0x10bce6, 3), (0x10bce9, 2), (0x10bceb, 4), (0x10bcef, 2), (0x10bcf1, 3), (0x10bcf4, 2), (0x10bcf6, 3), (0x10bcf9, 2), (0x10bcfb, 3), (0x10bcfe, 2), (0x10bd00, 5), (0x10bd05, 5), (0x10bd0a, 3), (0x10bd0d, 3), (0x10bd10, 2), (0x10bd12, 3), (0x10bd15, 2), (0x10bd17, 3), (0x10bd1a, 2), (0x10bd1c, 2), (0x10bd1e, 3), (0x10bd21, 2), (0x10bd23, 3), (0x10bd26, 2), (0x10bd28, 2), (0x10bd2a, 8), (0x10bd32, 2), (0x10bd34, 3), (0x10bd37, 3), (0x10bd3a, 3), (0x10bd3d, 2), (0x10bd3f, 3), (0x10bd42, 3), (0x10bd45, 2), (0x10bd47, 5), (0x10bd4c, 3), (0x10bd4f, 3), (0x10bd52, 3), (0x10bd55, 2), (0x10bd57, 2), (0x10bd59, 3), (0x10bd5c, 5), (0x10bd61, 3), (0x10bd64, 3), (0x10bd67, 3), (0x10bd6a, 2)]

theorem part10_layout [Bindings] : InstructionTrace.layout part10 = part10Layout := by
  rfl

theorem part10_ordered [Bindings] : InstructionTrace.ordered 0x10bcb1 part10 = true := by
  rw [InstructionTrace.ordered_eq_layout, part10_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part10_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xbcb1 187 = part10Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
