import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part37 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d1b9 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d1bc 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d1bf 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d1c2 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d1c4 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d1c7 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d1c9 0xc7 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d1cc 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d1ce 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d1d1 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d1d4 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d1d7 0x41 0xc0 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d1db 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d1de 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d1e1 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d1e4 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10d1e7 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d1eb 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10d1ed 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d1f1 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d1f3 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d1f6 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d1f8 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d1fb 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d1fe 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d201 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d204 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d207 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d20a 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d20c 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d20f 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d212 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d214 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d216 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d218 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d21b 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d21d 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d220 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d222 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d225 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d228 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10d22a 0xd192e819) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d22f 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d232 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d235 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d237 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d23a 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d23d 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d23f 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d242 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d245 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d248 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d24b 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d24e 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d251 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d254 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d256 0x44 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d259 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d25c 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d25f 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d262 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d265 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d268 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d26a 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part37Bytes : List UInt8 :=
  [0x41,0x1,0xf9,0x41,0x1,0xcb,0x41,0x1,0xc9,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xef,0xc1,0xc7,0xd,0x31,0xcf,0x44,0x89,0xf1,0xc1,0xc1,0x19,0x45,0x89,0xf0,0x41,0xc1,0xc0,0xe,0x41,0x31,0xc8,0x44,0x89,0xf1,0xc1,0xe9,0x3,0x44,0x31,0xc1,0x1,0x6c,0x24,0xc,0x1,0xe9,0x89,0x4c,0x24,0x58,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xf9,0x45,0x89,0xea,0x41,0x1,0xca,0x44,0x89,0xd9,0xc1,0xc1,0x1a,0x44,0x89,0xdf,0xc1,0xc7,0x15,0x31,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf9,0x89,0xd7,0x31,0xf7,0x44,0x21,0xdf,0x31,0xf7,0x44,0x1,0xd0,0x1,0xf8,0x44,0x89,0xcf,0xc1,0xc7,0x1e,0x1,0xc8,0x5,0x19,0xe8,0x92,0xd1,0x44,0x89,0xc9,0xc1,0xc1,0x13,0x31,0xf9,0x44,0x89,0xcf,0xc1,0xc7,0xa,0x31,0xcf,0x44,0x89,0xe1,0x44,0x21,0xf9,0x45,0x89,0xe5,0x45,0x31,0xfd,0x45,0x21,0xcd,0x41,0x31,0xcd,0x41,0x1,0xfd,0x1,0xc3,0x44,0x89,0xf5,0x44,0x89,0xf1,0xc1,0xc1,0xf,0x41,0x1,0xc5,0x44,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xd1]

set_option maxRecDepth 4096 in
theorem part37_bytes [Bindings] : part37.flatMap CheckedInstruction.bytes = part37Bytes  := by
  rfl

def part37Layout : List (BitVec 64 × Nat) :=
  [(0x10d1b9, 3), (0x10d1bc, 3), (0x10d1bf, 3), (0x10d1c2, 2), (0x10d1c4, 3), (0x10d1c7, 2), (0x10d1c9, 3), (0x10d1cc, 2), (0x10d1ce, 3), (0x10d1d1, 3), (0x10d1d4, 3), (0x10d1d7, 4), (0x10d1db, 3), (0x10d1de, 3), (0x10d1e1, 3), (0x10d1e4, 3), (0x10d1e7, 4), (0x10d1eb, 2), (0x10d1ed, 4), (0x10d1f1, 2), (0x10d1f3, 3), (0x10d1f6, 2), (0x10d1f8, 3), (0x10d1fb, 3), (0x10d1fe, 3), (0x10d201, 3), (0x10d204, 3), (0x10d207, 3), (0x10d20a, 2), (0x10d20c, 3), (0x10d20f, 3), (0x10d212, 2), (0x10d214, 2), (0x10d216, 2), (0x10d218, 3), (0x10d21b, 2), (0x10d21d, 3), (0x10d220, 2), (0x10d222, 3), (0x10d225, 3), (0x10d228, 2), (0x10d22a, 5), (0x10d22f, 3), (0x10d232, 3), (0x10d235, 2), (0x10d237, 3), (0x10d23a, 3), (0x10d23d, 2), (0x10d23f, 3), (0x10d242, 3), (0x10d245, 3), (0x10d248, 3), (0x10d24b, 3), (0x10d24e, 3), (0x10d251, 3), (0x10d254, 2), (0x10d256, 3), (0x10d259, 3), (0x10d25c, 3), (0x10d25f, 3), (0x10d262, 3), (0x10d265, 3), (0x10d268, 2), (0x10d26a, 3)]

theorem part37_layout [Bindings] : InstructionTrace.layout part37 = part37Layout := by
  rfl

theorem part37_ordered [Bindings] : InstructionTrace.ordered 0x10d1b9 part37 = true := by
  rw [InstructionTrace.ordered_eq_layout, part37_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part37_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd1b9 180 = part37Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
