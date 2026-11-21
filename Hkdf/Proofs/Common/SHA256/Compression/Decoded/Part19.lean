import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part19 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a4d8 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a4db 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a4dd 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a4e0 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a4e3 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a4e6 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a4e9 0x44 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a4ec 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10a4ef 0xfb rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a4f1 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a4f4 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a4f7 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a4fb 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a4fd 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a4ff 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a502 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a505 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a508 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a50c 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a50e 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a510 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a513 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a516 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a519 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a51c 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a520 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a523 2 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a527 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10a52a 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a52f 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a532 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a535 0x41 0xc0 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a539 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a53b 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a53e 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10a541 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a546 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a549 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a54c 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a54f 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a552 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a554 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a557 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a559 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a55c 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a55e 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a561 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10a564 0x42 (by simp [RexNoWPrefix]) 0 (.sib 1 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10a568 0x76f988da) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a56d 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a56f 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a572 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a575 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a579 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a57c 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a57e 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a581 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a584 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a587 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a58a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a58d 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a590 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a593 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a596 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part19Bytes : List UInt8 :=
  [0x41,0x31,0xc0,0x89,0xf8,0xc1,0xc0,0xa,0x44,0x31,0xc0,0x45,0x89,0xe8,0x45,0x21,0xe0,0x44,0x89,0xeb,0x44,0x31,0xe3,0x21,0xfb,0x44,0x31,0xc3,0x41,0x89,0xd0,0x41,0xc1,0xc0,0xf,0x1,0xc3,0x89,0xd0,0xc1,0xc0,0xd,0x41,0x1,0xcf,0x41,0x89,0xeb,0x41,0xc1,0xc3,0x19,0x1,0xcb,0x89,0xe9,0xc1,0xc1,0xe,0x44,0x31,0xc0,0x44,0x31,0xd9,0x41,0x89,0xe8,0x41,0xc1,0xe8,0x3,0x41,0x31,0xc8,0x1,0x54,0x24,0x10,0x41,0x1,0xd0,0x44,0x89,0x44,0x24,0x68,0xc1,0xea,0xa,0x45,0x89,0xf8,0x41,0xc1,0xc0,0x1a,0x31,0xc2,0x44,0x89,0xf8,0xc1,0xc0,0x15,0x44,0x8b,0x74,0x24,0x60,0x41,0x1,0xd6,0x44,0x89,0xf9,0xc1,0xc1,0x7,0x44,0x31,0xc0,0x31,0xc1,0x44,0x89,0xc8,0x31,0xf0,0x44,0x21,0xf8,0x31,0xf0,0x45,0x1,0xf2,0x41,0x1,0xc2,0x42,0x8d,0x4,0x11,0x5,0xda,0x88,0xf9,0x76,0x89,0xd9,0xc1,0xc1,0x1e,0x41,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x41,0x31,0xc8,0x89,0xd9,0xc1,0xc1,0xa,0x44,0x31,0xc1,0x41,0x89,0xfa,0x45,0x21,0xea,0x41,0x89,0xf8,0x45,0x31,0xe8,0x41,0x21,0xd8,0x45,0x31,0xd0,0x41,0x1,0xc8]

set_option maxRecDepth 4096 in
theorem part19_bytes [Bindings] : part19.flatMap CheckedInstruction.bytes = part19Bytes  := by
  rfl

def part19Layout : List (BitVec 64 × Nat) :=
  [(0x10a4d8, 3), (0x10a4db, 2), (0x10a4dd, 3), (0x10a4e0, 3), (0x10a4e3, 3), (0x10a4e6, 3), (0x10a4e9, 3), (0x10a4ec, 3), (0x10a4ef, 2), (0x10a4f1, 3), (0x10a4f4, 3), (0x10a4f7, 4), (0x10a4fb, 2), (0x10a4fd, 2), (0x10a4ff, 3), (0x10a502, 3), (0x10a505, 3), (0x10a508, 4), (0x10a50c, 2), (0x10a50e, 2), (0x10a510, 3), (0x10a513, 3), (0x10a516, 3), (0x10a519, 3), (0x10a51c, 4), (0x10a520, 3), (0x10a523, 4), (0x10a527, 3), (0x10a52a, 5), (0x10a52f, 3), (0x10a532, 3), (0x10a535, 4), (0x10a539, 2), (0x10a53b, 3), (0x10a53e, 3), (0x10a541, 5), (0x10a546, 3), (0x10a549, 3), (0x10a54c, 3), (0x10a54f, 3), (0x10a552, 2), (0x10a554, 3), (0x10a557, 2), (0x10a559, 3), (0x10a55c, 2), (0x10a55e, 3), (0x10a561, 3), (0x10a564, 4), (0x10a568, 5), (0x10a56d, 2), (0x10a56f, 3), (0x10a572, 3), (0x10a575, 4), (0x10a579, 3), (0x10a57c, 2), (0x10a57e, 3), (0x10a581, 3), (0x10a584, 3), (0x10a587, 3), (0x10a58a, 3), (0x10a58d, 3), (0x10a590, 3), (0x10a593, 3), (0x10a596, 3)]

theorem part19_layout [Bindings] : InstructionTrace.layout part19 = part19Layout := by
  rfl

theorem part19_ordered [Bindings] : InstructionTrace.ordered 0x10a4d8 part19 = true := by
  rw [InstructionTrace.ordered_eq_layout, part19_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part19_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa4d8 193 = part19Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
