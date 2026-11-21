import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part44 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10d6c0 0x391c0cb3) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d6c5 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d6c8 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d6cb 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d6ce 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d6d1 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d6d3 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d6d6 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d6d9 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d6db 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d6de 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d6e1 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d6e4 0x45 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d6e7 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d6ea 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d6ed 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d6f0 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d6f2 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d6f5 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d6f7 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d6fa 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d6fc 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d6ff 0xc1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10d701 7 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d705 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d707 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d70a 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10d70c 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d711 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d714 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d716 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d719 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d71b 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d71e 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d720 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d722 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d725 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d727 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d72a 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d72d 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d72f 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d732 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d735 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d738 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d73b 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10d73e 0x42 (by simp [RexNoWPrefix]) 2 (.sib 0 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10d742 0xc2 0x4ed8aa4a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d748 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d74b 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d74e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d750 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d753 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d756 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d758 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d75b 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d75e 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d761 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d764 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d767 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d769 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d76b 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d76e 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d770 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d773 0xd0 rfl) (by x86_local)]

def part44Bytes : List UInt8 :=
  [0x5,0xb3,0xc,0x1c,0x39,0x44,0x89,0xc9,0xc1,0xc1,0x1e,0x44,0x89,0xca,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xd2,0x44,0x21,0xda,0x45,0x89,0xd5,0x45,0x31,0xdd,0x45,0x21,0xcd,0x41,0x31,0xd5,0x41,0x1,0xcd,0x1,0xc3,0x41,0x1,0xc5,0x89,0xf8,0xc1,0xc0,0xf,0x89,0xf9,0xc1,0xc1,0xd,0x31,0xc1,0x1,0x7c,0x24,0x58,0x89,0xf8,0xc1,0xe8,0xa,0x31,0xc8,0x44,0x8b,0x7c,0x24,0x14,0x41,0x1,0xc7,0x89,0xd8,0xc1,0xc0,0x1a,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xc1,0x44,0x31,0xf1,0x21,0xd9,0x44,0x31,0xf1,0x45,0x1,0xfc,0x41,0x1,0xcc,0x44,0x89,0xe9,0xc1,0xc1,0x1e,0x42,0x8d,0x14,0x20,0x81,0xc2,0x4a,0xaa,0xd8,0x4e,0x44,0x89,0xe8,0xc1,0xc0,0x13,0x31,0xc8,0x44,0x89,0xe9,0xc1,0xc1,0xa,0x31,0xc1,0x44,0x89,0xce,0x44,0x21,0xd6,0x44,0x89,0xc8,0x44,0x31,0xd0,0x44,0x21,0xe8,0x31,0xf0,0x1,0xc8,0x41,0x1,0xd3,0x89,0xe9,0xc1,0xc1,0xf,0x1,0xd0]

set_option maxRecDepth 4096 in
theorem part44_bytes [Bindings] : part44.flatMap CheckedInstruction.bytes = part44Bytes  := by
  rfl

def part44Layout : List (BitVec 64 × Nat) :=
  [(0x10d6c0, 5), (0x10d6c5, 3), (0x10d6c8, 3), (0x10d6cb, 3), (0x10d6ce, 3), (0x10d6d1, 2), (0x10d6d3, 3), (0x10d6d6, 3), (0x10d6d9, 2), (0x10d6db, 3), (0x10d6de, 3), (0x10d6e1, 3), (0x10d6e4, 3), (0x10d6e7, 3), (0x10d6ea, 3), (0x10d6ed, 3), (0x10d6f0, 2), (0x10d6f2, 3), (0x10d6f5, 2), (0x10d6f7, 3), (0x10d6fa, 2), (0x10d6fc, 3), (0x10d6ff, 2), (0x10d701, 4), (0x10d705, 2), (0x10d707, 3), (0x10d70a, 2), (0x10d70c, 5), (0x10d711, 3), (0x10d714, 2), (0x10d716, 3), (0x10d719, 2), (0x10d71b, 3), (0x10d71e, 2), (0x10d720, 2), (0x10d722, 3), (0x10d725, 2), (0x10d727, 3), (0x10d72a, 3), (0x10d72d, 2), (0x10d72f, 3), (0x10d732, 3), (0x10d735, 3), (0x10d738, 3), (0x10d73b, 3), (0x10d73e, 4), (0x10d742, 6), (0x10d748, 3), (0x10d74b, 3), (0x10d74e, 2), (0x10d750, 3), (0x10d753, 3), (0x10d756, 2), (0x10d758, 3), (0x10d75b, 3), (0x10d75e, 3), (0x10d761, 3), (0x10d764, 3), (0x10d767, 2), (0x10d769, 2), (0x10d76b, 3), (0x10d76e, 2), (0x10d770, 3), (0x10d773, 2)]

theorem part44_layout [Bindings] : InstructionTrace.layout part44 = part44Layout := by
  rfl

theorem part44_ordered [Bindings] : InstructionTrace.ordered 0x10d6c0 part44 = true := by
  rw [InstructionTrace.ordered_eq_layout, part44_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part44_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd6c0 181 = part44Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
