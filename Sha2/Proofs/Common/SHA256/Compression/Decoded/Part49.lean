import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part49 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da62 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10da65 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10da67 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da69 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da6c 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10da6f 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da72 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10da75 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10da78 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10da7b 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10da7e 0xeb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10da80 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10da82 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da85 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10da88 0x41 0xc1 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da8c 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10da8f 0xeb 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da92 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da95 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10da98 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10da9b 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10da9f 0x41 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10daa2 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10daa5 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10daa9 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10daac 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10daaf 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dab2 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dab5 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dab8 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10dabb 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dabe 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dac1 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dac4 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dac7 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10daca 0xc7 0x90befffa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dad0 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10dad3 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dad7 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dada 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dadd 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dae0 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10dae3 0x41 0xc6 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dae7 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10daea 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10daed 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10daef 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10daf2 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10daf5 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10daf8 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dafb 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10dafe 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10db00 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db03 0x44 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db06 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db09 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10db0c 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db0f 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db12 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10db14 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10db17 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10db19 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10db1b 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10db1e 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part49Bytes : List UInt8 :=
  [0x45,0x31,0xd9,0x89,0xd3,0x21,0xcb,0x41,0x89,0xd3,0x41,0x31,0xcb,0x45,0x21,0xd3,0x41,0x31,0xdb,0x45,0x1,0xcb,0x41,0x1,0xf8,0x41,0x1,0xfb,0x89,0xeb,0x89,0xef,0xc1,0xc7,0xf,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xd,0x41,0x31,0xf9,0xc1,0xeb,0xa,0x44,0x31,0xcb,0x44,0x89,0xc7,0xc1,0xc7,0x1a,0x44,0x8b,0x24,0x24,0x41,0x1,0xdc,0x45,0x89,0xc1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xf9,0x44,0x89,0xc7,0xc1,0xc7,0x7,0x44,0x31,0xcf,0x41,0x89,0xf1,0x41,0x31,0xc1,0x45,0x21,0xc1,0x41,0x31,0xc1,0x45,0x1,0xe5,0x45,0x1,0xcd,0x44,0x1,0xef,0x81,0xc7,0xfa,0xff,0xbe,0x90,0x45,0x89,0xd9,0x41,0xc1,0xc1,0x1e,0x44,0x89,0xdb,0xc1,0xc3,0x13,0x44,0x31,0xcb,0x45,0x89,0xde,0x41,0xc1,0xc6,0xa,0x41,0x31,0xde,0x44,0x89,0xd3,0x21,0xd3,0x45,0x89,0xd1,0x41,0x31,0xd1,0x45,0x21,0xd9,0x41,0x31,0xd9,0x45,0x1,0xf1,0x1,0xf9,0x41,0x1,0xf9,0x44,0x89,0xfd,0x44,0x89,0xff,0xc1,0xc7,0xf,0x44,0x89,0xfb,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xed,0xa,0x31,0xdd,0x89,0xcf,0xc1,0xc7,0x1a,0x44,0x8b,0x7c,0x24,0x4]

set_option maxRecDepth 4096 in
theorem part49_bytes [Bindings] : part49.flatMap CheckedInstruction.bytes = part49Bytes  := by
  rfl

def part49Layout : List (BitVec 64 × Nat) :=
  [(0x10da62, 3), (0x10da65, 2), (0x10da67, 2), (0x10da69, 3), (0x10da6c, 3), (0x10da6f, 3), (0x10da72, 3), (0x10da75, 3), (0x10da78, 3), (0x10da7b, 3), (0x10da7e, 2), (0x10da80, 2), (0x10da82, 3), (0x10da85, 3), (0x10da88, 4), (0x10da8c, 3), (0x10da8f, 3), (0x10da92, 3), (0x10da95, 3), (0x10da98, 3), (0x10da9b, 4), (0x10da9f, 3), (0x10daa2, 3), (0x10daa5, 4), (0x10daa9, 3), (0x10daac, 3), (0x10daaf, 3), (0x10dab2, 3), (0x10dab5, 3), (0x10dab8, 3), (0x10dabb, 3), (0x10dabe, 3), (0x10dac1, 3), (0x10dac4, 3), (0x10dac7, 3), (0x10daca, 6), (0x10dad0, 3), (0x10dad3, 4), (0x10dad7, 3), (0x10dada, 3), (0x10dadd, 3), (0x10dae0, 3), (0x10dae3, 4), (0x10dae7, 3), (0x10daea, 3), (0x10daed, 2), (0x10daef, 3), (0x10daf2, 3), (0x10daf5, 3), (0x10daf8, 3), (0x10dafb, 3), (0x10dafe, 2), (0x10db00, 3), (0x10db03, 3), (0x10db06, 3), (0x10db09, 3), (0x10db0c, 3), (0x10db0f, 3), (0x10db12, 2), (0x10db14, 3), (0x10db17, 2), (0x10db19, 2), (0x10db1b, 3), (0x10db1e, 5)]

theorem part49_layout [Bindings] : InstructionTrace.layout part49 = part49Layout := by
  rfl

theorem part49_ordered [Bindings] : InstructionTrace.ordered 0x10da62 part49 = true := by
  rw [InstructionTrace.ordered_eq_layout, part49_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part49_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xda62 193 = part49Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
