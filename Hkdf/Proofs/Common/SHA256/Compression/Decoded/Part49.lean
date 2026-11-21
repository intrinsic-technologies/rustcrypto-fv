import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part49 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb42 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb45 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bb47 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb49 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb4c 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bb4f 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb52 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb55 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb58 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb5b 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb5e 0xeb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb60 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb62 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb65 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bb68 0x41 0xc1 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb6c 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bb6f 0xeb 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb72 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb75 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb78 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10bb7b 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb7f 0x41 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb82 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bb85 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb89 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb8c 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb8f 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb92 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb95 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb98 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bb9b 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb9e 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bba1 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bba4 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bba7 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bbaa 0xc7 0x90befffa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbb0 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bbb3 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbb7 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbba 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bbbd 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbc0 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bbc3 0x41 0xc6 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bbc7 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbca 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bbcd 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbcf 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bbd2 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bbd5 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bbd8 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bbdb 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bbde 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bbe0 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbe3 0x44 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbe6 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbe9 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bbec 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbef 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bbf2 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bbf4 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bbf7 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bbf9 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbfb 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10bbfe 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part49Bytes : List UInt8 :=
  [0x45,0x31,0xd9,0x89,0xd3,0x21,0xcb,0x41,0x89,0xd3,0x41,0x31,0xcb,0x45,0x21,0xd3,0x41,0x31,0xdb,0x45,0x1,0xcb,0x41,0x1,0xf8,0x41,0x1,0xfb,0x89,0xeb,0x89,0xef,0xc1,0xc7,0xf,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xd,0x41,0x31,0xf9,0xc1,0xeb,0xa,0x44,0x31,0xcb,0x44,0x89,0xc7,0xc1,0xc7,0x1a,0x44,0x8b,0x24,0x24,0x41,0x1,0xdc,0x45,0x89,0xc1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xf9,0x44,0x89,0xc7,0xc1,0xc7,0x7,0x44,0x31,0xcf,0x41,0x89,0xf1,0x41,0x31,0xc1,0x45,0x21,0xc1,0x41,0x31,0xc1,0x45,0x1,0xe5,0x45,0x1,0xcd,0x44,0x1,0xef,0x81,0xc7,0xfa,0xff,0xbe,0x90,0x45,0x89,0xd9,0x41,0xc1,0xc1,0x1e,0x44,0x89,0xdb,0xc1,0xc3,0x13,0x44,0x31,0xcb,0x45,0x89,0xde,0x41,0xc1,0xc6,0xa,0x41,0x31,0xde,0x44,0x89,0xd3,0x21,0xd3,0x45,0x89,0xd1,0x41,0x31,0xd1,0x45,0x21,0xd9,0x41,0x31,0xd9,0x45,0x1,0xf1,0x1,0xf9,0x41,0x1,0xf9,0x44,0x89,0xfd,0x44,0x89,0xff,0xc1,0xc7,0xf,0x44,0x89,0xfb,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xed,0xa,0x31,0xdd,0x89,0xcf,0xc1,0xc7,0x1a,0x44,0x8b,0x7c,0x24,0x4]

set_option maxRecDepth 4096 in
theorem part49_bytes [Bindings] : part49.flatMap CheckedInstruction.bytes = part49Bytes  := by
  rfl

def part49Layout : List (BitVec 64 × Nat) :=
  [(0x10bb42, 3), (0x10bb45, 2), (0x10bb47, 2), (0x10bb49, 3), (0x10bb4c, 3), (0x10bb4f, 3), (0x10bb52, 3), (0x10bb55, 3), (0x10bb58, 3), (0x10bb5b, 3), (0x10bb5e, 2), (0x10bb60, 2), (0x10bb62, 3), (0x10bb65, 3), (0x10bb68, 4), (0x10bb6c, 3), (0x10bb6f, 3), (0x10bb72, 3), (0x10bb75, 3), (0x10bb78, 3), (0x10bb7b, 4), (0x10bb7f, 3), (0x10bb82, 3), (0x10bb85, 4), (0x10bb89, 3), (0x10bb8c, 3), (0x10bb8f, 3), (0x10bb92, 3), (0x10bb95, 3), (0x10bb98, 3), (0x10bb9b, 3), (0x10bb9e, 3), (0x10bba1, 3), (0x10bba4, 3), (0x10bba7, 3), (0x10bbaa, 6), (0x10bbb0, 3), (0x10bbb3, 4), (0x10bbb7, 3), (0x10bbba, 3), (0x10bbbd, 3), (0x10bbc0, 3), (0x10bbc3, 4), (0x10bbc7, 3), (0x10bbca, 3), (0x10bbcd, 2), (0x10bbcf, 3), (0x10bbd2, 3), (0x10bbd5, 3), (0x10bbd8, 3), (0x10bbdb, 3), (0x10bbde, 2), (0x10bbe0, 3), (0x10bbe3, 3), (0x10bbe6, 3), (0x10bbe9, 3), (0x10bbec, 3), (0x10bbef, 3), (0x10bbf2, 2), (0x10bbf4, 3), (0x10bbf7, 2), (0x10bbf9, 2), (0x10bbfb, 3), (0x10bbfe, 5)]

theorem part49_layout [Bindings] : InstructionTrace.layout part49 = part49Layout := by
  rfl

theorem part49_ordered [Bindings] : InstructionTrace.ordered 0x10bb42 part49 = true := by
  rw [InstructionTrace.ordered_eq_layout, part49_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part49_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xbb42 193 = part49Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
