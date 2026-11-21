import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part33 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10af51 0x41 0xeb 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af55 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10af58 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af5b 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af5e 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10af61 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10af65 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af6a 0x45 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af6d 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10af70 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af74 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af77 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af7a 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af7d 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10af80 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10af83 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af86 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af89 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10af8c 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10af8f 0x41 0xc0 0x92722c85 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af96 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10af99 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10af9d 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10afa0 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10afa4 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10afa7 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10afaa 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10afae 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10afb1 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10afb3 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10afb5 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10afb8 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10afbb 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10afbe 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10afc1 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10afc4 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10afc7 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10afca 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10afcd 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10afd1 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10afd4 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10afd7 0x41 0xc0 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10afdb 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10afde 0x44 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10afe1 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10afe4 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10afe8 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10afeb 0xc3 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10afee 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aff1 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10aff4 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aff8 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10affb 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b000 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10b003 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b008 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10b00b 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b00f 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b012 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b017 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b01a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b01d 0x41 0xc0 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b021 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b024 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part33Bytes : List UInt8 :=
  [0x41,0xc1,0xeb,0xa,0x44,0x89,0xf3,0xc1,0xc3,0x1a,0x45,0x31,0xcb,0x45,0x89,0xf1,0x41,0xc1,0xc1,0x15,0x44,0x8b,0x64,0x24,0x48,0x45,0x1,0xdc,0x45,0x89,0xf3,0x41,0xc1,0xc3,0x7,0x41,0x31,0xd9,0x45,0x31,0xcb,0x45,0x89,0xd1,0x41,0x31,0xc9,0x45,0x21,0xf1,0x41,0x31,0xc9,0x45,0x1,0xe0,0x45,0x1,0xc8,0x45,0x1,0xd8,0x41,0x81,0xc0,0x85,0x2c,0x72,0x92,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x41,0x89,0xd1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xd9,0x89,0xf3,0x21,0xc3,0x41,0x89,0xf3,0x41,0x31,0xc3,0x41,0x21,0xd3,0x41,0x31,0xdb,0x45,0x1,0xcb,0x44,0x1,0xc7,0x45,0x1,0xc3,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x41,0x89,0xe8,0x41,0x89,0xef,0x41,0xc1,0xc0,0xd,0x45,0x31,0xc8,0x44,0x89,0xe5,0x45,0x89,0xe1,0x41,0xc1,0xc1,0x19,0x44,0x89,0xe3,0xc1,0xc3,0xe,0x44,0x31,0xcb,0x45,0x89,0xe1,0x41,0xc1,0xe9,0x3,0x41,0x31,0xd9,0x44,0x1,0x7c,0x24,0x24,0x45,0x1,0xf9,0x44,0x89,0x4c,0x24,0x48,0x45,0x89,0xf9,0x41,0xc1,0xe9,0xa,0x45,0x31,0xc1,0x44,0x8b,0x64,0x24,0x70,0x45,0x1,0xcc,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x1a,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x15]

set_option maxRecDepth 4096 in
theorem part33_bytes [Bindings] : part33.flatMap CheckedInstruction.bytes = part33Bytes  := by
  rfl

def part33Layout : List (BitVec 64 × Nat) :=
  [(0x10af51, 4), (0x10af55, 3), (0x10af58, 3), (0x10af5b, 3), (0x10af5e, 3), (0x10af61, 4), (0x10af65, 5), (0x10af6a, 3), (0x10af6d, 3), (0x10af70, 4), (0x10af74, 3), (0x10af77, 3), (0x10af7a, 3), (0x10af7d, 3), (0x10af80, 3), (0x10af83, 3), (0x10af86, 3), (0x10af89, 3), (0x10af8c, 3), (0x10af8f, 7), (0x10af96, 3), (0x10af99, 4), (0x10af9d, 3), (0x10afa0, 4), (0x10afa4, 3), (0x10afa7, 3), (0x10afaa, 4), (0x10afae, 3), (0x10afb1, 2), (0x10afb3, 2), (0x10afb5, 3), (0x10afb8, 3), (0x10afbb, 3), (0x10afbe, 3), (0x10afc1, 3), (0x10afc4, 3), (0x10afc7, 3), (0x10afca, 3), (0x10afcd, 4), (0x10afd1, 3), (0x10afd4, 3), (0x10afd7, 4), (0x10afdb, 3), (0x10afde, 3), (0x10afe1, 3), (0x10afe4, 4), (0x10afe8, 3), (0x10afeb, 3), (0x10afee, 3), (0x10aff1, 3), (0x10aff4, 4), (0x10aff8, 3), (0x10affb, 5), (0x10b000, 3), (0x10b003, 5), (0x10b008, 3), (0x10b00b, 4), (0x10b00f, 3), (0x10b012, 5), (0x10b017, 3), (0x10b01a, 3), (0x10b01d, 4), (0x10b021, 3), (0x10b024, 4)]

theorem part33_layout [Bindings] : InstructionTrace.layout part33 = part33Layout := by
  rfl

theorem part33_ordered [Bindings] : InstructionTrace.ordered 0x10af51 part33 = true := by
  rw [InstructionTrace.ordered_eq_layout, part33_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part33_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xaf51 215 = part33Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
