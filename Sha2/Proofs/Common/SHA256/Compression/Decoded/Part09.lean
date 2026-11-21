import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part09 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bbf7 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bbf9 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bbfc 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bbfe 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc00 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc03 0xce rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bc05 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bc0a 5 (.base 1 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10bc0d 5) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bc0f 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bc11 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc13 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc16 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bc19 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10bc1b 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bc1d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc20 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10bc23 0x42 (by simp [RexNoWPrefix]) 1 (.sib 6 (some 11) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bc27 0xc1 0x9bdc06a7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc2d 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc30 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc33 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc36 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc39 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc3b 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc3e 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc41 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc43 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bc46 0xdf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc48 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bc4b 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bc4e 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bc51 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc54 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc57 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc5a 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10bc5d 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc60 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc63 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc66 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc69 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc6c 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc6e 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc71 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bc74 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bc76 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10bc7b 0x44 (by simp [RexNoWPrefix]) 5 (.base 6 (.d8 60)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10bc7f 13) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc82 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bc85 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc87 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc8a 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc8d 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10bc90 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bc92 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc94 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bc97 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bc9a 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bc9d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bca0 0xc1 0xc19bf174 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bca6 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bca9 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bcac 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bcae 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part09Bytes : List UInt8 :=
  [0x89,0xd1,0xc1,0xc1,0x15,0x31,0xf1,0x89,0xd6,0xc1,0xc6,0x7,0x31,0xce,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x69,0x38,0xf,0xcd,0x89,0xd1,0x21,0xc1,0x41,0x1,0xeb,0x41,0x1,0xcb,0x89,0xd1,0xf7,0xd1,0x44,0x21,0xd1,0x41,0x1,0xcb,0x42,0x8d,0xc,0x1e,0x81,0xc1,0xa7,0x6,0xdc,0x9b,0x44,0x89,0xf6,0xc1,0xc6,0x1e,0x44,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xf6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xcf,0x21,0xdf,0x45,0x89,0xc8,0x41,0x31,0xd8,0x45,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xf0,0x41,0x1,0xcf,0x41,0x1,0xc8,0x4d,0x89,0xc3,0x44,0x89,0xf9,0xc1,0xc1,0x1a,0x44,0x89,0xfe,0xc1,0xc6,0x15,0x31,0xce,0x44,0x89,0xf9,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x44,0x8b,0x6e,0x3c,0x41,0xf,0xcd,0x44,0x89,0xfe,0x21,0xd6,0x45,0x1,0xea,0x41,0x1,0xf2,0x44,0x89,0xfe,0xf7,0xd6,0x21,0xc6,0x41,0x1,0xf2,0x44,0x89,0xde,0xc1,0xc6,0x1e,0x44,0x1,0xd1,0x81,0xc1,0x74,0xf1,0x9b,0xc1,0x44,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xde]

set_option maxRecDepth 4096 in
theorem part09_bytes [Bindings] : part09.flatMap CheckedInstruction.bytes = part09Bytes  := by
  rfl

def part09Layout : List (BitVec 64 × Nat) :=
  [(0x10bbf7, 2), (0x10bbf9, 3), (0x10bbfc, 2), (0x10bbfe, 2), (0x10bc00, 3), (0x10bc03, 2), (0x10bc05, 5), (0x10bc0a, 3), (0x10bc0d, 2), (0x10bc0f, 2), (0x10bc11, 2), (0x10bc13, 3), (0x10bc16, 3), (0x10bc19, 2), (0x10bc1b, 2), (0x10bc1d, 3), (0x10bc20, 3), (0x10bc23, 4), (0x10bc27, 6), (0x10bc2d, 3), (0x10bc30, 3), (0x10bc33, 3), (0x10bc36, 3), (0x10bc39, 2), (0x10bc3b, 3), (0x10bc3e, 3), (0x10bc41, 2), (0x10bc43, 3), (0x10bc46, 2), (0x10bc48, 3), (0x10bc4b, 3), (0x10bc4e, 3), (0x10bc51, 3), (0x10bc54, 3), (0x10bc57, 3), (0x10bc5a, 3), (0x10bc5d, 3), (0x10bc60, 3), (0x10bc63, 3), (0x10bc66, 3), (0x10bc69, 3), (0x10bc6c, 2), (0x10bc6e, 3), (0x10bc71, 3), (0x10bc74, 2), (0x10bc76, 5), (0x10bc7b, 4), (0x10bc7f, 3), (0x10bc82, 3), (0x10bc85, 2), (0x10bc87, 3), (0x10bc8a, 3), (0x10bc8d, 3), (0x10bc90, 2), (0x10bc92, 2), (0x10bc94, 3), (0x10bc97, 3), (0x10bc9a, 3), (0x10bc9d, 3), (0x10bca0, 6), (0x10bca6, 3), (0x10bca9, 3), (0x10bcac, 2), (0x10bcae, 3)]

theorem part09_layout [Bindings] : InstructionTrace.layout part09 = part09Layout := by
  rfl

theorem part09_ordered [Bindings] : InstructionTrace.ordered 0x10bbf7 part09 = true := by
  rw [InstructionTrace.ordered_eq_layout, part09_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part09_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xbbf7 186 = part09Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
