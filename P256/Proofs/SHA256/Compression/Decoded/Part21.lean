import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part21 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a24 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116a27 0x41 0xc3 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a2b 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a2e 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x116a31 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a35 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x116a38 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116a3d 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x116a40 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x116a45 0x41 0xee 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a49 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116a4c 0 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116a4f 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a52 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116a55 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a58 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116a5b 0x41 0xc2 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a5f 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a62 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116a65 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a68 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a6b 0x45 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a6e 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116a71 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a74 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116a77 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a7a 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116a7d 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116a81 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116a84 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116a87 0x41 0xc2 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x116a8b 0x42 (by simp [RexNoWPrefix]) 5 (.sib 1 (some 9) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116a8f 0xc5 0xa831c66d rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116a95 0xf1 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x116a97 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116a9c 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116a9f 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116aa2 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116aa5 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116aa8 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116aab 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116aae 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116ab1 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116ab4 0x45 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116ab7 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116aba 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116abd 0x41 0xc2 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116ac1 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116ac3 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116ac5 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116ac8 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116acb 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116ace 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116ad2 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116ad5 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116ad8 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116adc 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116adf 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x116ae2 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116ae6 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x116ae9 2 (.sib 4 none 0 (.d32 140)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116af0 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x116af3 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116af8 0xea 0xa rfl rfl) (by x86_local)]

def part21Bytes : List UInt8 :=
  [0x41,0x89,0xd3,0x41,0xc1,0xc3,0xe,0x45,0x31,0xd3,0x41,0x89,0xd2,0x41,0xc1,0xea,0x3,0x45,0x31,0xda,0x44,0x1,0x74,0x24,0x4,0x45,0x1,0xf2,0x44,0x89,0x54,0x24,0x48,0x41,0xc1,0xee,0xa,0x41,0x31,0xce,0x8b,0x4,0x24,0x44,0x1,0xf0,0x44,0x89,0xe9,0xc1,0xc1,0x1a,0x45,0x89,0xea,0x41,0xc1,0xc2,0x15,0x41,0x31,0xca,0x44,0x89,0xe9,0xc1,0xc1,0x7,0x44,0x31,0xd1,0x45,0x89,0xe2,0x45,0x31,0xfa,0x45,0x21,0xea,0x45,0x31,0xfa,0x41,0x1,0xc1,0x41,0x89,0xf3,0x41,0xc1,0xc3,0x1e,0x45,0x1,0xd1,0x41,0x89,0xf2,0x41,0xc1,0xc2,0x13,0x42,0x8d,0x2c,0x9,0x81,0xc5,0x6d,0xc6,0x31,0xa8,0x89,0xf1,0x48,0x89,0x74,0x24,0x28,0xc1,0xc1,0xa,0x45,0x31,0xda,0x44,0x31,0xd1,0x45,0x89,0xc2,0x41,0x21,0xda,0x45,0x89,0xc6,0x41,0x31,0xde,0x41,0x21,0xf6,0x45,0x31,0xd6,0x41,0x1,0xce,0x41,0x89,0xd2,0x41,0xc1,0xc2,0xf,0x1,0xef,0x89,0xd1,0xc1,0xc1,0xd,0x41,0x1,0xee,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x19,0x44,0x31,0xd1,0x41,0x89,0xc2,0x41,0xc1,0xc2,0xe,0x45,0x31,0xda,0x41,0x89,0xc1,0x41,0xc1,0xe9,0x3,0x45,0x31,0xd1,0x1,0x94,0x24,0x8c,0x0,0x0,0x0,0x41,0x1,0xd1,0x44,0x89,0x4c,0x24,0x70,0xc1,0xea,0xa]

set_option maxRecDepth 4096 in
theorem part21_bytes [Bindings] : part21.flatMap CheckedInstruction.bytes = part21Bytes  := by
  rfl

def part21Layout : List (BitVec 64 × Nat) :=
  [(0x116a24, 3), (0x116a27, 4), (0x116a2b, 3), (0x116a2e, 3), (0x116a31, 4), (0x116a35, 3), (0x116a38, 5), (0x116a3d, 3), (0x116a40, 5), (0x116a45, 4), (0x116a49, 3), (0x116a4c, 3), (0x116a4f, 3), (0x116a52, 3), (0x116a55, 3), (0x116a58, 3), (0x116a5b, 4), (0x116a5f, 3), (0x116a62, 3), (0x116a65, 3), (0x116a68, 3), (0x116a6b, 3), (0x116a6e, 3), (0x116a71, 3), (0x116a74, 3), (0x116a77, 3), (0x116a7a, 3), (0x116a7d, 4), (0x116a81, 3), (0x116a84, 3), (0x116a87, 4), (0x116a8b, 4), (0x116a8f, 6), (0x116a95, 2), (0x116a97, 5), (0x116a9c, 3), (0x116a9f, 3), (0x116aa2, 3), (0x116aa5, 3), (0x116aa8, 3), (0x116aab, 3), (0x116aae, 3), (0x116ab1, 3), (0x116ab4, 3), (0x116ab7, 3), (0x116aba, 3), (0x116abd, 4), (0x116ac1, 2), (0x116ac3, 2), (0x116ac5, 3), (0x116ac8, 3), (0x116acb, 3), (0x116ace, 4), (0x116ad2, 3), (0x116ad5, 3), (0x116ad8, 4), (0x116adc, 3), (0x116adf, 3), (0x116ae2, 4), (0x116ae6, 3), (0x116ae9, 7), (0x116af0, 3), (0x116af3, 5), (0x116af8, 3)]

theorem part21_layout [Bindings] : InstructionTrace.layout part21 = part21Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part21_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16a24 215 = part21Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
