import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part32 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cda1 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cda5 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cda8 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10cdab 0x41 0xeb 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cdaf 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10cdb2 3 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cdb6 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10cdb9 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cdbe 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10cdc1 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cdc5 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cdc8 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cdcb 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10cdce 5 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cdd2 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cdd5 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cdd8 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cddc 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cddf 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cde2 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cde5 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cde8 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cdeb 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cdee 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cdf1 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cdf4 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cdf7 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10cdfa 0x46 (by simp [RexNoWPrefix]) 3 (.sib 2 (some 13) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10cdfe 0x41 0xc3 0x81c2c92e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ce05 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ce07 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce0a 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ce0d 0x41 0xc1 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce11 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce14 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ce17 0x41 0xc7 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce1b 0x45 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce1e 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ce21 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ce24 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ce26 0xfa rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ce28 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce2a 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce2d 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ce30 0xc3 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ce33 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce36 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ce39 0x41 0xc1 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ce3d 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce40 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ce43 0x41 0xc7 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ce47 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce4a 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ce4d 0x41 0xc3 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce51 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce54 0x45 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ce57 0xeb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ce59 0xeb 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ce5c 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10ce5f 0x44 (by simp [RexNoWPrefix]) 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ce64 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ce67 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10ce6a 3 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ce6e 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part32Bytes : List UInt8 :=
  [0x41,0xc1,0xc1,0xe,0x45,0x31,0xd9,0x45,0x89,0xe3,0x41,0xc1,0xeb,0x3,0x45,0x31,0xcb,0x1,0x5c,0x24,0x58,0x41,0x1,0xdb,0x44,0x89,0x5c,0x24,0x78,0x41,0x89,0xd9,0x41,0xc1,0xe9,0xa,0x41,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x1a,0x8b,0x6c,0x24,0x14,0x44,0x1,0xcd,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x7,0x44,0x31,0xca,0x41,0x89,0xc9,0x45,0x31,0xc1,0x45,0x21,0xd1,0x45,0x31,0xc1,0x41,0x1,0xed,0x45,0x1,0xcd,0x46,0x8d,0x1c,0x2a,0x41,0x81,0xc3,0x2e,0xc9,0xc2,0x81,0x89,0xf2,0xc1,0xc2,0x1e,0x41,0x89,0xf1,0x41,0xc1,0xc1,0x13,0x41,0x31,0xd1,0x41,0x89,0xf7,0x41,0xc1,0xc7,0xa,0x45,0x31,0xcf,0x41,0x89,0xc1,0x41,0x21,0xf9,0x89,0xc2,0x31,0xfa,0x21,0xf2,0x44,0x31,0xca,0x44,0x89,0xe3,0xc1,0xc3,0xf,0x44,0x1,0xfa,0x45,0x89,0xe1,0x41,0xc1,0xc1,0xd,0x45,0x1,0xde,0x41,0x89,0xef,0x41,0xc1,0xc7,0x19,0x44,0x1,0xda,0x41,0x89,0xeb,0x41,0xc1,0xc3,0xe,0x41,0x31,0xd9,0x45,0x31,0xfb,0x89,0xeb,0xc1,0xeb,0x3,0x44,0x31,0xdb,0x44,0x8b,0x6c,0x24,0x10,0x45,0x1,0xe5,0x44,0x1,0xe3,0x89,0x5c,0x24,0x14,0x45,0x89,0xe3]

set_option maxRecDepth 4096 in
theorem part32_bytes [Bindings] : part32.flatMap CheckedInstruction.bytes = part32Bytes  := by
  rfl

def part32Layout : List (BitVec 64 × Nat) :=
  [(0x10cda1, 4), (0x10cda5, 3), (0x10cda8, 3), (0x10cdab, 4), (0x10cdaf, 3), (0x10cdb2, 4), (0x10cdb6, 3), (0x10cdb9, 5), (0x10cdbe, 3), (0x10cdc1, 4), (0x10cdc5, 3), (0x10cdc8, 3), (0x10cdcb, 3), (0x10cdce, 4), (0x10cdd2, 3), (0x10cdd5, 3), (0x10cdd8, 4), (0x10cddc, 3), (0x10cddf, 3), (0x10cde2, 3), (0x10cde5, 3), (0x10cde8, 3), (0x10cdeb, 3), (0x10cdee, 3), (0x10cdf1, 3), (0x10cdf4, 3), (0x10cdf7, 3), (0x10cdfa, 4), (0x10cdfe, 7), (0x10ce05, 2), (0x10ce07, 3), (0x10ce0a, 3), (0x10ce0d, 4), (0x10ce11, 3), (0x10ce14, 3), (0x10ce17, 4), (0x10ce1b, 3), (0x10ce1e, 3), (0x10ce21, 3), (0x10ce24, 2), (0x10ce26, 2), (0x10ce28, 2), (0x10ce2a, 3), (0x10ce2d, 3), (0x10ce30, 3), (0x10ce33, 3), (0x10ce36, 3), (0x10ce39, 4), (0x10ce3d, 3), (0x10ce40, 3), (0x10ce43, 4), (0x10ce47, 3), (0x10ce4a, 3), (0x10ce4d, 4), (0x10ce51, 3), (0x10ce54, 3), (0x10ce57, 2), (0x10ce59, 3), (0x10ce5c, 3), (0x10ce5f, 5), (0x10ce64, 3), (0x10ce67, 3), (0x10ce6a, 4), (0x10ce6e, 3)]

theorem part32_layout [Bindings] : InstructionTrace.layout part32 = part32Layout := by
  rfl

theorem part32_ordered [Bindings] : InstructionTrace.ordered 0x10cda1 part32 = true := by
  rw [InstructionTrace.ordered_eq_layout, part32_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part32_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xcda1 208 = part32Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
