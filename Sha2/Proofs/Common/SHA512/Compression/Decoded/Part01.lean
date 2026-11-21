import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part00

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part01 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10de17 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 352)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10de1f 0x4c (by simp [RexWPrefix]) 1 (.base 6 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10de22 9) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10de25 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10de2d 0x4c (by simp [RexWPrefix]) 5 (.base 6 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de31 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10de34 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10de38 0x48 (by simp [RexWPrefix]) 1 (.base 6 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10de3c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de41 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10de44 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10de48 0x48 (by simp [RexWPrefix]) 2 (.base 6 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10de4c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part01Bytes : List UInt8 :=
  [0x4c,0x89,0xac,0x24,0x60,0x1,0x0,0x0,0x4c,0x8b,0xe,0x49,0xf,0xc9,0x4c,0x89,0x8c,0x24,0x90,0x0,0x0,0x0,0x4c,0x8b,0x6e,0x8,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x32,0x48,0x8b,0x4e,0x10,0x48,0x89,0x4c,0x24,0x48,0x48,0x89,0xd9,0x48,0xc1,0xc1,0x2e,0x48,0x8b,0x56,0x18,0x48,0x89,0x14,0x24]

theorem part01_bytes [Bindings] : part01.flatMap CheckedInstruction.bytes = part01Bytes := by
  rfl

def part01Layout : List (BitVec 64 × Nat) :=
  [(0x10de17, 8), (0x10de1f, 3), (0x10de22, 3), (0x10de25, 8),
   (0x10de2d, 4), (0x10de31, 3), (0x10de34, 4), (0x10de38, 4),
   (0x10de3c, 5), (0x10de41, 3), (0x10de44, 4), (0x10de48, 4),
   (0x10de4c, 4)]

theorem part01_layout [Bindings] : InstructionTrace.layout part01 = part01Layout := by
  change [(0x10de17, 8), (0x10de1f, 3), (0x10de22, 3), (0x10de25, 8),
    (0x10de2d, 4), (0x10de31, 3), (0x10de34, 4), (0x10de38, 4),
    (0x10de3c, 5), (0x10de41, 3), (0x10de44, 4), (0x10de48, 4),
    (0x10de4c, 4)] = part01Layout
  rfl

theorem part01_ordered [Bindings] : InstructionTrace.ordered 0x10de17 part01 = true := by
  rw [InstructionTrace.ordered_eq_layout, part01_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part01_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xde17 57 = part01Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
