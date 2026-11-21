import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part05
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part06 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10dfba 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10dfbd 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10dfc1 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10dfc4 0x48 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10dfc8 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10dfcb 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10dfce 0x48 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10dfd2 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10dfd5 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10dfda 7) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10dfdd 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10dfe2 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10dfe5 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (lea_r64_effect_step 0x10dfe8 0x4c (by simp [RexWPrefix]) 1 (.sib 7 (some 5) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10dfec 0x4c (by simp [RexWPrefix]) 1 (.rip 0xf201d) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10dff3 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10dff6 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10dff9 0x48 0xd6 (by simp [RexWPrefix]) rfl rfl) (by x86_local)
  ]

def part06Bytes : List UInt8 :=
  [0x4c,0x89,0xc2,0x48,0xc1,0xc2,0x32,0x4c,0x89,0xc6,0x48,0xc1,0xc6,0x2e,0x48,0x31,0xd6,0x4c,0x89,0xc2,0x48,0xc1,0xc2,0x17,0x48,0x31,0xf2,0x48,0x8b,0x7c,0x24,0x48,0x48,0xf,0xcf,0x48,0x89,0x7c,0x24,0x48,0x4c,0x89,0xc6,0x48,0x21,0xce,0x4c,0x8d,0xc,0x2f,0x4c,0x3,0xd,0x1d,0x20,0xf,0x0,0x49,0x1,0xf1,0x4c,0x89,0xc6,0x48,0xf7,0xd6]

def part06Layout : List (BitVec 64 × Nat) :=
  [(0x10dfba, 3), (0x10dfbd, 4), (0x10dfc1, 3), (0x10dfc4, 4), (0x10dfc8, 3),
   (0x10dfcb, 3), (0x10dfce, 4), (0x10dfd2, 3), (0x10dfd5, 5), (0x10dfda, 3),
   (0x10dfdd, 5), (0x10dfe2, 3), (0x10dfe5, 3), (0x10dfe8, 4), (0x10dfec, 7),
   (0x10dff3, 3), (0x10dff6, 3), (0x10dff9, 3)]

set_option maxRecDepth 4096 in
theorem part06_bytes [Bindings] : part06.flatMap CheckedInstruction.bytes = part06Bytes := by
  rfl

theorem part06_layout [Bindings] : InstructionTrace.layout part06 = part06Layout := by
  rfl

theorem part06_ordered [Bindings] : InstructionTrace.ordered 0x10dfba part06 = true := by
  rw [InstructionTrace.ordered_eq_layout, part06_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part06_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xdfba 66 = part06Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
