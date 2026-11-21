import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part00 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ddf0 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ddf8 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 360)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de00 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de03 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de06 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10de09 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 344)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de11 0x4c 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10de14 0x4d 0xec (by simp [RexWPrefix]) rfl) (by x86_local)
  ]

def part00Bytes : List UInt8 :=
  [0x48,0x89,0x9c,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0xb4,0x24,0x68,0x1,0x0,0x0,0x49,0x89,0xcf,0x4d,0x89,0xd6,0x49,0x89,0xc2,0x48,0x89,0x84,0x24,0x58,0x1,0x0,0x0,0x4c,0x89,0xcd,0x4d,0x89,0xec]

theorem part00_bytes [Bindings] : part00.flatMap CheckedInstruction.bytes = part00Bytes := by
  rfl

def part00Layout : List (BitVec 64 × Nat) :=
  [(0x10ddf0, 8), (0x10ddf8, 8), (0x10de00, 3), (0x10de03, 3),
   (0x10de06, 3), (0x10de09, 8), (0x10de11, 3), (0x10de14, 3)]

theorem part00_layout [Bindings] : InstructionTrace.layout part00 = part00Layout := by
  rfl

theorem part00_ordered [Bindings] : InstructionTrace.ordered 0x10ddf0 part00 = true := by
  rw [InstructionTrace.ordered_eq_layout, part00_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part00_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xddf0 39 = part00Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
