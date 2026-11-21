import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part55

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part56 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r64_r64_effect_step 0x1117e4 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1117e7 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x1117ea 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d32 320)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x1117f2 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 336)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x1117fa 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d32 352)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
  ]

def part56Bytes : List UInt8 :=
  [0x4d,0x1,0xf3,0x4c,0x1,0xf3,0x4c,0x3,0x8c,0x24,0x40,0x1,0x0,0x0,0x4c,0x3,0x84,0x24,0x50,0x1,0x0,0x0,0x4c,0x3,0xac,0x24,0x60,0x1,0x0,0x0]

set_option maxRecDepth 4096 in
theorem part56_bytes [Bindings] : part56.flatMap CheckedInstruction.bytes = part56Bytes := by
  rfl

def part56Layout : List (BitVec 64 × Nat) :=
  [(0x1117e4, 3), (0x1117e7, 3), (0x1117ea, 8), (0x1117f2, 8), (0x1117fa, 8)]

theorem part56_layout [Bindings] : InstructionTrace.layout part56 = part56Layout := by
  rfl

theorem part56_ordered [Bindings] : InstructionTrace.ordered 0x1117e4 part56 = true := by
  rw [InstructionTrace.ordered_eq_layout, part56_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part56_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x117e4 30 = part56Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
