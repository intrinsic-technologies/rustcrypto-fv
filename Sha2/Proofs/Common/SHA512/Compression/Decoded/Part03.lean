import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part02

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part03 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (add_r64_m64_effect_step 0x10df22 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf20d7) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10df29 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10df2c 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local)
  ]

def part03Bytes : List UInt8 :=
  [0x48,0x3,0xd,0xd7,0x20,0xf,0x0,0x48,0x1,0xc8,0x4c,0x1,0xd1]

def part03Layout : List (BitVec 64 × Nat) :=
  [(0x10df22, 7), (0x10df29, 3), (0x10df2c, 3)]

set_option maxRecDepth 4096 in
theorem part03_bytes [Bindings] : part03.flatMap CheckedInstruction.bytes = part03Bytes := by
  rfl

theorem part03_layout [Bindings] : InstructionTrace.layout part03 = part03Layout := by
  rfl

theorem part03_ordered [Bindings] : InstructionTrace.ordered 0x10df22 part03 = true := by
  rw [InstructionTrace.ordered_eq_layout, part03_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part03_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xdf22 13 = part03Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
