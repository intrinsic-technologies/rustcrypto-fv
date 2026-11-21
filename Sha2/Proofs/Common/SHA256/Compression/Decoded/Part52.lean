import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part52 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (add_r32_m32_effect_step 0x10dcab 1 (.sib 4 none 0 (.d32 188)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part52Bytes : List UInt8 :=
  [0x3,0x8c,0x24,0xbc,0x0,0x0,0x0]

set_option maxRecDepth 4096 in
theorem part52_bytes [Bindings] : part52.flatMap CheckedInstruction.bytes = part52Bytes  := by
  rfl

def part52Layout : List (BitVec 64 × Nat) :=
  [(0x10dcab, 7)]

theorem part52_layout [Bindings] : InstructionTrace.layout part52 = part52Layout := by
  rfl

theorem part52_ordered [Bindings] : InstructionTrace.ordered 0x10dcab part52 = true := by
  rw [InstructionTrace.ordered_eq_layout, part52_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part52_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xdcab 7 = part52Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
