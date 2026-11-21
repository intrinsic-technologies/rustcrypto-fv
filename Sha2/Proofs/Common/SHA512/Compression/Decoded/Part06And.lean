import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.Instructions.MemoryAlu.AndLoad.Effect
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part06

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part06And [Bindings] : List CheckedInstruction :=
  [CheckedInstruction.load
    (and_r64_m64_effect_step 0x10dffc 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl)
    (by x86_local)
    (fun _ _ h => AddrMode.addr_obs h _ _)]

def part06AndBytes : List UInt8 :=
  [0x48,0x23,0xb4,0x24,0xb0,0x0,0x0,0x0]

def part06AndLayout : List (BitVec 64 × Nat) :=
  [(0x10dffc, 8)]

set_option maxRecDepth 4096 in
theorem part06And_bytes [Bindings] : part06And.flatMap CheckedInstruction.bytes = part06AndBytes := by
  simp [part06And, part06AndBytes, CheckedInstruction.load, CheckedInstruction.ofStep,
    AddrMode.modrm, AddrMode.mod, AddrMode.rm, AddrMode.tail, AddrMode.sibByte, idxLow,
    regLow, Disp.bytes, Disp.mod, immBytes] <;> decide +kernel

theorem part06And_layout [Bindings] : InstructionTrace.layout part06And = part06AndLayout := by
  simp [part06And, part06AndLayout, CheckedInstruction.load, CheckedInstruction.ofStep,
    InstructionTrace.layout, AddrMode.tail, Disp.bytes, immBytes] <;> decide +kernel

theorem part06And_ordered [Bindings] : InstructionTrace.ordered 0x10dffc part06And = true := by
  rw [InstructionTrace.ordered_eq_layout, part06And_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part06And_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xdffc 8 = part06AndBytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
