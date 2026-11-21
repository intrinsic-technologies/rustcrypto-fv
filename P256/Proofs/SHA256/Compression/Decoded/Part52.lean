import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part52 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (add_r32_m32_effect_step 0x11815b 1 (.sib 4 none 0 (.d32 188)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part52Bytes : List UInt8 :=
  [0x3,0x8c,0x24,0xbc,0x0,0x0,0x0]

set_option maxRecDepth 4096 in
theorem part52_bytes [Bindings] : part52.flatMap CheckedInstruction.bytes = part52Bytes  := by
  rfl

def part52Layout : List (BitVec 64 × Nat) :=
  [(0x11815b, 7)]

theorem part52_layout [Bindings] : InstructionTrace.layout part52 = part52Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part52_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x1815b 7 = part52Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
