import Sha2.Proofs.Common.SHA256.Compression.Execution

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.InstructionTrace

open X86 X86.Machine X86.UserProcess X86Proofs

def layout [Bindings] (instructions : List CheckedInstruction) : List (BitVec 64 × Nat) :=
  instructions.map fun instruction => (instruction.address, instruction.bytes.length)

def orderedLayout : BitVec 64 → List (BitVec 64 × Nat) → Bool
  | _, [] => true
  | address, (current, count) :: rest =>
    (current == address) && orderedLayout (address + BitVec.ofNat 64 count) rest

theorem ordered_eq_layout [Bindings] (instructions : List CheckedInstruction)
    (address : BitVec 64) : ordered address instructions = orderedLayout address (layout instructions) := by
  induction instructions generalizing address with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [ordered, layout, List.map_cons, orderedLayout]
    rw [show ordered (address + BitVec.ofNat 64 instruction.bytes.length) rest =
      orderedLayout (address + BitVec.ofNat 64 instruction.bytes.length) (layout rest) from ih _]
    rfl

theorem layout_append [Bindings] (first rest : List CheckedInstruction) :
    layout (first ++ rest) = layout first ++ layout rest :=
  List.map_append

end Sha2.Proofs.Common.SHA256.Compression.InstructionTrace

namespace Sha2.Proofs.Common.SHA256.Compression

theorem chunked_toListFrom_append (data : Prelude.Bytes.Chunked) (start first rest : Nat) :
    data.toListFrom start (first + rest) =
      data.toListFrom start first ++ data.toListFrom (start + first) rest := by
  simp only [Prelude.Bytes.Chunked.toListFrom, ← List.range'_append_1, List.map_append]

end Sha2.Proofs.Common.SHA256.Compression

namespace Sha2.Proofs.Common.SHA256.Compression.InstructionTrace

open X86 X86.Machine X86.UserProcess X86Proofs

theorem layout_append_eq [Bindings] {first rest : List CheckedInstruction}
    {firstLayout restLayout : List (BitVec 64 × Nat)}
    (hf : layout first = firstLayout) (hr : layout rest = restLayout) :
    layout (first ++ rest) = firstLayout ++ restLayout := by
  rw [layout_append, hf, hr]

theorem bytes_append_eq [Bindings] {first rest : List CheckedInstruction}
    {firstBytes restBytes : List UInt8}
    (hf : first.flatMap CheckedInstruction.bytes = firstBytes)
    (hr : rest.flatMap CheckedInstruction.bytes = restBytes) :
    (first ++ rest).flatMap CheckedInstruction.bytes = firstBytes ++ restBytes := by
  rw [List.flatMap_append, hf, hr]

end Sha2.Proofs.Common.SHA256.Compression.InstructionTrace
