import Sha3.Proofs.Image
import Sha3.Proofs.Run

namespace Sha3.Proofs.Memcpy

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def scalarClobbers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 8, .flags, .rip]

structure PrefixPost (s t : RamState) (length : BitVec 64 := 208)
    (lead : BitVec 64 := 0) : Prop where
  rip : t.RIP = 0x106a87
  rax : (Operand.reg 0 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s
  rcx : (Operand.reg 1 : Operand 64).read t = lead
  r8 : (Operand.reg 8 : Operand 64).read t = lead
  rdx : (Operand.reg 2 : Operand 64).read t = length
  agrees : AgreesExcept scalarClobbers s t

def instructionBytes : List (BitVec 64 × List UInt8) :=
  [(0x106a70, [0x48, 0x89, 0xf8]),
   (0x106a73, [0x41, 0x89, 0xc0]),
   (0x106a76, [0x41, 0xf7, 0xd8]),
   (0x106a79, [0x41, 0x83, 0xe0, 0x07]),
   (0x106a7d, [0x4c, 0x39, 0xc2]),
   (0x106a80, [0x4c, 0x0f, 0x42, 0xc2]),
   (0x106a84, [0x4c, 0x89, 0xc1]),
   (0x106a87, [0xf3, 0xa4]),
   (0x106a89, [0x4c, 0x29, 0xc2]),
   (0x106a8c, [0x48, 0x89, 0xd1]),
   (0x106a8f, [0x48, 0xc1, 0xe9, 0x03]),
   (0x106a93, [0xf3, 0x48, 0xa5]),
   (0x106a96, [0x83, 0xe2, 0x07]),
   (0x106a99, [0x48, 0x89, 0xd1]),
   (0x106a9c, [0xf3, 0xa4]),
   (0x106a9e, [0xc3])]

theorem instruction_image : ∀ instruction ∈ instructionBytes,
    let offset := instruction.1.toNat - Extracted.textAddress.toNat
    instruction.1 = Extracted.textAddress + BitVec.ofNat 64 offset ∧
      offset + instruction.2.length ≤ Extracted.textBytes.size ∧
      Extracted.textBytes.toListFrom offset instruction.2.length = instruction.2 := by
  decide +kernel

theorem instruction_subset {p : BitVec 64} {bytes : List UInt8}
    (hmem : (p, bytes) ∈ instructionBytes) :
    ∀ x ∈ codeRange p bytes, x ∈ Extracted.programImage := by
  obtain ⟨hp, hbound, hslice⟩ := instruction_image (p, bytes) hmem
  dsimp only at hp hbound hslice
  rw [hp]
  exact textSlice_subset_programImage hbound hslice

theorem instruction_codeIn {s : RamState} (hcode : CodeIn Extracted.programImage s)
    {p : BitVec 64} {bytes : List UInt8} (hmem : (p, bytes) ∈ instructionBytes) :
    CodeIn (codeRange p bytes) s :=
  hcode.mono (instruction_subset hmem)

end Sha3.Proofs.Memcpy
