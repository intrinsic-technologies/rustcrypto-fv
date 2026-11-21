import Sha3.Proofs.Image
import Sha3.Proofs.Run

namespace Sha3.Proofs.Memset

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def scalarClobbers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 8, .flags, .rip]

structure PrefixPost (s t : RamState) (tail : Nat := 1) : Prop where
  rip : t.RIP = 0x106a54
  rax : (Operand.reg 0 : Operand 64).read t = 0
  rcx : (Operand.reg 1 : Operand 64).read t = 0
  rdx : (Operand.reg 2 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s
  rsi : (Operand.reg 6 : Operand 64).read t = 25
  r8 : (Operand.reg 8 : Operand 64).read t = BitVec.ofNat 64 tail
  agrees : AgreesExcept scalarClobbers s t

def instructionBytes : List (BitVec 64 × List UInt8) :=
  [
    (0x106a20, [0x49, 0x89, 0xd0]),
    (0x106a23, [0x48, 0x89, 0xfa]),
    (0x106a26, [0x40, 0x0f, 0xb6, 0xce]),
    (0x106a2a, [0x48, 0xb8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01]),
    (0x106a34, [0x48, 0x0f, 0xaf, 0xc1]),
    (0x106a38, [0x89, 0xd1]),
    (0x106a3a, [0xf7, 0xd9]),
    (0x106a3c, [0x83, 0xe1, 0x07]),
    (0x106a3f, [0x49, 0x39, 0xc8]),
    (0x106a42, [0x49, 0x0f, 0x42, 0xc8]),
    (0x106a46, [0x49, 0x29, 0xc8]),
    (0x106a49, [0x4c, 0x89, 0xc6]),
    (0x106a4c, [0x48, 0xc1, 0xee, 0x03]),
    (0x106a50, [0x41, 0x83, 0xe0, 0x07]),
    (0x106a54, [0xf3, 0xaa]),
    (0x106a56, [0x48, 0x89, 0xf1]),
    (0x106a59, [0xf3, 0x48, 0xab]),
    (0x106a5c, [0x4c, 0x89, 0xc1]),
    (0x106a5f, [0xf3, 0xaa]),
    (0x106a61, [0x48, 0x89, 0xd0]),
    (0x106a64, [0xc3])]

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

end Sha3.Proofs.Memset
