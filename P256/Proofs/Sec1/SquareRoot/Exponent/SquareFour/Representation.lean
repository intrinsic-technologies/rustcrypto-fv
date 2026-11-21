import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Arithmetic
import P256.Proofs.Sec1.SquareRoot.Exponent.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open X86 X86.Machine X86.UserProcess X86Proofs

def ReverseWordsAt (s : RamState) (base : BitVec 64) (a : Vector (BitVec 64) 4) : Prop :=
  (Operand.mem (base + 0x68) : Operand 64).read s = a[0] ∧
  (Operand.mem (base + 0x60) : Operand 64).read s = a[1] ∧
  (Operand.mem (base + 0x58) : Operand 64).read s = a[2] ∧
  (Operand.mem (base + 0x50) : Operand 64).read s = a[3]

end P256.Proofs.Sec1.SquareRoot.SquareFour
