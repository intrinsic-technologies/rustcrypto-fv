import P256.Proofs.Sec1Serialize.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Input

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def compressionFlag (s t : RamState) : Prop :=
  (Operand.mem (stackPtr s - 300) : Operand 32).read t = 0

def canonicalLimb (value index : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (value / 2^(64*index))

structure Converted (t : RamState) (x y : Nat) : Prop where
  x0 : t.regValue .rbx = canonicalLimb x 0
  x1 : t.regValue .r15 = canonicalLimb x 1
  x2 : t.regValue .r12 = canonicalLimb x 2
  x3 : t.regValue .r13 = canonicalLimb x 3
  y0 : t.regValue .rsi = canonicalLimb y 0
  y1 : t.regValue .r11 = canonicalLimb y 1
  y2 : t.regValue .rax = canonicalLimb y 2
  y3 : t.regValue .rdx = canonicalLimb y 3

end P256.Proofs.Sec1Serialize
