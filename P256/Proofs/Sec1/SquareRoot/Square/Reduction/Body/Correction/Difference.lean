import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Stages
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def inputLimbs (t : RamState) : Limbs :=
  ⟨t.regValue .rbx, t.regValue .rcx, t.regValue .r8, t.regValue .rax⟩

structure Difference [Bindings] (s t u : RamState) : Prop where
  frame : ScalarFrame.FrameState s u 32 112 112
  rip : u.RIP = 0x1136fc
  rdi : u.regValue .rdi = s.regValue .rdi
  low : u.regValue .rbx = t.regValue .rbx
  middleLow : u.regValue .rcx = t.regValue .rcx
  middleHigh : u.regValue .r8 = t.regValue .r8
  high : u.regValue .r12 = t.regValue .r12
  top : (u.regValue .rdx).toNat + (slot s u 24).toNat +
    2^64 * (slot s u 16).toNat =
      (t.regValue .rax).toNat + 2^64 * (t.regValue .r12).toNat
  rsi : u.regValue .rsi = (subRaw (inputLimbs t) modulus).1.l0
  r9 : u.regValue .r9 = (subRaw (inputLimbs t) modulus).1.l1
  r14 : u.regValue .r14 = (subRaw (inputLimbs t) modulus).1.l2
  r15 : u.regValue .r15 = (subRaw (inputLimbs t) modulus).1.l3
  rbp : u.regValue .rbp = -(subRaw (inputLimbs t) modulus).2

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction
