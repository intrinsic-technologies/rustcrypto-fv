import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Field.Interface

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Field (BinaryFieldPre)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev FrameState [Bindings] (s t : RamState) :=
  P256.Proofs.Program.ScalarFrame.FrameState s t 32 64 64

def sumLimbs (t : RamState) : Limbs :=
  ⟨t.regValue .r11, t.regValue .r10, t.regValue .r9, t.regValue .r8⟩

def differenceLimbs (t : RamState) : Limbs :=
  ⟨t.regValue .rdx, t.regValue .rsi, t.regValue .r14, t.regValue .r15⟩

structure SumState [Bindings] (s t : RamState) (a b : Nat) : Prop extends FrameState s t where
  rip : t.RIP = 0x113974
  output : t.regValue .rdi = s.regValue .rdi
  modulus : t.regValue .rcx = 0x2025e0
  sum : (sumLimbs t).toNat + 2^256 * (t.regValue .r12).toNat = a + b

structure DifferenceState [Bindings] (s t : RamState) (a b : Nat) : Prop extends FrameState s t where
  rip : t.RIP = 0x113a42
  output : t.regValue .rdi = s.regValue .rdi
  sum : (sumLimbs t).toNat + 2^256 * (t.regValue .r12).toNat = a + b
  difference : ∃ borrow : BitVec 64, borrow.toNat ≤ 1 ∧ t.regValue .r13 = -borrow ∧
    (differenceLimbs t).toNat + P256.Spec.Operations.domain.n =
      (sumLimbs t).toNat + 2^256 * borrow.toNat

end P256.Proofs.Signing.Core.Iteration.Components.Addition
