import P256.Proofs.Signing.Interface
import P256.Proofs.Field.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

def AddContract : Prop :=
  ∀ [Bindings] {s : RamState} {boundary : ReturnBoundary} {a b : Nat},
    Field.BinaryFieldPre s boundary 0x113310 64 →
    Nat256At s (s.regValue .rsi) a → Nat256At s (s.regValue .rdx) b →
    a < Operations.domain.n → b < Operations.domain.n →
    ∃ t, CalleeResult s t boundary 32 64 ∧
      Nat256At t (s.regValue .rdi) ((a+b) % Operations.domain.n)

structure ConstructorPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop extends
    CalleePre s boundary 0x109890 32 72 512 where
  rightBounded : (registerRegion s .rdx 32).Bounded
  rightAllocated : (registerRegion s .rdx 32).Allocated s.external
  rightOutput : (registerRegion s .rdx 32).Disjoint (registerRegion s .rdi 72)
  rightStack : (registerRegion s .rdx 32).Disjoint (Stack.region s 512)

def ConstructorResult (t : RamState) (address : BitVec 64) (r scalarS : Nat) : Prop :=
  if r = 0 ∨ scalarS = 0 then
    memLoad t.external address 64 = 1 ∧ memLoad t.external (address+8) 64 = 0
  else memLoad t.external address 64 = 0 ∧
    Nat256At t (address+8) r ∧ Nat256At t (address+40) scalarS

def ConstructorContract : Prop :=
  ∀ [Bindings] {s : RamState} {boundary : ReturnBoundary} {r scalarS : Nat},
    ConstructorPre s boundary → Nat256At s (s.regValue .rsi) r →
    Nat256At s (s.regValue .rdx) scalarS →
    r < Operations.domain.n → scalarS < Operations.domain.n →
    ∃ t, CalleeResult s t boundary 72 512 ∧
      ConstructorResult t (s.regValue .rdi) r scalarS

end P256.Proofs.Signing.Core.Iteration.Components
