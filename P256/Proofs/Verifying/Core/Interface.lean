import P256.Proofs.Verifying.Model
import P256.Proofs.Program.ScalarFrame.State

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core

open P256.Spec P256.Spec.Program.Routines Program
open SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop extends
    CalleePre s boundary 0x10d570 72 24 9992 where
  signatureBounded : (registerRegion s .r8 64).Bounded
  signatureAllocated : (registerRegion s .r8 64).Allocated s.external
  signatureStack : (registerRegion s .r8 64).Disjoint (Stack.region s 9992)

def frameBase (s : RamState) : BitVec 64 := stackPtr s - 1176

abbrev Frame [Bindings] (s t : RamState) := ScalarFrame.FrameState s t 24 9992 1176

structure InputAt (s t : RamState) (point : Projective) (digest : ByteArray)
    (r scalarS : Nat) : Prop where
  point : ProjectiveAt t (frameBase s + 1000) point
  digest : (⟨(frameBase s + 424).toNat, 32⟩ : MemoryRegion).HasBytes t.external digest
  signature : memLoad t.external (frameBase s + 464) 64 = s.regValue .r8
  output : memLoad t.external (frameBase s + 384) 64 = s.regValue .rdi
  r : Nat256At t (s.regValue .r8) r
  scalarS : Nat256At t (s.regValue .r8 + 32) scalarS

structure ResultAt (s : RamState) (output : BitVec 64) (accepted : Bool) : Prop where
  tag : memLoad s.external output 64 = if accepted then 0 else 1
  error : accepted = false → memLoad s.external (output + 8) 64 = 0

def Correct : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {digest : ByteArray} {r scalarS : Nat},
    Pre s boundary → Frame s t → t.RIP = 0x10da4d →
    InputAt s t point digest r scalarS → point.valid →
    0 < r → r < Operations.domain.n → 0 < scalarS → scalarS < Operations.domain.n →
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10e194 ∧
      ResultAt u (s.regValue .rdi) (Ecdsa.verifies point.toAffine digest (r, scalarS))

def FinalCorrect : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point result : Projective} {digest : ByteArray} {r scalarS : Nat},
    Pre s boundary → Frame s t → t.RIP = 0x10de41 →
    ProjectiveAt t (frameBase s) result → Nat256At t (frameBase s + 704) r →
    memLoad t.external (frameBase s + 384) 64 = s.regValue .rdi →
    result.toAffine = Verifying.verificationPoint point.toAffine digest r scalarS →
    0 < r → r < Operations.domain.n → 0 < scalarS → scalarS < Operations.domain.n →
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10e194 ∧
      ResultAt u (s.regValue .rdi) (Ecdsa.verifies point.toAffine digest (r, scalarS))

end P256.Proofs.Verifying.Core
