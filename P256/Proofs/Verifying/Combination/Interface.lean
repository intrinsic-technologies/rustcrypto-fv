import P256.Proofs.Projective.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess

abbrev Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  CalleePre s boundary 0x106500 256 96 8808

def InputAt (s : RamState) (address : BitVec 64) (p q : Projective) (u v : Nat) : Prop :=
  ProjectiveAt s address p ∧ Nat256At s (address + 96) u ∧
    ProjectiveAt s (address + 128) q ∧ Nat256At s (address + 224) v

def RepresentsSum (result p q : Projective) (u v : Nat) : Prop :=
  result.valid ∧ result.toAffine = Points.add (Points.mul u p.toAffine) (Points.mul v q.toAffine)

def Correct : Prop :=
  ∀ [Bindings] (s : RamState) (boundary : ReturnBoundary) (p q : Projective) (u v : Nat),
    Pre s boundary → InputAt s (s.regValue .rsi) p q u v → p.valid → q.valid →
      ∃ t result, CalleeResult s t boundary 96 8808 ∧
        ProjectiveAt t (s.regValue .rdi) result ∧ RepresentsSum result p q u v

end P256.Proofs.Verifying.Combination
