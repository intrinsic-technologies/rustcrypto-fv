import P256.Proofs.Field.Interface
import P256.Spec.Points

set_option autoImplicit false

namespace P256.Proofs

open P256.Spec.Operations (domain)
open Standards.SECG.ECC
open Prelude X86 X86.Machine

structure Projective where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq

def Projective.canonical (point : Projective) : Prop :=
  point.x < domain.p ∧ point.y < domain.p ∧ point.z < domain.p

def Projective.toAffine (point : Projective) : Curve.Point :=
  if point.z = 0 then .infinity else
    .affine (point.x * Curve.inverse domain.p point.z % domain.p)
      (point.y * Curve.inverse domain.p point.z % domain.p)

def Projective.valid (point : Projective) : Prop :=
  point.canonical ∧
    (point.x ≠ 0 ∨ point.y ≠ 0 ∨ point.z ≠ 0) ∧
    (point.y * point.y * point.z + 3 * point.x * point.z * point.z) % domain.p =
      (point.x * point.x * point.x + domain.b * point.z * point.z * point.z) % domain.p

def ProjectiveAt (s : RamState) (address : BitVec 64) (point : Projective) : Prop :=
  Field.MontgomeryAt s address point.x ∧ Field.MontgomeryAt s (address + 32) point.y ∧
    Field.MontgomeryAt s (address + 64) point.z

theorem ProjectiveAt.canonical {s : RamState} {address : BitVec 64} {point : Projective}
    (represented : ProjectiveAt s address point) : point.canonical :=
  ⟨represented.1.1, represented.2.1.1, represented.2.2.1⟩

end P256.Proofs
