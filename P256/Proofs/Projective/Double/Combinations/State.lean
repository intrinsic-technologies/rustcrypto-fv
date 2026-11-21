import P256.Proofs.Projective.Double.Combinations.Memory

set_option autoImplicit false


namespace P256.Proofs.Projective.Double.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def tripleZZ (point : Projective) : Nat :=
  (((values point).zz + (values point).zz) % P256.Spec.Operations.domain.p +
    (values point).zz) % P256.Spec.Operations.domain.p

def bXZ (point : Projective) : Nat :=
  P256.Spec.Operations.domain.b * (values point).xz2 % P256.Spec.Operations.domain.p

def bXZDifference (point : Projective) : Nat :=
  Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (bXZ point)
    ((tripleZZ point + (values point).xx) % P256.Spec.Operations.domain.p)

structure SavedProductsAt (s t : RamState) (point : Projective) : Prop where
  pointAt : ProjectiveAt t (s.regValue .rdi) point
  rbx : t.regValue .rbx = s.regValue .rdi
  r15 : t.regValue .r15 = stackSlot s 616
  xx : MontgomeryAt t (stackSlot s 104) (values point).xx
  yy : MontgomeryAt t (stackSlot s 136) (values point).yy
  xProduct : MontgomeryAt t (stackSlot s 520) (values point).xProduct
  yProduct : MontgomeryAt t (stackSlot s 616) (values point).yProduct
  r12 : t.regValue .r12 = stackSlot s 360
  zz3 : MontgomeryAt t (stackSlot s 360) (tripleZZ point)

structure BProductAt (s t : RamState) (point : Projective) : Prop extends SavedProductsAt s t point where
  r14 : t.regValue .r14 = stackSlot s 232
  bxz : MontgomeryAt t (stackSlot s 232) (bXZ point)

structure DifferenceAt (s t : RamState) (point : Projective) : Prop extends SavedProductsAt s t point where
  r13 : t.regValue .r13 = stackSlot s 392
  difference : MontgomeryAt t (stackSlot s 392) (bXZDifference point)

structure TripledAt (s t : RamState) (point : Projective) : Prop extends SavedProductsAt s t point where
  r14 : t.regValue .r14 = stackSlot s 424
  bxz6 : MontgomeryAt t (stackSlot s 424) (values point).bxz6

end P256.Proofs.Projective.Double.Combinations
