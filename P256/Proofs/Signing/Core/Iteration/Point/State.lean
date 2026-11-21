import P256.Proofs.Signing.Core.Iteration.Point.Interface
import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

theorem Preserved.trans {s t u v : RamState}
    (first : Preserved s t u) (second : Preserved s u v) : Preserved s t v := by
  intro offset live
  exact (second offset live).trans (first offset live)

structure Converted [Bindings] (s t : RamState) (x y : Nat) : Prop where
  frame : Frame s t
  point : Sec1.AffineAt t (frameBase s + 104) (.affine x y)
  value : Nat256At t (frameBase s + 528) x
  rbp : t.regValue .rbp = frameBase s + 528
  r13 : t.regValue .r13 = frameBase s + 432
  r15 : t.regValue .r15 = frameBase s + 1328

end P256.Proofs.Signing.Core.Iteration.Point
