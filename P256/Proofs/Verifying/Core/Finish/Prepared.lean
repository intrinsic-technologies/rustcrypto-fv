import P256.Proofs.Verifying.Core.Finish.Memory
import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame



theorem buffer_add (s : RamState) (a : BitVec 64) (b i : Nat) :
    (frameBase s + a) + BitVec.ofNat 64 (b+i) =
      (frameBase s + (a + BitVec.ofNat 64 b)) + BitVec.ofNat 64 i := by
  simp only [BitVec.ofNat_add,BitVec.add_assoc]

structure Coordinates [Bindings] (s t : RamState) (x y r : Nat) (nonzero : Bool) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10df44
  output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi
  x : Field.MontgomeryAt t (frameBase s + 576) x
  y : Field.MontgomeryAt t (frameBase s + 392) y
  choice : (t.regValue .rbx).setWidth 8 = if nonzero then 1 else 0
  r15 : t.regValue .r15 = frameBase s + 576
  scalar : SecretKeyFromBytes.Scalar.Nat256At t (frameBase s + 704) r

structure Prepared [Bindings] (s t : RamState) (x y r : Nat) (nonzero : Bool) : Prop extends FrameState s t 24 9992 1176 where
  rip : t.RIP = 0x10dfc3
  output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi
  x : Field.MontgomeryAt t (frameBase s + 128)
    x
  y : Field.MontgomeryAt t (frameBase s + 160)
    y
  zeroX : Field.MontgomeryAt t (frameBase s + 576) 0
  zeroY : Field.MontgomeryAt t (frameBase s + 608) 0
  tag : t.external[frameBase s + 192]? = some 0
  choice : (t.regValue .rbx).setWidth 8 = if nonzero then 1 else 0
  rax : t.regValue .rax = frameBase s + 576
  scalar : SecretKeyFromBytes.Scalar.Nat256At t (frameBase s + 704) r
  rdx : t.regValue .rdx = frameBase s + 128

end P256.Proofs.Verifying.Core.Finish
