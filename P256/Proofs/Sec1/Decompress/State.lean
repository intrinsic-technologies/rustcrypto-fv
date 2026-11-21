import P256.Proofs.Sec1.Decompress.Interface
import P256.Proofs.Sec1.SquareRoot.Interface
import P256.Proofs.Program.ScalarFrame.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def checkedX (x : Nat) : Nat := if x < P256.Spec.Operations.domain.p then x else 0

abbrev Frame [Bindings] (s t : RamState) := ScalarFrame.FrameState s t 80 2592 408

structure Persistent [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Frame s t where
  output : memLoad t.external (stackPtr s - 224) 64 = s.regValue .rdi
  parity : memLoad t.external (stackPtr s - 332) 32 = BitVec.ofNat 32 odd.toNat
  valid : t.regValue .rbp = BitVec.ofNat 64 (decide (x < P256.Spec.Operations.domain.p)).toNat
  xCoordinate : Field.MontgomeryAt t (stackPtr s - 288) (checkedX x)

structure InputState [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Persistent s t x odd where
  rip : t.RIP = 0x10fdcc
  r14 : t.regValue .r14 = 0xffffffff00000001
  r15 : t.regValue .r15 = stackPtr s - 288

structure RootState [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Persistent s t x odd where
  rip : t.RIP = 0x10fede
  r14 : t.regValue .r14 = 0xffffffff00000001
  r13 : t.regValue .r13 = stackPtr s - 328
  rootProof : (SquareRoot.SquareRootResultAt t (stackPtr s - 328)
    (P256.Spec.Points.curveRhs (checkedX x))) ∧ True

theorem RootState.root [Bindings] {s t : RamState} {x : Nat} {odd : Bool}
    (state : RootState s t x odd) :
    SquareRoot.SquareRootResultAt t (stackPtr s - 328)
      (P256.Spec.Points.curveRhs (checkedX x)) := state.rootProof.1

structure SelectedState [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Frame s t where
  rip : t.RIP = 0x11005f
  output : memLoad t.external (stackPtr s - 224) 64 = s.regValue .rdi
  valid : t.regValue .rbp = BitVec.ofNat 64 (decide (x < P256.Spec.Operations.domain.p)).toNat
  rootValid : (t.regValue .r15).setWidth 8 = BitVec.ofNat 8
    (P256.Spec.Operations.sqrtMod (P256.Spec.Points.curveRhs (checkedX x))).isSome.toNat
  coordinates : ∀ y, P256.Spec.Points.decompress x odd =
      some (.affine x y) →
    Field.MontgomeryAt t (stackPtr s - 288) x ∧
      Field.MontgomeryAt t (stackPtr s - 376) y

end P256.Proofs.Sec1.Decompress
