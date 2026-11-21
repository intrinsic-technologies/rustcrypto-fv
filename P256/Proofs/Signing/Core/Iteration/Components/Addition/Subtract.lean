import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Parameters
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Low
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Second
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Third
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.High

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Field (BinaryFieldPre)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction (borrow subWord subRaw subRaw_toNat)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Subtract

theorem subtract_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a b : Nat}
    (pre : BinaryFieldPre s boundary 0x113310 64) (state : SumState s t a b) :
    ∃ fuel u, Advances boundary fuel t u ∧ DifferenceState s u a b := by
  obtain ⟨n1,t1,run1,state1,rip1,f1,e1⟩ := block_run (offset := 0x13974)
    pre.toCalleePre state.toFrameState state.modulus state.rip
    (low_correct boundary pre.outerBoundary) (by decide +kernel) (by decide +kernel) rfl
    (by simp [lowEffect, Effect.components, blockFrame])
  have rcx1 : t1.regValue .rcx = 0x2025e0 :=
    (e1.agrees.read (n := 64) (r := 1) (by simp [lowEffect, Effect.components])).trans state.modulus
  obtain ⟨n2,t2,run2,state2,rip2,f2,e2⟩ := block_run (offset := 0x139a3)
    pre.toCalleePre state1 rcx1 rip1
    (second_correct boundary pre.outerBoundary) (by decide +kernel) (by decide +kernel) rfl
    (by simp [secondEffect, Effect.components, blockFrame])
  have rcx2 : t2.regValue .rcx = 0x2025e0 :=
    (e2.agrees.read (n := 64) (r := 1) (by simp [secondEffect, Effect.components])).trans rcx1
  obtain ⟨n3,t3,run3,state3,rip3,f3,e3⟩ := block_run (offset := 0x139d8)
    pre.toCalleePre state2 rcx2 rip2
    (third_correct boundary pre.outerBoundary) (by decide +kernel) (by decide +kernel) rfl
    (by simp [thirdEffect, Effect.components, blockFrame])
  have rcx3 : t3.regValue .rcx = 0x2025e0 :=
    (e3.agrees.read (n := 64) (r := 1) (by simp [thirdEffect, Effect.components])).trans rcx2
  obtain ⟨n4,t4,run4,state4,rip4,f4,e4⟩ := block_run (offset := 0x13a0d)
    pre.toCalleePre state3 rcx3 rip3
    (high_correct boundary pre.outerBoundary) (by decide +kernel) (by decide +kernel) rfl
    (by simp [highEffect, Effect.components, blockFrame])
  have m0 := modulus_limbs state.loaded state.modulus
  have m1 := modulus_limbs state1.loaded rcx1
  have m2 := modulus_limbs state2.loaded rcx2
  have m3 := modulus_limbs state3.loaded rcx3
  have x1 := sumLimbs_eq_of_agrees f1
  have x2 := (sumLimbs_eq_of_agrees f2).trans x1
  have x3 := (sumLimbs_eq_of_agrees f3).trans x2
  have x4 := (sumLimbs_eq_of_agrees f4).trans x3
  let x := sumLimbs t
  let p := scalarModulus
  let r0 := x.l0 - p.l0
  let b0 := borrow x.l0 p.l0 r0
  let r1 := subWord x.l1 p.l1 b0
  let b1 := borrow x.l1 p.l1 r1
  let r2 := subWord x.l2 p.l2 b1
  let b2 := borrow x.l2 p.l2 r2
  let r3 := subWord x.l3 p.l3 b2
  let b3 := borrow x.l3 p.l3 r3
  have d0 := e1.writes.2.1
  change t1.regValue .rdx = x.l0 - (P256.Proofs.Field.readLimbs t (t.regValue .rcx)).l0 at d0
  rw [m0] at d0
  have c1 := e1.writes.2.2.1
  change t1.regValue .rsi = -borrow x.l0 (P256.Proofs.Field.readLimbs t (t.regValue .rcx)).l0
    (x.l0 - (P256.Proofs.Field.readLimbs t (t.regValue .rcx)).l0) at c1
  rw [m0] at c1
  change t1.regValue .rsi = -b0 at c1
  have d1 := e2.writes.2.2.1
  change t2.regValue .rsi = (t1.regValue .rsi).sshiftRight 63 +
    ((sumLimbs t1).l1 - (P256.Proofs.Field.readLimbs t1 (t1.regValue .rcx)).l1) at d1
  rw [x1, m1, c1] at d1
  change t2.regValue .rsi = r1 at d1
  have c2 := e2.writes.1
  change t2.regValue .r14 = -borrow (sumLimbs t1).l1 (P256.Proofs.Field.readLimbs t1 (t1.regValue .rcx)).l1
    ((t1.regValue .rsi).sshiftRight 63 +
      ((sumLimbs t1).l1 - (P256.Proofs.Field.readLimbs t1 (t1.regValue .rcx)).l1)) at c2
  rw [x1, m1, c1] at c2
  change t2.regValue .r14 = -b1 at c2
  have d2 := e3.writes.2.1
  change t3.regValue .r14 = (t2.regValue .r14).sshiftRight 63 +
    ((sumLimbs t2).l2 - (P256.Proofs.Field.readLimbs t2 (t2.regValue .rcx)).l2) at d2
  rw [x2, m2, c2] at d2
  change t3.regValue .r14 = r2 at d2
  have c3 := e3.writes.2.2.2.1
  change t3.regValue .r15 = -borrow (sumLimbs t2).l2 (P256.Proofs.Field.readLimbs t2 (t2.regValue .rcx)).l2
    ((t2.regValue .r14).sshiftRight 63 +
      ((sumLimbs t2).l2 - (P256.Proofs.Field.readLimbs t2 (t2.regValue .rcx)).l2)) at c3
  rw [x2, m2, c2] at c3
  change t3.regValue .r15 = -b2 at c3
  have d3 := e4.writes.2.1
  change t4.regValue .r15 = (t3.regValue .r15).sshiftRight 63 +
    ((sumLimbs t3).l3 - (P256.Proofs.Field.readLimbs t3 (t3.regValue .rcx)).l3) at d3
  rw [x3, m3, c3] at d3
  change t4.regValue .r15 = r3 at d3
  have c4 := e4.writes.2.2.2.1
  change t4.regValue .r13 = -borrow (sumLimbs t3).l3 (P256.Proofs.Field.readLimbs t3 (t3.regValue .rcx)).l3
    ((t3.regValue .r15).sshiftRight 63 +
      ((sumLimbs t3).l3 - (P256.Proofs.Field.readLimbs t3 (t3.regValue .rcx)).l3)) at c4
  rw [x3, m3, c3] at c4
  change t4.regValue .r13 = -b3 at c4
  have difference : differenceLimbs t4 = (subRaw x p).1 := by
    unfold differenceLimbs
    change Limbs.mk _ _ _ _ = Limbs.mk r0 r1 r2 r3
    congr 1
    · exact (e4.agrees.read (n := 64) (r := 2) (by simp [highEffect, Effect.components])).trans
        ((e3.agrees.read (n := 64) (r := 2) (by simp [thirdEffect, Effect.components])).trans
          ((e2.agrees.read (n := 64) (r := 2) (by simp [secondEffect, Effect.components])).trans d0))
    · exact (e4.agrees.read (n := 64) (r := 6) (by simp [highEffect, Effect.components])).trans
        ((e3.agrees.read (n := 64) (r := 6) (by simp [thirdEffect, Effect.components])).trans d1)
    · exact (e4.agrees.read (n := 64) (r := 14) (by simp [highEffect, Effect.components])).trans d2
  have arithmetic := subRaw_toNat x p
  have hp : p.toNat = P256.Spec.Operations.domain.n := scalar_modulus
  rw [hp] at arithmetic
  refine ⟨n1+n2+n3+n4,t4,((run1.trans run2).trans run3).trans run4,
    { toFrameState := state4
      rip := rip4
      output := ?_
      sum := ?_
      difference := ⟨b3, arithmetic.1, c4, ?_⟩ }⟩
  · exact (f4.read (n := 64) (r := 7) (by simp [blockFrame])).trans
      ((f3.read (n := 64) (r := 7) (by simp [blockFrame])).trans
        ((f2.read (n := 64) (r := 7) (by simp [blockFrame])).trans
          ((f1.read (n := 64) (r := 7) (by simp [blockFrame])).trans state.output)))
  · have carry : t4.regValue .r12 = t.regValue .r12 :=
      (f4.read (n := 64) (r := 12) (by simp [blockFrame])).trans
        ((f3.read (n := 64) (r := 12) (by simp [blockFrame])).trans
          ((f2.read (n := 64) (r := 12) (by simp [blockFrame])).trans
            (f1.read (n := 64) (r := 12) (by simp [blockFrame]))))
    rw [x4, carry]
    exact state.sum
  · rw [difference, x4]
    exact arithmetic.2

end P256.Proofs.Signing.Core.Iteration.Components.Addition
