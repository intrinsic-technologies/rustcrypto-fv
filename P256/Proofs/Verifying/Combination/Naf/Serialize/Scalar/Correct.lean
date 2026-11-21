import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Prepare
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Fill
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.RecodeCall
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Finish

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

theorem naf_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat} (pre : ScalarPre s boundary cursor point)
    (input : Nat256At s (point + 96) n) :
    ∃ t, ScalarResult s t boundary cursor point ∧ NafAt t (s.regValue .rdi) n := by
  obtain ⟨n0, t0, run0, state0, rip0, rbx0, scalar0⟩ := prepare_scalar pre input
  obtain ⟨n1, t1, run1, state1, rip1, rbx1, r14_1, scalar1, zeroes1⟩ :=
    fill_digits pre state0 rip0 scalar0
  obtain ⟨n2, t2, run2, state2, rip2, rbx2, length2, values2⟩ :=
    RecodeCall.run pre state1 rip1 r14_1 scalar1 zeroes1
  exact finish pre state2 ⟨n0+n1+n2, (run0.trans run1).trans run2⟩ rip2
    (rbx2.trans (rbx1.trans rbx0)) length2 values2

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

namespace P256.Proofs.Verifying.Combination.Naf.Serialize

theorem scalar_correct : ScalarCorrect := by
  intro bindings s boundary cursor point n pre input
  exact Scalar.naf_correct pre input

end P256.Proofs.Verifying.Combination.Naf.Serialize
