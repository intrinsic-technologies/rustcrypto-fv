import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Reverse
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.ScalarCopy
import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field

theorem prepare_scalar [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat} (pre : ScalarPre s boundary cursor point)
    (input : Nat256At s (point+96) n) :
    ∃ fuel t, Advances boundary fuel s t ∧ Memory s t cursor point ∧
      t.RIP = 0x10b30b ∧ t.regValue .rbx = s.regValue .rdi ∧
      Nat256At t (stackPtr s-48) n := by
  obtain ⟨n0, t0, run0, state0, rip0, rbx0, rcx0⟩ := entry pre
  obtain ⟨n1, t1, run1, state1, rip1, rbx1, bytes1⟩ :=
    encode_scalar pre state0 rip0 rcx0 input
  have pre2 : P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Pre t1 :=
    ⟨rip1, stack_writable pre state1.toFrameState (offset := 8) (len := 32) (by decide) (by decide),
      stack_code pre state1.toFrameState (offset := 8) (len := 32)
        (codeOffset := 0xb1cf) (codeLen := 264) (by decide) (by decide)⟩
  obtain ⟨n2, t2, run2, ready2, _, post2⟩ := P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.reverse_correct boundary pre.outerBoundary t1
    (readyToStep state1.machine state1.bindingsSupported)
    (programText_slice (programLoaded_codeIn state1.loaded) 0xb1cf P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.reverseBytes
      (by decide +kernel) (by decide +kernel)) pre2
  have state2 := state1.after_reverse pre ready2 post2
  have scalar2 : Nat256At t2 (stackPtr t2+8) n := by
    apply reversed_scalar input.1 post2
    have address : stackPtr t1+8 = stackPtr s-352 :=
      stack_address state1.rsp (offset := 8) (by decide)
    rw [address]
    exact bytes1
  obtain ⟨n3, t3, run3, state3, rip3, rbx3, scalar3⟩ :=
    copy_reversed_scalar pre state2 post2.rip scalar2
  refine ⟨n0+n1+n2+n3, t3, ((run0.trans run1).trans run2).trans run3,
    state3, rip3, ?_, scalar3⟩
  exact rbx3.trans ((post2.agrees.read (n := 64) (r := 3)
    (by simp [P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint])).trans (rbx1.trans rbx0))

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
