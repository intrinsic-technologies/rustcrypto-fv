import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.SerializeCall
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.ScalarCall
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.CheckedScalar
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.Copies
import P256.Proofs.SignatureFromDer.Fixed.Decode.CopyFrame

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program.ScalarFrame

theorem decode [Bindings] {s : RamState} {boundary : ReturnBoundary} {a b : Nat}
    (pre : ConstructorPre s boundary)
    (left : Nat256At s (s.regValue .rsi) a) (right : Nat256At s (s.regValue .rdx) b)
    (leftCanonical : a < Operations.domain.n)
    (rightCanonical : b < Operations.domain.n) :
    ∃ t, Decoded s t boundary a b := by
  obtain ⟨s1, st1, ip1, r14, r15, bytes1⟩ := Decode.serialize_left pre left
  obtain ⟨s2, st2, ip2, scalar2, r14_2, _⟩ :=
    Decode.call_scalar pre.toCalleePre st1 false ip1 r15 bytes1
  simp only [Bool.false_eq_true, ite_false] at ip2
  obtain ⟨s3, st3, ip3, scalar3, frame3⟩ :=
    Decode.scalar_status pre.toCalleePre st2 false ip2 leftCanonical scalar2
  simp only [Bool.false_eq_true, ite_false] at ip3
  obtain ⟨s4, st4, ip4, first4, frame4⟩ :=
    Decode.save_scalar pre.toCalleePre st3 false ip3 scalar3
  simp only [Bool.false_eq_true, ite_false] at ip4 first4 frame4
  have source4 : s4.regValue .r14 = s.regValue .rdx :=
    (frame4.read (n := 64) (r := 14) (by simp [P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components])).trans
      ((frame3.read (n := 64) (r := 14) (by simp)).trans (r14_2.trans r14))
  obtain ⟨s5, st5, ip5, second5, frame5⟩ := Decode.copy_right pre st4 ip4 source4 right
  have sp5 : stackPtr s5 = stackPtr s4 := frame5.read (n := 64) (r := 4) (by simp [Copy32.components])
  have first5 : Nat256At s5 (stackPtr s5 + 64#64) a := by
    rw [sp5]
    exact P256.Proofs.SignatureFromDer.Fixed.Decode.copy_preserves_nat256 frame5
      (RangeApart.offsets (stackPtr s4) (a := 128) (b := 64)
        (by decide) (by decide) (.inr (by decide))) first4
  obtain ⟨s6, st6, ip6, source6, bytes6, first6⟩ :=
    Decode.serialize_right pre.toCalleePre st5 ip5 first5 second5
  obtain ⟨s7, st7, ip7, scalar7, _, preserved7⟩ :=
    Decode.call_scalar pre.toCalleePre st6 true ip6 source6 bytes6
  simp only [ite_true] at ip7
  have first7 : Nat256At s7 (stackPtr s7 + 64#64) a :=
    ⟨first6.1, fun i hi => (preserved7 64 32 i (by decide) (by decide) hi).trans (first6.2 i hi)⟩
  obtain ⟨s8, st8, ip8, second8, frame8⟩ :=
    Decode.scalar_status pre.toCalleePre st7 true ip7 rightCanonical scalar7
  simp only [ite_true] at ip8
  have memory8 := frame8.external (by simp [Component.Covers])
  have sp8 : stackPtr s8 = stackPtr s7 := frame8.read (n := 64) (r := 4) (by simp)
  have first8 : Nat256At s8 (stackPtr s8 + 64#64) a := by
    simpa only [Nat256At, memory8, sp8] using first7
  obtain ⟨t, state, rip, secondT, frameT⟩ :=
    Decode.save_scalar pre.toCalleePre st8 true ip8 second8
  simp only [ite_true] at rip secondT frameT
  have spT : stackPtr t = stackPtr s8 := frameT.read (n := 64) (r := 4) (by simp [P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components])
  have firstT : Nat256At t (stackPtr t + 64#64) a := by
    rw [spT]
    refine ⟨first8.1, fun i hi => (frameT.byte ?_).trans (first8.2 i hi)⟩
    intro c hc ha
    simp only [P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨j, hj, he⟩ := ha
    exact RangeApart.offsets (stackPtr s8) (a := 96) (b := 64)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm

  exact ⟨t, state, rip, firstT, secondT⟩

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
