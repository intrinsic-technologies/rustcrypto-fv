import P256.Proofs.Nonce.Fill.Tail.Decode.Shift.State
import P256.Proofs.Nonce.Fill.Tail.Decode.Guard
import P256.Proofs.Nonce.Fill.Tail.Decode.Copy
import P256.Proofs.Nonce.Fill.Tail.Decode.Arguments

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Shift

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : ReadDone initial s orderAddress state) :
    ∃ t, Advances boundary 13 s t ∧ Prepared initial t orderAddress state := by
  obtain ⟨a, guardRun, ar, arip, ag⟩ := guard
    (readyToStep input.machine input.bindingsSupported) input.loaded input.rip input.status pre.outerBoundary
  have af := input.toContext.after_registers ar ag (by simp [Component.Covers])
    (by simp) (by simp) (by simp)
  have am := ag.external (by simp [Component.Covers])
  have ai : Nat256At a (frameBase initial + 104) (Signing.Search.nextCandidate state).1 := by
    simpa only [Nat256At, am] using input.integer
  have a12 : a.regValue .r12 = frameBase initial + 8 :=
    (ag.read (n := 64) (r := 12) (by simp)).trans input.r12
  have a14 : a.regValue .r14 = 0 :=
    (ag.read (n := 64) (r := 14) (by simp)).trans input.r14
  obtain ⟨b, copyRun, bf, brip, bg, words⟩ := Copy.correct pre af arip
  have bi : Nat256At b (frameBase initial + 152) (Signing.Search.nextCandidate state).1 := by
    apply nat256At_of_memLoad_limbs ai.1
    · intro i hi
      have address : frameBase initial + 152 = stackPtr initial - 80 :=
        frameBase_add initial (offset := 152) (by decide)
      rw [address]
      exact bf.allocated _ ((stack_sub_readable pre.stack (offset := 80) (len := 32)
        (by decide) (by decide)).mem i hi)
    · intro j hj
      have h := words j hj
      rw [bf.rsp, af.rsp] at h
      exact h.trans (ai.memLoad_limb j hj)
  have b12 : b.regValue .r12 = frameBase initial + 8 :=
    (bg.read (n := 64) (r := 12) (by simp [Copy.components])).trans a12
  have b14 : b.regValue .r14 = 0 :=
    (bg.read (n := 64) (r := 14) (by simp [Copy.components])).trans a14
  obtain ⟨t, argRun, tr, trip, dst, src, count, tg⟩ := arguments
    (readyToStep bf.machine bf.bindingsSupported) bf.loaded brip b14
    (by simpa only [bf.rsp] using b12) pre.outerBoundary
  have tf := bf.after_registers tr tg (by simp [Component.Covers])
    (by simp) (by simp) (by simp)
  have tm := tg.external (by simp [Component.Covers])
  refine ⟨t, (guardRun.trans copyRun).trans argRun, tf, trip,
    (tg.read (n := 64) (r := 12) (by simp)).trans b12,
    count, ?_, ?_, ?_⟩
  · simpa only [bf.rsp] using src
  · simpa only [bf.rsp] using dst
  · simpa only [Nat256At, tm] using bi

end P256.Proofs.Nonce.Fill.Tail.Decode.Shift
