import P256.Proofs.Nonce.Fill.Tail.Compare.Zero.Return

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem zero [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Decoded initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compared initial t orderAddress state ∧
      t.RIP = 0x1075e5 ∧ (t.regValue .rax).setWidth 8 =
        if (nextCandidate state).1 = 0 then 1 else 0 := by
  obtain ⟨setupFuel, t, setupRun, prepared⟩ := zero_prepare pre input
  obtain ⟨u, callRun, ready, effect⟩ := ScalarFrame.call_step pre.toCalleePre
    (frameOffset := 232) (by decide) (by decide)
    (readyToStep prepared.machine prepared.bindingsSupported)
    prepared.loaded prepared.allocated prepared.rsp 0x75e0 0x11c8b
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x19270 (by decide)) prepared.rip
  change (callEffect (fun _ => 0x119270) 0x1075e5 t).Holds t u at effect
  have di : u.regValue .rdi = frameBase initial + 72 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans prepared.rdi
  have dx : u.regValue .rdx = frameBase initial + 8 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans prepared.rdx
  have left : Nat256At u (u.regValue .rdi) (nextCandidate state).1 := by
    rw [di]
    exact zero_call_nat256 prepared.toFrame effect (off := 72) (by decide) prepared.integer
  have right : Nat256At u (u.regValue .rdx) 0 := by
    rw [dx]
    exact zero_call_nat256 prepared.toFrame effect (off := 8) (by decide) prepared.zero
  obtain ⟨v, result, value⟩ := Equal.equal_correct (zero_call_pre pre prepared ready effect)
  simp only [Equal.prefixEqual_nat256 left right, decide_eq_true_eq] at value
  obtain ⟨calleeFuel, calleeRun⟩ := result.execution
  exact ⟨setupFuel + 1 + calleeFuel, v, (setupRun.trans callRun).trans calleeRun,
    zero_return pre prepared effect result, result.rip.trans (callEffect_stack effect).1, value⟩

end P256.Proofs.Nonce.Fill.Tail.Compare
