import P256.Proofs.Signing.Core.Initialize.Entry
import P256.Proofs.Signing.Core.Initialize.State
import P256.Proofs.Signing.Core.Initialize.EncodeCall

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat)
open SecretKeyFromBytes.Scalar (Nat256At)

variable [Bindings] {s : RamState} {boundary : ReturnBoundary} {secret : Nat}

theorem encode_secret (pre : SignPre s boundary) (input : Nat256At s (s.regValue .rsi) secret) :
    ∃ fuel u, Advances boundary fuel s u ∧ Encoded s u secret ∧ u.RIP = 0x10ca39 := by
  obtain ⟨t, run, frame, rip, agrees⟩ := prologue pre
  obtain ⟨setupFuel, v, setupRun, setupFrame, setup⟩ := setup_frame pre frame rip
  have writes := setup.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at writes
  rcases writes with ⟨rbx, r14, r12, r13, output, _, _, _, _, _, rbp, rdi, scalarPtr⟩
  have source : v.regValue .rsi = s.regValue .rsi :=
    (setup.agrees.read (n := 64) (r := 6) (by simp [setupEffect, Effect.components])).trans
      (agrees.read (n := 64) (r := 6) (by simp [saveFrame]))
  have destination : v.regValue .rdi = frameBase s + 528 := by
    change v.regValue .rdi = stackPtr t + 528 at rdi
    exact rdi.trans (congrArg (· + 528) frame.rsp)
  have output' : (Operand.mem (frameBase s + 72) : Operand 64).read v = s.regValue .rdi := by
    have h : (Operand.mem (stackPtr t + 72) : Operand 64).read v = t.regValue .rdi := output
    rw [frame.rsp] at h
    exact h.trans (agrees.read (n := 64) (r := 7)
      (by simp [saveFrame]))
  have scalarPtr' : (Operand.mem (frameBase s + 80) : Operand 64).read v = s.regValue .rsi := by
    have h : (Operand.mem (stackPtr t + 80) : Operand 64).read v = t.regValue .rsi := scalarPtr
    rw [frame.rsp] at h
    exact h.trans (agrees.read (n := 64) (r := 6)
      (by simp [saveFrame]))
  have order := setup_order pre frame setupFrame setup
  obtain ⟨entry, called, ready, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre (by decide) (by decide) (scalarFrame setupFrame) 0xca34 0x6467
    (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x12ea0 (by decide)) setup.rip
  change (callEffect (fun _ => 0x112ea0) 0x10ca39 v).Holds v entry at effect
  have callPre := encode_pre pre setupFrame ready effect source destination
  have entrySource : entry.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have entryDestination : entry.regValue .rdi = frameBase s + 528 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have scalar : Nat256At entry (entry.regValue .rsi) secret := by
    rw [entrySource]
    exact scalar_of_frame pre
      ((scalarFrame setupFrame).after_call pre.toCalleePre (by decide) (by decide) ready effect).frame input
  obtain ⟨u, result, bytes, _, _⟩ := Projective.Multiply.Machine.Radix.Serialize.scalar_encode_correct callPre scalar
  obtain ⟨calleeFuel, calleeRun⟩ := result.execution
  rw [entryDestination] at bytes
  refine ⟨7 + setupFuel + 1 + calleeFuel, u, ((run.trans setupRun).trans called).trans calleeRun,
    ⟨encode_frame pre setupFrame ready effect result destination,
      ?_, ?_, ?_, bytes, ?_, ?_, ?_, ?_, ?_⟩,
    result.rip.trans (callEffect_stack effect).1⟩
  · exact (encode_word pre setupFrame ready effect result destination (by decide) (.inl (by decide))).trans output'
  · exact (encode_word pre setupFrame ready effect result destination (by decide) (.inl (by decide))).trans scalarPtr'
  · refine ⟨order.1, fun i hi => ?_⟩
    apply Eq.trans _ (order.2 i hi)
    exact encode_byte pre setupFrame ready effect result destination (offset := 272) (len := 32) (by decide) (.inl (by decide)) hi
  · apply (encode_preserved effect result .rbp (by simp)).trans
    change v.regValue .rbp = stackPtr t + 528 at rbp
    exact rbp.trans (congrArg (· + 528) frame.rsp)
  · apply (encode_preserved effect result .r13 (by simp)).trans
    exact r13.trans (agrees.read (n := 64) (r := 2)
      (by simp [saveFrame]))
  · apply (encode_preserved effect result .r12 (by simp)).trans
    exact r12.trans ((agrees.read (n := 64) (r := 1)
      (by simp [saveFrame])).trans pre.digestLength)
  · apply (encode_preserved effect result .r14 (by simp)).trans
    exact r14.trans ((agrees.read (n := 64) (r := 8)
      (by simp [saveFrame])).trans pre.entropyPointer)
  · apply (encode_preserved effect result .rbx (by simp)).trans
    exact rbx.trans ((agrees.read (n := 64) (r := 9)
      (by simp [saveFrame])).trans pre.entropyLength)

end P256.Proofs.Signing.Core.Initialize
