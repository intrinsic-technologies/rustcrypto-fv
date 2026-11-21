import P256.Proofs.Nonce.Fill.Tail.Decode.Shift.Prepare
import P256.Proofs.Nonce.Fill.Tail.Decode.Shift.Call
import P256.Proofs.Nonce.Fill.Tail.Decode.CallFrame
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem shift [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : ReadDone initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Decoded initial t orderAddress state := by
  obtain ⟨prepared, setupRun, stage⟩ := Shift.prepare pre input
  obtain ⟨called, callRun, effect, cp, count, integer⟩ := Shift.call pre stage
  obtain ⟨t, result, value⟩ := Initialize.Conversions.shift_zero_correct cp count integer
  have output : called.regValue .rdi = frameBase initial + 8 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans stage.destination
  have context := context_after_call pre stage.toContext effect (offset := 8)
    (by decide) (by decide +kernel) output result
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨13 + 1 + fuel, t, (setupRun.trans callRun).trans run, context,
    result.rip.trans (callEffect_stack effect).1, ?_, ?_⟩
  · exact ((result.calleeSaved .r12 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 12) (by simp))).trans stage.r12
  · simpa only [output] using value

end P256.Proofs.Nonce.Fill.Tail.Decode
