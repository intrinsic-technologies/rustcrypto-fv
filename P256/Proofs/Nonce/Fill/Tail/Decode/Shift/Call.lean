import P256.Proofs.Nonce.Fill.Tail.Decode.Shift.State
import P256.Proofs.Nonce.Fill.Call
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Shift

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

def layout : StackCallLayout 2096 32 32 128 :=
  ⟨240, 80, 224, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Prepared initial s orderAddress state) :
    ∃ t, Advances boundary 1 s t ∧
      (callEffect (fun _ => 0x109530) 0x10757a s).Holds s t ∧
      CalleePre t boundary 0x109530 32 32 128 ∧ t.regValue .rdx = 0 ∧
      Nat256At t (t.regValue .rsi) (Signing.Search.nextCandidate state).1 := by
  obtain ⟨t, run, ready, effect⟩ := ScalarFrame.call_step pre.toCalleePre
    (frameOffset := 232) (by decide) (by decide)
    (readyToStep input.machine input.bindingsSupported) input.loaded input.allocated input.rsp
    0x7575 0x1fb6 (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x9530 (by decide)) input.rip
  change (callEffect (fun _ => 0x109530) 0x10757a s).Holds s t at effect
  have source : t.regValue .rsi = stackPtr initial - 80 :=
    ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans input.source).trans
      (frameBase_add initial (offset := 152) (by decide))
  have destination : t.regValue .rdi = stackPtr initial - 224 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.destination).trans
      (frameBase_add initial (offset := 8) (by decide))
  have rsp : stackPtr t = stackPtr initial - 240 :=
    effect.writes.1.trans (call_address input.toFrame)
  have ret : (returnBoundary t).rip = 0x10757a := (callEffect_stack effect).1
  have cp := CalleePre.of_stack pre.toCalleePre layout
    (bindingsSupported_of_ready_agrees input.bindingsSupported ready effect.agrees)
    (supportedMachine_of_ready_agrees input.machine ready effect.agrees)
    (effect.agrees.directionFlagClear (by simp) input.directionFlag)
    (call_loaded pre input.toFrame effect)
    (fun a ha => effect.agrees.grow a (input.allocated a ha)) effect.rip rsp source destination
    (ret ▸ inProgram_of_textOffset 0x757a (by decide))
  refine ⟨t, run, effect, cp,
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans input.count,
    input.integer.1, ?_⟩
  intro i hi
  rw [source]
  refine (ScalarFrame.call_byte (frameOffset := 232) (by decide) input.rsp effect
    (offset := 80) (len := 32) (by decide) (by decide) hi).trans ?_
  have address : frameBase initial + 152 = stackPtr initial - 80 :=
    frameBase_add initial (offset := 152) (by decide)
  have value := input.integer.2 i hi
  rw [address] at value
  exact value

end P256.Proofs.Nonce.Fill.Tail.Decode.Shift
