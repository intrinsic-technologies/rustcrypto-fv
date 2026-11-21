import P256.Proofs.Nonce.Initialize.Read.Prepare
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Shift

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

def layout : StackCallLayout 2144 32 32 128 :=
  ⟨288, 208, 272, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (state : Read.ShiftReady initial s boundary digest) (rip : s.RIP = 0x107999) :
    ∃ t, Stage initial t boundary 288 ∧ CalleePre t boundary 0x109530 32 32 128 ∧
      t.regValue .rdx = 0 ∧ Nat256At t (t.regValue .rsi) (Arith.uint digest) ∧
      (callEffect (fun _ => 0x109530) 0x10799e s).Holds s t := by
  obtain ⟨t, run, ready, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) state.stage.toFrameState 0x7999 0x1b92
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x9530 (by decide)) rip
  change (callEffect (fun _ => 0x109530) 0x10799e s).Holds s t at effect
  have frame : Stage initial t boundary 288 := by
    obtain ⟨fuel, execution⟩ := state.stage.execution
    exact ⟨state.stage.toFrameState.after_call pre.toCalleePre (by decide) (by decide)
      ready effect, fuel + 1, execution.trans run⟩
  have input : t.regValue .rsi = stackPtr initial - 208 := by
    have h := (effect.agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])).trans state.source
    change t.regValue .rsi = stackPtr s + 72 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have output : t.regValue .rdi = stackPtr initial - 272 := by
    have h := (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans state.destination
    change t.regValue .rdi = stackPtr s + 8 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have ret : (returnBoundary t).rip = 0x10799e := (callEffect_stack effect).1
  refine ⟨t, frame, CalleePre.of_stack pre.toCalleePre layout frame.bindingsSupported
    frame.machine frame.directionFlag frame.loaded frame.allocated effect.rip frame.rsp
    input output (ret ▸ inProgram_of_textOffset 0x799e (by decide)),
    (effect.agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans state.count,
    ?_, effect⟩
  have address : stackPtr s + 72 = stackPtr initial - 208 := by
    rw [state.stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  refine ⟨state.value.1, ?_⟩
  intro i hi
  rw [input]
  refine (ScalarFrame.scalar_call_byte (frameOffset := 280) (by decide)
    state.stage.toFrameState effect (offset := 208) (len := 32) (by decide) (by decide) hi).trans ?_
  have value := state.value.2 i hi
  rw [address] at value
  exact value

end P256.Proofs.Nonce.Initialize.Shift
