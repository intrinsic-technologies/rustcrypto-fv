import P256.Proofs.Nonce.Fill.Update.Call
import P256.Proofs.Nonce.Update.Prepare
import P256.Proofs.Nonce.Update.Absorb.Prefix
import P256.Proofs.Nonce.Update.Absorb.Empty
import P256.Proofs.Nonce.Update.Zero
import P256.Proofs.Nonce.Update.Branch
import P256.Proofs.Nonce.Update.Return

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Update

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : State}

theorem correct (pre : Pre initial boundary orderAddress original)
    (input : Generated initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Updated initial t orderAddress state := by
  obtain ⟨setup, readyState, setupRun, ready⟩ := arguments pre input
  obtain ⟨called, callRun, effect, emptyPre⟩ := call pre ready
  obtain ⟨prepareSteps, preparedState, prepareRun, prepared⟩ :=
    Nonce.Update.prepare emptyPre.toDrbgCalleePre
  obtain ⟨prefixSteps, taggedState, prefixRun, tagged⟩ :=
    Nonce.Update.Absorb.prefix emptyPre.toDrbgCalleePre prepared
  obtain ⟨absorbSteps, absorbedState, absorbRun, absorbed⟩ :=
    Nonce.Update.Absorb.empty emptyPre tagged
  obtain ⟨zeroSteps, zeroState, zeroRun, zero⟩ :=
    Nonce.Update.zero (input := .empty) emptyPre absorbed
  obtain ⟨finishedState, finishRun, finished⟩ := Nonce.Update.finish_empty emptyPre zero
  obtain ⟨t, result⟩ := Nonce.Update.finish emptyPre.toDrbgCalleePre finished
    ⟨prepareSteps + prefixSteps + absorbSteps + zeroSteps + 2,
      (((prepareRun.trans prefixRun).trans absorbRun).trans zeroRun).trans finishRun⟩
  obtain ⟨fuel, bodyRun⟩ := result.execution
  exact ⟨setup + 1 + fuel, t, (setupRun.trans callRun).trans bodyRun,
    returned pre ready effect result⟩

end P256.Proofs.Nonce.Fill.Update
