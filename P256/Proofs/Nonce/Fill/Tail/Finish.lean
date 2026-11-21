import P256.Proofs.Nonce.Fill.Tail.Finish.Input
import P256.Proofs.Nonce.Fill.Tail.Finish.Epilogue
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Signing.Search

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Compared initial s orderAddress state) (rip : s.RIP = 0x1076e5) :
    ∃ fuel t, Advances boundary fuel s t ∧
      ReturnState initial t orderAddress (nextCandidate state).1 (nextState state) := by
  obtain ⟨setupFuel, t, setupRun, prepared⟩ := Finish.prepare pre input rip
  obtain ⟨u, callRun, ready, callEffect⟩ := Program.ScalarFrame.call_step pre.toCalleePre
    (frameOffset := 232) (by decide) (by decide)
    (Program.readyToStep prepared.machine prepared.bindingsSupported)
    prepared.loaded prepared.allocated prepared.rsp 0x76f5 0xfffff846
    (by decide) (by decide +kernel) (by decide +kernel)
    (Program.inProgram_of_textOffset 0x6f40 (by decide)) prepared.rip
  change (X86Proofs.callEffect (fun _ => 0x106f40) 0x1076fa t).Holds t u at callEffect
  obtain ⟨v, result⟩ := Initialize.Conversions.Int2Octets.correct
    (Finish.call_pre pre prepared ready callEffect) (Finish.call_input prepared callEffect)
  obtain ⟨final, finalRip⟩ := Finish.return_state pre prepared ready callEffect result
  obtain ⟨w, epilogueRun, returned⟩ := Finish.epilogue pre final finalRip
  obtain ⟨calleeFuel, calleeRun⟩ := result.execution
  exact ⟨setupFuel + 1 + calleeFuel + 8, w,
    ((setupRun.trans callRun).trans calleeRun).trans epilogueRun, returned⟩

end P256.Proofs.Nonce.Fill.Tail
