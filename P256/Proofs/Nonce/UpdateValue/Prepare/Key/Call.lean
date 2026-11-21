import P256.Proofs.Nonce.UpdateValue.Prepare.Key.Arguments
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStackInput

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Key

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}

omit [Bindings] in
theorem output_address : scratch initial + 8 = stackPtr initial - 480 := by
  change stackPtr initial - 488 + 8 = stackPtr initial - 480
  rw [show (488 : BitVec 64) = 480 + 8 by decide, ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem call (pre : UpdateValuePre initial boundary state) (input : Saved initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (Setup.effect s).Holds s t := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Setup.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (Setup.code input.loaded) (arguments pre input)
  exact ⟨fuel, t, run, ready, effect⟩

end P256.Proofs.Nonce.UpdateValue.Prepare.Key
