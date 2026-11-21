import Hkdf.Proofs.Standard.Initialization.Pad
import Hkdf.Proofs.Standard.Initialization.Inner
import Hkdf.Proofs.Standard.Initialization.OuterPad
import Hkdf.Proofs.Standard.Initialization.Outer

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Initialization

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common

theorem initialize_correct [Bindings] {initial : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) :
    ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧ ReadyToStep t ∧
      Standard.Initialized initial t salt := by
  obtain ⟨_, innerPad, _, readyInnerPad, preserved, rip, block⟩ := inner_pad ctx
  obtain ⟨_, innerHash, _, readyInnerHash, inner⟩ :=
    inner_hash ctx readyInnerPad preserved rip block
  obtain ⟨_, outerPad, _, readyOuterPad, outer⟩ := outer_pad ctx readyInnerHash inner
  obtain ⟨_, pads, _, _, compressed⟩ := outer_hash ctx readyOuterPad outer
  obtain ⟨t, initialized⟩ := assemble ctx compressed
  obtain ⟨fuel, run⟩ := initialized.execution
  exact ⟨fuel, t, run, Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep initialized.machine, initialized⟩

end Hkdf.Proofs.Standard.Initialization
