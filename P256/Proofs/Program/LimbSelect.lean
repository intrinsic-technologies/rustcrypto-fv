import P256.Proofs.Program.LimbSelect.Prologue
import P256.Proofs.Program.LimbSelect.Loop
import P256.Proofs.Program.LimbSelect.Finish

set_option autoImplicit false

namespace P256.Proofs.Program.LimbSelect

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem limb_select32_low8_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {select : Bool} (pre : Pre s boundary)
    (choice : (s.regValue .r8).setWidth 8 = if select then 1 else 0) :
    ∃ t, CalleeResult s t boundary 32 80 ∧ SelectedBytesAt s t select := by
  obtain ⟨t, ⟨f, hf⟩, ht, hrt⟩ := prologue pre choice
  obtain ⟨u, ⟨g, hg⟩, hu, hru⟩ := loop pre ht hrt
  exact finish pre hu hru ⟨f + g, hf.trans hg⟩

theorem limb_select32_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {select : Bool} (pre : Pre s boundary)
    (choice : s.regValue .r8 = if select then 1 else 0) :
    ∃ t, CalleeResult s t boundary 32 80 ∧ SelectedBytesAt s t select := by
  apply limb_select32_low8_correct pre
  rw [choice]
  cases select <;> rfl

end P256.Proofs.Program.LimbSelect
