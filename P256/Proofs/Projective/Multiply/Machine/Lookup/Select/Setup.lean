import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Machine
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Facts

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup [Bindings] {s : RamState} {boundary : ReturnBoundary} {select : Bool}
    (pre : BinaryFieldPre s boundary 0x114380 128)
    (choice : (s.regValue .rcx).setWidth 8 = if select then 1 else 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ CallState s t select := by
  obtain ⟨fuel, t, run, ready, effect⟩ := setup_machine pre.toCalleePre
  exact ⟨fuel, t, run, setup_state pre choice ready effect⟩

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
