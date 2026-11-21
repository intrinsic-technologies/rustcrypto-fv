import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Select.Guard

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem select_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (state : PreparedState s t boundary a) :
    ∃ u, SelectedState s u boundary a := by
  obtain ⟨u, loaded⟩ := load_correct pre state
  obtain ⟨v, masked⟩ := mask_correct pre loaded
  exact selected_of_masked pre masked

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
