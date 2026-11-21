import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.Prepare
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.Output

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem store_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (state : MixedState s t boundary a) :
    ∃ u, StoredState s u boundary a := by
  obtain ⟨u, output⟩ := Store.prepare_output pre state
  exact Store.write_output pre output

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
