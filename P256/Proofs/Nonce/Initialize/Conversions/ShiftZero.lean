import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Entry
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Select
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Mix
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem shift_zero_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {value : Nat} (pre : CalleePre s boundary 0x109530 32 32 128)
    (count : s.regValue .rdx = 0) (integer : Nat256At s (s.regValue .rsi) value) :
    ∃ t, CalleeResult s t boundary 32 128 ∧ Nat256At t (s.regValue .rdi) value := by
  obtain ⟨a, limbs, prepared, valueEq⟩ := ShiftZero.prepare_correct pre count integer
  obtain ⟨b, selected⟩ := ShiftZero.select_correct pre prepared
  obtain ⟨c, mixed⟩ := ShiftZero.mix_correct pre selected
  obtain ⟨d, stored⟩ := ShiftZero.store_correct pre mixed
  obtain ⟨t, result, memory⟩ := ShiftZero.epilogue_correct pre stored.toStage stored.rip
  refine ⟨t, result, ?_⟩
  simpa only [Nat256At, memory, valueEq] using stored.output

end P256.Proofs.Nonce.Initialize.Conversions
