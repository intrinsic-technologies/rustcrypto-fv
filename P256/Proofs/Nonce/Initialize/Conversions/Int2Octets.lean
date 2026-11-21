import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prologue
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar

theorem correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {value : Nat} (pre : Pre s boundary)
    (integer : Nat256At s (s.regValue .rdi) value) :
    ∃ t, Result s t boundary value := by
  obtain ⟨s₁, stage₁, registers₁, rip₁⟩ := prologue_correct pre
  obtain ⟨s₂, stage₂, registers₂, rip₂⟩ :=
    prefix_correct pre stage₁ registers₁ rip₁
  obtain ⟨s₃, stage₃, rip₃, output⟩ :=
    loop_correct pre stage₂ integer registers₂ rip₂
  exact finish_correct pre stage₃ rip₃ output

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
