import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Finish

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix

theorem recenter_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : NibbleState s t d) :
    ∃ fuel u, Advances boundary fuel t u ∧ DigitsState s u d ∧
      AgreesExcept (Radix.digitComponents s) t u := by
  obtain ⟨fuel,u,run,loop,agrees⟩ := Recenter.loop_all pre (Recenter.loop_initial state) 32 (by decide)
  exact ⟨fuel,u,run,Recenter.loop_final loop,agrees⟩

end P256.Proofs.Projective.Multiply.Machine.Radix
