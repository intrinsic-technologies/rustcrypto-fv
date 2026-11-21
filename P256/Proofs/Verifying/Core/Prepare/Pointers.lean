import P256.Proofs.Verifying.Core.Prepare.First

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare

open X86 X86.Machine X86Proofs

theorem Pointers.after {s t u : RamState} {cs : List Component}
    (pointers : Pointers s t) (agrees : AgreesExcept cs t u)
    (excluded : .reg 3 ∉ cs) : Pointers s u := by
  exact ⟨(agrees.read (n := 64) (r := 3) excluded).trans pointers.signature⟩

end P256.Proofs.Verifying.Core.Prepare
