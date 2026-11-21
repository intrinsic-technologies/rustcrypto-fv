import P256.Proofs.Signing.Core.Iteration.Components.Addition.Input
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Sum
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Epilogue
import P256.Proofs.Signing.Core.Iteration.Components.Callees

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem correct : Components.AddContract := by
  intro bindings s boundary a b pre left right leftCanonical rightCanonical
  obtain ⟨entered, enterRun, enterState, enterRip, rsi, rdx, output, modulus, left', right'⟩ :=
    start pre left right
  obtain ⟨sumFuel, summed, sumRun, sumState⟩ :=
    sum_stage pre enterState enterRip rsi rdx output modulus left' right'
  obtain ⟨subFuel, subtracted, subRun, subState⟩ := subtract_stage pre sumState
  obtain ⟨outputFuel, written, outputRun, outputState, outputRip, result⟩ :=
    output_stage pre subState leftCanonical rightCanonical
  obtain ⟨final, returned, memory⟩ := epilogue pre.toCalleePre outputState outputRip
    ⟨9 + sumFuel + subFuel + outputFuel, ((enterRun.trans sumRun).trans subRun).trans outputRun⟩
  refine ⟨final, returned, result.1, ?_⟩
  intro i hi
  rw [memory]
  exact result.2 i hi

end P256.Proofs.Signing.Core.Iteration.Components.Addition
