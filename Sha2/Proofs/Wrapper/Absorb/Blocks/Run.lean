import Sha2.Proofs.Wrapper.Absorb.Blocks.Select
import Sha2.Proofs.Wrapper.Absorb.Blocks.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (ctx : Context (v := v) initial inputs)
    (input : Input (v := v) initial s inputs index consumed)
    (entry : s.RIP = (v.pc 0x14c) ∨ s.RIP = (v.pc 0x1b0)) :
    ∃ t, Result (v := v) initial t inputs index := by
  have entryChoice : ∃ empty, s.RIP = countPC empty v := by
    rcases entry with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨empty,rip⟩ := entryChoice
  obtain ⟨u,inputU,countU,ripU⟩ := select ctx input empty rip
  by_cases zero : ((inputs[index]'input.remaining).bytes.size-consumed)/64 = 0
  · have ripU' : u.RIP = (v.pc 0x16d) := by simpa only [zero,↓reduceIte] using ripU
    exact tail ctx (skip inputU zero) ripU'
  · have ripU' : u.RIP = (v.pc 0x155) := by simpa only [zero,↓reduceIte] using ripU
    obtain ⟨mid,inputV,ripV⟩ := compress ctx inputU ripU' countU
    exact tail ctx inputV ripV

end Sha2.Proofs.Wrapper.Absorb.Blocks
