import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Select
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Compressed
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run [Bindings] (body : Common.SHA512.Compression.BlockCorrect) {variant : Variant} {form : Form} {initial s : RamState} {inputs : Array Program.Input}
    {index consumed : Nat} (ctx : Context variant initial inputs form)
    (input : Absorb.Blocks.Input variant initial s inputs index consumed form)
    (entry : s.RIP = countPC variant false form ∨ s.RIP = countPC variant true form)
    (nonDigest : form ≠ .digest := by decide) :
    ∃ t, Absorb.Blocks.Result variant initial t inputs index form ∧ t.RIP = tailEndPC variant form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (variant.routine form).minStackBytes] := by
  have entryChoice : ∃ empty, s.RIP = countPC variant empty form := by
    rcases entry with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨empty,rip⟩ := entryChoice
  obtain ⟨u,inputU,countU,ripU,⟨fuelU,runU⟩,frameU⟩ := select ctx input empty rip nonDigest
  by_cases zero : ((inputs[index]'input.remaining).bytes.size-consumed)/128 = 0
  · have ripU' : u.RIP = tailPC variant form := by simpa only [zero,↓reduceIte] using ripU
    obtain ⟨t,result,ripT,⟨fuelT,runT⟩,frameT⟩ := tail ctx (skip inputU zero) ripU' nonDigest
    exact ⟨t,result,ripT,⟨_,runU.trans runT⟩, memoryWriteFrame_trans frameU frameT⟩
  · have ripU' : u.RIP = compressPC variant form := by simpa only [zero,↓reduceIte] using ripU
    obtain ⟨v,inputV,ripV,⟨fuelV,runV⟩,frameV⟩ := compress body ctx inputU ripU' countU nonDigest
    obtain ⟨t,result,ripT,⟨fuelT,runT⟩,frameT⟩ := tail ctx inputV ripV nonDigest
    exact ⟨t,result,ripT,⟨_,(runU.trans runV).trans runT⟩,
      memoryWriteFrame_trans (memoryWriteFrame_trans frameU frameV) frameT⟩

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
