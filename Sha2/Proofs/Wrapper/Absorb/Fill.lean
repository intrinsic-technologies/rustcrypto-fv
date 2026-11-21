import Sha2.Proofs.Wrapper.Absorb.FillCopy
import Sha2.Proofs.Wrapper.Absorb.Partial.Correctness
import Sha2.Proofs.Wrapper.Absorb.Blocks.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

theorem fill {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (input : Prepared (v := v) initial s inputs index)
    (rip : s.RIP=(v.pc 0x107))
    (enough : 64-(prefixMessage inputs index).size%64 ≤ (inputs[index]'input.remaining).bytes.size) :
    ∃ t, Blocks.Input (v := v) initial t inputs index (64-(prefixMessage inputs index).size%64) ∧
      t.RIP=(v.pc 0x14c) := by
  obtain ⟨u,filled,ripU⟩ := fill_copy ctx input rip enough
  obtain ⟨t,result⟩ := Partial.compress ctx filled.toPreserved ripU filled.hashWords filled.bytes
  have counts := filled_prefix_counts (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes enough
  refine ⟨t,⟨result.preserved,input.remaining,enough,counts.1,?_,?_,
    result.source.trans filled.source, result.savedRbp.trans filled.length,
    result.indexRegister.trans filled.indexRegister,
    result.countRegister.trans filled.countRegister⟩,result.rip⟩
  · rw [compressBlocks_filled_prefix _ _ _ enough]
    exact result.hashWords
  · rw [result.blocks,filled.blocks,counts.2,BitVec.ofNat_add]
    rfl

end Sha2.Proofs.Wrapper.Absorb
