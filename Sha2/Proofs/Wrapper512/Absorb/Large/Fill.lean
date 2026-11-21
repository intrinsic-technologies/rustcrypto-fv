import Sha2.Proofs.Wrapper512.Absorb.Large.FillCopy
import Sha2.Proofs.Wrapper512.Absorb.Large.Compress
import Sha2.Proofs.Wrapper512.Absorb.Large.Arithmetic
import Sha2.Proofs.Wrapper512.Absorb.Blocks.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large

open Sha2.Proofs.Wrapper (prefixMessage)
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512

theorem fill [Bindings] (body : Compression.BlockCorrect) {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context v initial inputs form) (input : Prepared v initial s inputs index form)
    (rip : s.RIP = v.pc (FillSetup.startOffset v form) form)
    (enough : 128-(prefixMessage inputs index).size%128 ≤ (inputs[index]'input.remaining).bytes.size)
    (nonDigest : form ≠ .digest := by decide)
    (bufferRegister : form = .reset 1 → s.regValue .rbx = bufferPointer initial form := input.bufferRegister)
    (memcpyTarget : match (generalizing := false) form with
      | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second =>
        s.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True := by
        cases form with
        | finalizeIntoReset second => cases second <;> exact input.memcpyTarget
        | _ => exact input.memcpyTarget) :
    ∃ t, Absorb.Blocks.Input v initial t inputs index (128-(prefixMessage inputs index).size%128) form ∧
      t.RIP=v.pc (finishMoveOffset v form + 3) form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  obtain ⟨u,filled,ripU,⟨copyFuel,copyRun⟩,copyFrame⟩ := fill_copy ctx input rip enough nonDigest bufferRegister memcpyTarget
  obtain ⟨t,result⟩ := compress body ctx filled.toPreserved ripU filled.hashWords filled.bytes
    nonDigest filled.bufferRegister filled.outputSaved
  have counts := filled_prefix_counts (prefixMessage inputs index)
    (inputs[index]'input.remaining).bytes enough
  have low := filled.blocks
  have high := filled.blocksHigh
  change memLoad u.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 = _ at low
  change memLoad u.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 = _ at high
  obtain ⟨compressFuel,compressRun⟩ := result.execution
  refine ⟨t,⟨result.preserved,input.remaining,enough,counts.1,?_,?_,?_,
    result.source.trans filled.source, result.restRegister.trans filled.length,
    result.indexRegister.trans filled.indexRegister,
    result.countRegister.trans filled.countRegister,
    (fun h => (result.outputSaved h).trans (filled.outputSaved h)),
    (fun h => (result.bufferRegister h).trans (filled.bufferRegister h)),
    ?_, result.activeBufferRegister⟩,result.rip,
    ⟨_,copyRun.trans compressRun⟩,memoryWriteFrame_trans copyFrame result.stackFrame⟩
  · rw [compressBlocks_filled_prefix _ _ _ enough]
    exact result.hashWords
  · change memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 = _
    rw [result.blocks,low,counts.2,BitVec.ofNat_add]
    rfl

  · change memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 = _
    rw [result.blocksHigh, high, low, counts.2]
    exact count_high_add _ 1 (by decide)

  · have preserved := result.memcpyTarget
    have target := filled.memcpyTarget
    cases form with
    | slices | digest | traitFinalizeIntoReset second => trivial
    | reset stage => exact fun h => (preserved h).trans (target h)
    | finalizeIntoReset second =>
      cases second
      · trivial
      · exact preserved.trans target

end Sha2.Proofs.Wrapper512.Absorb.Large
