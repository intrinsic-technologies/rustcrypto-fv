import Sha2.Proofs.Wrapper.Absorb.State
import Sha2.Proofs.Wrapper.Absorb.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

structure Input [Bindings] (initial s : RamState) (inputs : Array Program.Input)
    (index consumed : Nat) (v : Variant := .sha256) : Prop extends Preserved (v := v) initial s where
  remaining : index < inputs.size
  consumedBound : consumed ≤ inputs[index].bytes.size
  aligned : (prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed).size % 64 = 0
  hashWords : HashStateAt s (stackPtr initial - 88)
    (compressBlocks v.initialHash
      (prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed))
  blocks : memLoad s.external (stackPtr initial - 56) 64 = BitVec.ofNat 64
    ((prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed).size / 64)
  source : s.regValue .r13 = inputs[index].address + BitVec.ofNat 64 consumed
  length : s.regValue .rbp = BitVec.ofNat 64 (inputs[index].bytes.size - consumed)
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 index
  countRegister : s.regValue .r15 = BitVec.ofNat 64 inputs.size

structure Result [Bindings] (initial s : RamState) (inputs : Array Program.Input)
    (index : Nat) (v : Variant := .sha256) : Prop extends Buffered (v := v) initial s (prefixMessage inputs (index + 1)) where
  rip : s.RIP = (v.pc 0x19f)
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 index
  countRegister : s.regValue .r15 = BitVec.ofNat 64 inputs.size

theorem Input.of_agrees [Bindings] {v : Variant} {initial s t : RamState} {inputs : Array Program.Input}
    {index consumed fuel : Nat} {components : List Component}
    (ctx : Context (v := v) initial inputs) (input : Input (v := v) initial s inputs index consumed)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (kept : ∀ r ∈ ([4,5,13,14,15] : List (BitVec 5)), Component.reg r ∉ components)
    (hdf : .df ∉ components := by simp) :
    Input (v := v) initial t inputs index consumed := by
  have bytes := fun a => frame.memory a (fun c hc => noMem c hc a)
  refine ⟨preserved_of_agrees ctx input.toPreserved run ready frame
    (fun c hc a ha => (noMem c hc a ha).elim) (kept 4 (by simp)) hdf,
    input.remaining, input.consumedBound, input.aligned,
    hashState_of_bytes input.hashWords (fun i _ => bytes _), ?_,
    (frame.read (n := 64) (r := 13) (kept 13 (by simp))).trans input.source,
    (frame.read (n := 64) (r := 5) (kept 5 (by simp))).trans input.length,
    (frame.read (n := 64) (r := 14) (kept 14 (by simp))).trans input.indexRegister,
    (frame.read (n := 64) (r := 15) (kept 15 (by simp))).trans input.countRegister⟩
  rw [← input.blocks]
  apply memLoad_congr
  intro i _
  exact congrArg (fun byte : Option UInt8 => byte.getD 0) (bytes _)

end Sha2.Proofs.Wrapper.Absorb.Blocks
