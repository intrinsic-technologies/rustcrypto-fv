import Sha2.Proofs.Wrapper.Buffered

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

structure Iteration [Bindings] (initial s : RamState) (inputs : Array Input) (index : Nat) (v : Variant := .sha256) : Prop
    extends Buffered (v := v) initial s (prefixMessage inputs index) where
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 index
  countRegister : s.regValue .r15 = BitVec.ofNat 64 inputs.size
  remaining : index < inputs.size

structure SliceState [Bindings] (initial s : RamState) (inputs : Array Input) (index : Nat) (v : Variant := .sha256) : Prop
    extends Iteration (v := v) initial s inputs index where
  source : s.regValue .r13 = inputs[index].address
  length : s.regValue .rbx = BitVec.ofNat 64 inputs[index].bytes.size
  position : s.regValue .r12 = BitVec.ofNat 64 ((prefixMessage inputs index).size % 64)

structure Loaded [Bindings] (initial s : RamState) (inputs : Array Input) (index : Nat) (v : Variant := .sha256) : Prop
    extends SliceState (v := v) initial s inputs index where
  rip : s.RIP = (v.pc 0xee)

theorem iteration_of_loop {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (input : LoopState (v := v) initial s inputs index) : Iteration (v := v) initial s inputs index :=
  ⟨input.toBuffered, input.indexRegister, input.countRegister, input.remaining⟩

theorem SliceState.of_agrees {v : Variant} [Bindings] {initial s t : RamState} {inputs : Array Input}
    {index fuel : Nat} {components : List Component}
    (ctx : Context (v := v) initial inputs) (input : SliceState (v := v) initial s inputs index)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (kept : ∀ r ∈ ([3,4,12,13,14,15] : List (BitVec 5)), Component.reg r ∉ components)
    (hdf : .df ∉ components := by simp) :
    SliceState (v := v) initial t inputs index := by
  refine {
    toIteration := ⟨buffered_of_agrees ctx input.toBuffered run ready frame noMem (kept 4 (by simp)) hdf,
      (frame.read (n := 64) (r := 14) (kept 14 (by simp))).trans input.indexRegister,
      (frame.read (n := 64) (r := 15) (kept 15 (by simp))).trans input.countRegister,
      input.remaining⟩
    source := (frame.read (n := 64) (r := 13) (kept 13 (by simp))).trans input.source
    length := (frame.read (n := 64) (r := 3) (kept 3 (by simp))).trans input.length
    position := (frame.read (n := 64) (r := 12) (kept 12 (by simp))).trans input.position
  }

end Sha2.Proofs.Wrapper.Absorb
