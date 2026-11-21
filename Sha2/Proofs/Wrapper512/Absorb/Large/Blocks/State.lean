import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Wrapper512.Absorb.Blocks.State
import Sha2.Proofs.Wrapper512.Absorb.Blocks.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper (prefixMessage prefixMessage_succ)
open Sha2.Proofs.Wrapper512.Absorb.Blocks

structure CompressedSlice [Bindings] (variant : Variant) (initial s : RamState) (inputs : Array Program.Input)
    (index consumed : Nat) (form : Form := .slices) : Prop extends Preserved variant initial s form where
  remaining : index < inputs.size
  consumedBound : consumed ≤ inputs[index].bytes.size
  aligned : (prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed).size % 128 = 0
  hashWords : HashStateAt s (hashPointer initial form form.activeMemory)
    (compressBlocks variant.initialHash (prefixMessage inputs (index+1)))
  blockCount : memLoad s.external (blockCountPointer initial form form.activeMemory) 64 =
    BitVec.ofNat 64 ((prefixMessage inputs (index+1)).size / 128)
  blockCountHigh : memLoad s.external (blockCountHighPointer initial form form.activeMemory) 64 =
    BitVec.ofNat 64 (((prefixMessage inputs (index+1)).size / 128) / 2^64)
  source : variant.sourceValue form s = inputs[index].address + BitVec.ofNat 64 consumed
  length : (.reg (variant.restRegister form) : Operand 64).read s = BitVec.ofNat 64 (inputs[index].bytes.size - consumed)
  indexRegister : variant.indexValue form s = BitVec.ofNat 64 index
  countRegister : variant.countValue form initial s = BitVec.ofNat 64 inputs.size

  outputSaved : form = .traitFinalizeIntoReset false →
    memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx
  bufferRegister : form = .reset 1 →
    s.regValue .rbx = bufferPointer initial form
  memcpyTarget : match form with
    | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
    | .finalizeIntoReset true =>
      s.regValue (if variant = .sha384 ∨ variant = .sha512 then .rbx else .r12) = 0x10dd60
    | _ => True
  activeBufferRegister : ∀ second, form = .traitFinalizeIntoReset second →
    s.regValue .rbx = bufferPointer initial form form.activeMemory

theorem input_of_agrees [Bindings] {variant : Variant} {form : Form}
    {initial s t : RamState} {inputs : Array Program.Input}
    {index consumed fuel : Nat} {components : List Component}
    (ctx : Context variant initial inputs form)
    (input : Absorb.Blocks.Input variant initial s inputs index consumed form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (kept : ∀ r ∈ ([4, 3, 5, 12, 13, 14, variant.restRegister form,
      BitVec.ofNat 5 (variant.traversal form).dataReg,
      BitVec.ofNat 5 (variant.traversal form).indexReg,
      BitVec.ofNat 5 ((variant.traversal form).countReg.getD 0)] : List (BitVec 5)),
      Component.reg r ∉ components)
    (hdf : .df ∉ components := by simp)
    (keptOutput : form = .digest → Component.reg 3 ∉ components := by simp)
    (keptFrameOutput : form = .traitFinalizeIntoReset false →
      (Component.reg (if variant = .sha512 then 13 else 5) ∉ components ∨
        memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) := by simp) :
    Absorb.Blocks.Input variant initial t inputs index consumed form := by
  have sameBytes := fun a => frame.memory a (fun c hc => noMem c hc a)
  have sameLoad (addr : BitVec 64) : memLoad t.external addr 64 = memLoad s.external addr 64 := by
    apply memLoad_congr
    intro i _
    exact congrArg (fun byte : Option UInt8 => byte.getD 0) (sameBytes _)
  refine ⟨preserved_of_agrees ctx input.toPreserved run ready frame
    (fun c hc a ha => (noMem c hc a ha).elim) (kept 4 (by simp)) hdf keptOutput keptFrameOutput,
    input.remaining, input.consumedBound, input.aligned,
    hashState_of_bytes input.hashWords (fun i _ => sameBytes _),
    (sameLoad _).trans input.blockCount, (sameLoad _).trans input.blockCountHigh,
    (frame.read (kept _ (by simp))).trans input.source,
    (frame.read (kept _ (by simp))).trans input.length,
    (frame.read (n := 64) (kept _ (by simp))).trans input.indexRegister, ?_, ?_, ?_, ?_, ?_⟩
  · apply Eq.trans _ input.countRegister
    unfold Variant.countValue
    split
    · rename_i reg hr
      exact frame.read (n := 64) (kept _ (by simp [hr]))
    · exact sameLoad _
  · intro h
    exact (sameLoad _).trans (input.outputSaved h)
  · intro h
    exact (frame.read (n := 64) (kept 3 (by simp))).trans (input.bufferRegister h)
  · have reg3 : t.regValue .rbx = s.regValue .rbx := frame.read (n := 64) (kept 3 (by simp))
    have reg12 : t.regValue .r12 = s.regValue .r12 := frame.read (n := 64) (kept 12 (by simp))
    have target := input.memcpyTarget
    cases form with
    | slices | digest => trivial
    | reset stage => intro h; exact reg3.trans (target h)
    | finalizeIntoReset second =>
      cases second
      · trivial
      · cases variant <;> first | exact reg3.trans target | exact reg12.trans target
    | traitFinalizeIntoReset second => trivial
  · intro second h
    exact (frame.read (n := 64) (kept 3 (by simp))).trans (input.activeBufferRegister second h)

theorem register_block [Bindings] {variant : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {pc : BitVec 64} {bytes : List UInt8}
    {effect : RamState → Effect}
    (ctx : Context variant initial inputs form) (input : Preserved variant initial s form)
    (block : Common.Field.AdvanceTriple (returnBoundary initial)
      (fun s => s.RIP = pc) (codeRange pc bytes) (Effect.post effect))
    (code : CodeIn (codeRange pc bytes) s) (rip : s.RIP = pc)
    (noMem : ∀ c ∈ (effect s).components, ∀ a, ¬ c.Covers a)
    (kept4 : Component.reg 4 ∉ (effect s).components) (hdf : .df ∉ (effect s).components)
    (keptOutput : form = .digest → Component.reg 3 ∉ (effect s).components := by simp)
    (keptFrameOutput : form = .traitFinalizeIntoReset false →
      (Component.reg (if variant = .sha512 then 13 else 5) ∉ (effect s).components ∨
        memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) := by simp) :
    ∃ t, Preserved variant initial t form ∧ (effect s).Holds s t ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (variant.routine form).minStackBytes] := by
  obtain ⟨_, t, run, ready, _, result⟩ := block s
    (supportedMachine_readyToStep input.machine) code rip
  exact ⟨t, preserved_of_agrees ctx input run ready result.agrees
    (fun c hc a ha => (noMem c hc a ha).elim) kept4 hdf keptOutput keptFrameOutput, result, ⟨_, run⟩,
    result.agrees.memoryWriteFrame (fun c hc a ha => (noMem c hc a ha).elim)⟩

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
