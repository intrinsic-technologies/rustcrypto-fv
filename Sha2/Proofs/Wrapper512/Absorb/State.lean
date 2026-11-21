import Sha2.Proofs.Wrapper512.Model

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512
def Variant.restRegister (v : Variant) (form : Form) : BitVec 5 :=
  match form with
  | .reset stage => if stage.val == 0 then 3 else 5
  | .finalizeIntoReset second =>
    match v with
    | .sha384 | .sha512 => if second then 5 else 3
    | _ => if second then 5 else 3
  | .traitFinalizeIntoReset second => if second then 14 else 12
  | _ => 5

def Variant.loadedOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .slices => 0x138
  | .digest => 0x138
  | .reset _ => (v.traversal form).head + 30
  | .finalizeIntoReset second =>
    (v.traversal form).head + if second && (v == .sha512_224 || v == .sha512_256) then 25 else 26
  | .traitFinalizeIntoReset second => (v.traversal form).head + if second then 39 else 40


end Sha2.Proofs.Wrapper512

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512
open Sha2.Proofs.Wrapper

structure Iteration [Bindings] (v : Variant) (initial s : RamState) (inputs : Array Input) (index : Nat) (form : Form := .slices)
    (memory : ResetLayout.MemoryOffsets := form.bufferedMemory) : Prop
    extends Buffered v initial s (prefixMessage inputs index) form memory where
  indexRegister : v.indexValue form s = BitVec.ofNat 64 index
  countRegister : v.countValue form initial s = BitVec.ofNat 64 inputs.size
  remaining : index < inputs.size
  outputSaved : form = .traitFinalizeIntoReset false →
    memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx

  bufferRegister : form = .reset 1 →
    s.regValue .rbx = bufferPointer initial form
  memcpyTarget : match form with
    | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
    | .finalizeIntoReset true =>
      s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
    | .traitFinalizeIntoReset second =>
      s.regValue (if second then .rbp else .r13) = 0x10dd60
    | _ => True

structure SliceState [Bindings] (v : Variant) (initial s : RamState) (inputs : Array Input) (index : Nat) (form : Form := .slices) : Prop
    extends Iteration v initial s inputs index form form.activeMemory where
  source : v.sourceValue form s = inputs[index].address
  length : v.lengthValue form s = BitVec.ofNat 64 inputs[index].bytes.size
  position : v.tailValue form s = BitVec.ofNat 64 ((prefixMessage inputs index).size % 128)

structure Loaded [Bindings] (v : Variant) (initial s : RamState) (inputs : Array Input) (index : Nat) (form : Form := .slices) : Prop
    extends SliceState v initial s inputs index form where
  rip : s.RIP = v.pc (v.loadedOffset form) form

theorem iteration_of_loop [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {index : Nat} {form : Form}
    (input : LoopState v initial s inputs index form) : Iteration v initial s inputs index form :=
  ⟨input.toBuffered, input.indexRegister, input.countRegister, input.remaining, input.outputSaved, input.bufferRegister, (by
    cases form with
    | finalizeIntoReset second => cases second <;> exact input.memcpyTarget
    | _ => exact input.memcpyTarget)⟩

theorem SavedStackAt.of_bytes {initial s t : RamState} (h : SavedStackAt initial s)
    (bytes : ∀ a, (Component.mem (stackPtr initial - 48) 56).Covers a →
      t.external[a]? = s.external[a]?) : SavedStackAt initial t := by
  have read (offset : Nat) (bound : offset ≤ 48) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    have addr : stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
        stackPtr initial - 48 + BitVec.ofNat 64 (48 - offset + i) := by
      have offsetEq : (48 : BitVec 64) = BitVec.ofNat 64 offset + BitVec.ofNat 64 (48 - offset) := by
        rw [← BitVec.ofNat_add, Nat.add_sub_cancel' bound]
        rfl
      rw [BitVec.ofNat_add, offsetEq]
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]
      congr 2
      rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add]
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [bytes _ ⟨48 - offset + i, by omega, addr⟩]
  constructor
  · intro slot hs
    exact (read slot.2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (h.words slot hs)
  · have zero := read 0 (by decide)
    simp only [BitVec.sub_zero] at zero
    exact zero.trans h.returnAddress

theorem State.of_agrees [bindings : Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {form : Form} {components : List Component} {fuel : Nat}
    (h : State v initial s form) (ctx : Context v initial inputs form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (writes : WritesWithin components
      (v.writeRegions initial form))
    (kept4 : Component.reg 4 ∉ components)
    (saved : ∀ c ∈ components, ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a)
    (hdf : .df ∉ components := by simp) :
    State v initial t form := by
  have memory := frame.memoryWriteFrame writes
  obtain ⟨n, hn⟩ := h.execution
  refine ⟨⟨n + fuel, hn.trans run⟩,
    supportedMachine_of_ready_agrees h.machine ready frame, ?_,
    fun a ha => frame.grow a (h.allocated a ha),
    SavedStackAt.of_bytes h.saved (fun a ha => frame.memory a (fun c hc => saved c hc a ha)),
    frame.directionFlagClear hdf h.directionFlag, memoryWriteFrame_trans h.frame memory, ?_⟩
  · intro address byte fetch
    rw [memory address]
    · exact h.loaded address byte fetch
    · intro region hr ha
      exact (ctx.separation.2 region (by simpa using hr)).2 address ha (.inl ⟨byte, fetch⟩)
  · have rsp0 : stackPtr t = stackPtr initial - BitVec.ofNat 64 form.frameBytes := by
      exact (frame.read (n := 64) (r := 4) kept4).trans h.rsp
    exact rsp0

theorem buffered_of_agrees [Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {form : Form} {layout : ResetLayout.MemoryOffsets} {message : ByteArray} {fuel : Nat} {components : List Component}
    (ctx : Context v initial inputs form) (input : Buffered v initial s message form layout)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (kept4 : Component.reg 4 ∉ components) (hdf : .df ∉ components := by simp)
    (keptOutput : form = .digest → Component.reg 3 ∉ components := by simp)
    (keptFrameOutput : form = .traitFinalizeIntoReset false →
      (Component.reg (if v = .sha512 then 13 else 5) ∉ components ∨
        memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) := by simp) :
    Buffered v initial t message form layout := by
  have memory : t.external = s.external := frame.external noMem
  have state := State.of_agrees input.toState ctx run ready frame
    (fun c hc a ha => (noMem c hc a ha).elim) kept4
    (fun c hc a _ => noMem c hc a) hdf
  refine ⟨⟨state, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · cases form with
    | slices => simpa only [memory] using input.outputPointer
    | digest => exact (frame.read (n := 64) (r := 3) (keptOutput rfl)).trans input.outputPointer
    | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
      refine ⟨?_, by simpa only [memory] using input.outputPointer.2⟩
      rcases input.outputPointer.1 with h | ⟨h, hr⟩
      · exact .inl (by simpa only [memory] using h)
      · rcases keptFrameOutput h with kept | saved
        · refine .inr ⟨h, ?_⟩
          have same := frame.read (n := 64) (r := if v = .sha512 then 13 else 5) kept
          have sameReg : t.regValue (if v = .sha512 then .r13 else .rbp) =
              s.regValue (if v = .sha512 then .r13 else .rbp) := by
            cases v <;> exact same
          exact sameReg.trans hr
        · cases h <;> (apply Or.inl
                       simpa only [memory, Form.secondOutput, Bool.false_eq_true, ite_false] using saved)
  · cases form <;> first | trivial | simpa only [memory] using input.pointerTable
  · cases form <;> first | trivial | simpa only [memory] using input.lengthTable
  · exact ⟨input.hashWords.1, fun i hi => by simpa only [memory] using input.hashWords.2 i hi⟩
  · simpa only [memory] using input.tailBytes
  · simpa only [memory] using input.tailLength
  · simpa only [memory] using input.blockCount
  · simpa only [memory] using input.blockCountHigh

theorem SliceState.of_agrees [Bindings] {v : Variant} {initial s t : RamState} {inputs : Array Input}
    {index fuel : Nat} {components : List Component} {form : Form}
    (ctx : Context v initial inputs form) (input : SliceState v initial s inputs index form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (kept : ∀ r ∈ ([BitVec.ofNat 5 (v.traversal form).lengthReg, 4,
      BitVec.ofNat 5 (v.traversal form).tailReg, BitVec.ofNat 5 (v.traversal form).dataReg,
      BitVec.ofNat 5 (v.traversal form).indexReg,
      BitVec.ofNat 5 ((v.traversal form).countReg.getD 0)] : List (BitVec 5)),
      Component.reg r ∉ components)
    (hdf : .df ∉ components := by simp)
    (keptOutput : form = .digest → Component.reg 3 ∉ components := by simp)
    (keptBuffer : form = .reset 1 → Component.reg 3 ∉ components := by simp)
    (keptMemcpy : match form with
      | .reset stage => stage.val = 2 → Component.reg 3 ∉ components
      | .finalizeIntoReset true => Component.reg (if v = .sha384 ∨ v = .sha512 then 3 else 12) ∉ components
      | .traitFinalizeIntoReset second => Component.reg (if second then 5 else 13) ∉ components
      | _ => True := by simp)
 :
    SliceState v initial t inputs index form := by
  have memory := frame.external noMem
  have count : v.countValue form initial t = v.countValue form initial s := by
    unfold Variant.countValue
    split
    · rename_i reg hreg
      exact frame.read (n := 64) (r := BitVec.ofNat 5 reg) (kept _ (by simp [hreg]))
    · rw [memory]
  refine {
    toIteration := ⟨buffered_of_agrees ctx input.toBuffered run ready frame noMem
      (kept 4 (by simp)) hdf keptOutput (fun h => .inr (input.outputSaved h)),
      (frame.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).indexReg)
        (kept _ (by simp))).trans input.indexRegister,
      count.trans input.countRegister, input.remaining,
      (fun h => by simpa only [memory] using input.outputSaved h),
      (fun h => (frame.read (n := 64) (r := 3) (keptBuffer h)).trans (input.bufferRegister h)),
      ?_⟩
    source := (frame.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).dataReg)
      (kept _ (by simp))).trans input.source
    length := (frame.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).lengthReg)
      (kept _ (by simp))).trans input.length
    position := (frame.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).tailReg)
      (kept _ (by simp))).trans input.position
  }
  · cases form with
    | slices | digest => trivial
    | reset stage =>
      intro h
      exact (frame.read (n := 64) (r := 3) (keptMemcpy h)).trans (input.memcpyTarget h)
    | finalizeIntoReset second =>
      cases second with
      | false => trivial
      | true =>
        have same := frame.read (n := 64)
          (r := if v = .sha384 ∨ v = .sha512 then 3 else 12) keptMemcpy
        cases v <;> exact same.trans input.memcpyTarget
    | traitFinalizeIntoReset second =>
      have same := frame.read (n := 64) (r := if second then 5 else 13) keptMemcpy
      cases second <;> exact same.trans input.memcpyTarget

end Sha2.Proofs.Wrapper512.Absorb
