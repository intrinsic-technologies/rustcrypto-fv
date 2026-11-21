import P256.Proofs.Program.ScalarFrame.Work
import P256.Proofs.Program.ScalarFrame.State
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.Program.ScalarFrame

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable {entry : BitVec 64} {inputBytes outputBytes stackReserve frameOffset : Nat}

variable {inputRegister : Syntax.Reg}

theorem stack_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister) {offset len : Nat} {a : BitVec 64}
    (hoffset : offset ≤ stackReserve) (hlen : len ≤ offset + 8)
    (covered : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers a) :
    (Stack.region s stackReserve).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat pre.stack hoffset]
    change (stackPtr s).toNat - stackReserve ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack hoffset]
    have := stack_bounds pre.stack
    omega

abbrev workRegion (s : RamState) (stackReserve : Nat) : MemoryRegion :=
  Work.region s stackReserve 48

theorem scalar_stack_address {s t : RamState} (hsp : stackPtr t = stackPtr s - BitVec.ofNat 64 frameOffset)
    {offset : Nat} (hframe : frameOffset < 2^64) (h : offset ≤ frameOffset) :
    stackPtr t + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (frameOffset - offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le frameOffset offset (by omega) h, hsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem work_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister) {offset len : Nat} {a : BitVec 64}
    (ho : offset ≤ stackReserve) (hl : len + 48 ≤ offset)
    (covered : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion s stackReserve).Contains a.toNat :=
  Work.contains pre ho hl covered

theorem output_work_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi outputBytes, workRegion s stackReserve]) :
    MemoryWriteFrame t u #v[registerRegion s .rdi outputBytes, Stack.region s stackReserve] :=
  Work.frame pre memory

theorem output_work_read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hreserve : 48 ≤ stackReserve)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi outputBytes, workRegion s stackReserve])
    {offset n : Nat} (ho : offset ≤ 48) (hl : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t :=
  Work.read pre hreserve memory ho hl

theorem loaded_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi outputBytes, Stack.region s stackReserve]) :
    ProgramLoaded t := by
  intro a b hf
  rw [frame a]
  · exact pre.loaded a b hf
  · intro region hr hin
    exact pre.avoids region (by simpa using hr) a hin (.inl ⟨b, hf⟩)

theorem FrameState.after_effect [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hreserve : 48 ≤ stackReserve)
    (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset)) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi outputBytes, workRegion s stackReserve])
    (sp : .reg 4 ∉ cs) (hdf : Component.df ∉ cs := by component_not_mem) (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : FrameState s u outputBytes stackReserve (BitVec.ofNat 64 frameOffset) := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans state.frame (output_work_frame pre memory)
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    loaded_of_frame pre total, agrees.directionFlagClear hdf state.directionFlag,
    fun a ha => agrees.grow a (state.allocated a ha), total,
    (agrees.read (n := 64) (r := 4) sp).trans state.rsp, ?_, ?_,
    (agrees.mxcsr hmxcsr).trans state.mxcsr, (agrees.fcw hfcw).trans state.fp87⟩
  · intro entry he
    have bound : entry.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre hreserve memory bound (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre hreserve memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem stack_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister) (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset))
    {offset len : Nat} (hframe : frameOffset ≤ stackReserve) (bound : offset + len ≤ frameOffset) :
    MemReadable t (stackPtr t + BitVec.ofNat 64 offset) len := by
  rw [scalar_stack_address state.rsp (by have := stack_bounds pre.stack; omega) (by omega)]
  exact readable_of_grow
    (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated

theorem stack_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister) (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset))
    {offset len : Nat} (hframe : frameOffset ≤ stackReserve) (bound : offset + len ≤ frameOffset) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      (stackPtr t + BitVec.ofNat 64 offset) len := by
  have readable := stack_readable pre state hframe bound
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi hreserved
  apply pre.avoids (Stack.region s stackReserve) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ (.inr hreserved)
  rw [scalar_stack_address state.rsp (by have := stack_bounds pre.stack; omega) (by omega)]
  exact stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩

theorem stack_code [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister) (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset))
    {offset len codeOffset codeLen : Nat} (hframe : frameOffset ≤ stackReserve) (bound : offset + len ≤ frameOffset)
    (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s stackReserve) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · rw [scalar_stack_address state.rsp (by have := stack_bounds pre.stack; omega) (by omega)]
    exact stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩
  · apply Or.inl
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset + j) (by omega)

end P256.Proofs.Program.ScalarFrame
