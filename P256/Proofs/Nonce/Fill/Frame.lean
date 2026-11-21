import P256.Proofs.Nonce.Fill.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {state : State}

omit [Bindings] in
theorem frameBase_add (initial : RamState) {offset : Nat} (bound : offset ≤ 232) :
    frameBase initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (232 - offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 232 offset (by omega) bound]
  simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem stack_readable (pre : Pre initial boundary orderAddress state)
    (input : Frame initial s) {offset len : Nat} (bound : offset + len ≤ 232) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  rw [input.rsp, frameBase_add initial (by omega)]
  exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) input.allocated

theorem stack_writable8 (pre : Pre initial boundary orderAddress state)
    (input : Frame initial s) {offset : Nat} (bound : offset ≤ 224)
    (aligned : offset % 8 = 0) : MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8 := by
  rw [input.rsp, frameBase_add initial (by omega)]
  exact writable_of_grow (stack_sub_writable8 pre.stack
    (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) (by omega)) input.allocated

theorem stack_code (pre : Pre initial boundary orderAddress state)
    (input : Frame initial s) {offset len codeOffset codeLen : Nat}
    (bound : offset + len ≤ 232) (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  rw [input.rsp, frameBase_add initial (by omega)]
  intro i hi j hj eq
  apply pre.avoids (Stack.region initial 2096) (by simp)
    (stackPtr initial - BitVec.ofNat 64 (232 - offset) + BitVec.ofNat 64 i)
  · exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ⟨i, hi, rfl⟩
  · apply Or.inl
    rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset + j) (by omega)

theorem Frame.after_registers {components : List Component}
    (input : Frame initial s) (ready : ReadyToStep t) (agrees : AgreesExcept components s t)
    (noMemory : ∀ c ∈ components, ∀ a, ¬ c.Covers a) (sp : .reg 4 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Frame initial t := by
  have memory := agrees.external noMemory
  refine ⟨bindingsSupported_of_ready_agrees input.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees input.machine ready agrees, ?_,
    agrees.directionFlagClear hdf input.directionFlag,
    fun a ha => agrees.grow a (input.allocated a ha), ?_,
    (agrees.read (n := 64) (r := 4) sp).trans input.rsp, ?_, ?_,
    (agrees.mxcsr hmxcsr).trans input.mxcsr, (agrees.fcw hfcw).trans input.fp87⟩
  · intro a b hb
    rw [memory]
    exact input.loaded a b hb
  · intro a ha
    rw [memory]
    exact input.frame a ha
  · intro item member
    rw [memory]
    exact input.saved item member
  · rw [memory]
    exact input.returnAddress

omit [Bindings] in
theorem Slots.of_memory_eq (slots : Slots initial s) (memory : t.external = s.external) :
    Slots initial t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [memory]; exact slots.outputSlot
  · rw [memory]; exact slots.lengthSlot
  · rw [memory]; exact slots.bitsSlot
  · rw [memory]; exact slots.statePointerSlot
  · rw [memory]; exact slots.valuePointerSlot
  · rw [memory]; exact slots.generatorPointerSlot

end P256.Proofs.Nonce.Fill
