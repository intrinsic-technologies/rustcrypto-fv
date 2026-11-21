import P256.Proofs.Nonce.Initialize.State
import P256.Proofs.Nonce.Initialize.Prepare.Memory
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64}

theorem stack_address (stage : Stage initial s boundary) {offset : Nat} (bound : offset ≤ 280) :
    stackPtr s + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (280 - offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 280 offset (by omega) bound, stage.rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem stack_readable (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) {offset len : Nat}
    (bound : offset ≤ 280) (span : offset + len ≤ 288) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  rw [stack_address stage bound]
  exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) stage.allocated

theorem stack_sub_contains (pre : InitializePre initial boundary orderAddress)
    {offset len : Nat} (bound : offset ≤ 2144) (span : len ≤ offset + 8)
    {a : BitVec 64} (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a) :
    (Stack.region initial 2144).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat pre.stack bound]
    change (stackPtr initial).toNat - 2144 ≤ (stackPtr initial).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack bound]
    have := (stack_bounds pre.stack).1
    omega

theorem output_writable (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (initial.regValue .rdi) 72 := by
  have readable := readable_of_grow
    (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _))
    stage.allocated
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved (by change 0 < 72; decide) readable.low
  intro i hi reserved
  exact pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr reserved)

theorem output_contains (pre : InitializePre initial boundary orderAddress)
    {offset len : Nat} {a : BitVec 64} (bound : offset + len ≤ 72)
    (covered : (Component.mem (initial.regValue .rdi + BitVec.ofNat 64 offset) len).Covers a) :
    (registerRegion initial .rdi 72).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show offset + i < 72 by omega)

theorem output_code (pre : InitializePre initial boundary orderAddress) {offset len : Nat}
    (bound : offset + len ≤ 118431) : RangeApart (initial.regValue .rdi) 72
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset + j) (by omega)

theorem stage_of_output_agrees (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) {fuel : Nat} {components : List Component}
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a → (registerRegion initial .rdi 72).Contains a.toNat)
    (rsp : .reg 4 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Stage initial t boundary := by
  obtain ⟨fuel₀, execution⟩ := stage.execution
  refine ⟨stage.toFrameState.after_effect pre.toCalleePre (by decide) ready agrees ?_
    rsp hdf hmxcsr hfcw, fuel₀ + fuel, execution.trans run⟩
  intro c hc a ha
  exact ⟨registerRegion initial .rdi 72, by simp, writes c hc a ha⟩

end P256.Proofs.Nonce.Initialize.Finish
