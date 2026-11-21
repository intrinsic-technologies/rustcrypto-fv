import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.State
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success

open P256.Proofs.SignatureFromSlice.Wrapper.Epilogue

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

structure Pre (initial : RamState) : Prop where
  stack : Stack.Valid initial 656
  outputBounded : (registerRegion initial .rcx 72).Bounded
  outputAllocated : (registerRegion initial .rcx 72).Allocated initial.external
  separated : (registerRegion initial .rcx 72).Disjoint (Stack.region initial 656)
  avoids : ∀ r ∈ [registerRegion initial .rcx 72, Stack.region initial 656],
    r.Avoids (fun a => InProgram a ∨ InPageTables a)
  outside : ¬ InProgram (returnBoundary initial).rip
  capacity : 72 ≤ (initial.regValue .r8).toNat

theorem stack_address {initial t : RamState} (rsp : stackPtr t = stackPtr initial - 88)
    {off : Nat} (ho : off ≤ 88) :
    stackPtr t + BitVec.ofNat 64 off = stackPtr initial - BitVec.ofNat 64 (88-off) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 88 off (by omega) ho, rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem stack_contains {initial : RamState} (pre : Pre initial) {off len : Nat} {a : BitVec 64}
    (ho : off ≤ 656) (hl : len ≤ off + 8)
    (ha : (Component.mem (stackPtr initial - BitVec.ofNat 64 off) len).Covers a) :
    (Stack.region initial 656).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := ha
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat pre.stack ho]
    change (stackPtr initial).toNat - 656 ≤ (stackPtr initial).toNat - off
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack ho]
    have := stack_bounds pre.stack
    omega

theorem frame_read_saved {initial t u : RamState} (pre : Pre initial)
    (frame : MemoryWriteFrame t u #v[registerRegion initial .rcx 72])
    {off : Nat} (ho : off ≤ 16) :
    memLoad u.external (stackPtr initial - BitVec.ofNat 64 off) 64 =
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 off) 64 := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr initial - BitVec.ofNat 64 off + BitVec.ofNat 64 i]?).getD 0 = _
  rw [frame _]
  · rfl
  intro r hr ha
  have hr' : r = registerRegion initial .rcx 72 := by simpa using hr
  subst r
  exact pre.separated _ ha (stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩)

theorem after [Bindings] {initial t u : RamState} {cs : List Component}
    (pre : Pre initial) (state : State initial t) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion initial .rcx 72])
    (registers : ∀ r ∈ [4,14,3,5,12,13,15], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : State initial u := by
  have frame := agrees.memoryWriteFrame writes
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear df state.directionFlag,
    (agrees.read (n := 64) (registers 4 (by simp))).trans state.rsp,
    (agrees.read (n := 64) (registers 3 (by simp))).trans state.output,
    (agrees.read (n := 64) (registers 14 (by simp))).trans state.capacity,
    (frame_read_saved pre frame (off := 16) (by decide)).trans state.savedRbx,
    (frame_read_saved pre frame (off := 8) (by decide)).trans state.savedR14,
    ?_, ?_, fun a ha => agrees.grow a (state.allocated a ha)⟩
  · intro a b hf
    rw [frame a]
    · exact state.loaded a b hf
    · intro r hr ha
      have hr' : r = registerRegion initial .rcx 72 := by simpa using hr
      subst r
      exact pre.avoids _ (by simp) a ha (.inl ⟨b,hf⟩)
  · have h := frame_read_saved pre frame (off := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (agrees.read (n := 64) (registers 5 (by simp))).trans (state.otherRegisters .rbp (by simp))
    · exact (agrees.read (n := 64) (registers 12 (by simp))).trans (state.otherRegisters .r12 (by simp))
    · exact (agrees.read (n := 64) (registers 13 (by simp))).trans (state.otherRegisters .r13 (by simp))
    · exact (agrees.read (n := 64) (registers 15 (by simp))).trans (state.otherRegisters .r15 (by simp))

theorem output_writable [Bindings] {initial t : RamState} (pre : Pre initial)
    (state : State initial t) : CrossPageStore.Writable t (initial.regValue .rcx) 72 := by
  have hr := readable_of_grow
    (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _))
    state.allocated
  refine ⟨hr, tables_of_not_reserved (by decide) hr.low ?_⟩
  intro i hi hp
  exact pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hp)

theorem output_code {initial : RamState} (pre : Pre initial) {offset len : Nat}
    (bound : offset + len ≤ 118431) : RangeApart (initial.regValue .rcx) 72
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset + j) (by omega)

theorem stack_readable [Bindings] {initial t : RamState} (pre : Pre initial)
    (state : State initial t) {off len : Nat} (bound : off + len ≤ 72) :
    MemReadable t (stackPtr t + BitVec.ofNat 64 off) len := by
  rw [stack_address state.rsp (by omega)]
  exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated

theorem output_contains {initial : RamState} (pre : Pre initial) {off len : Nat} {a : BitVec 64}
    (bound : off + len ≤ 72)
    (ha : (Component.mem (initial.regValue .rcx + BitVec.ofNat 64 off) len).Covers a) :
    (registerRegion initial .rcx 72).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := ha
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show off + i < 72 by omega)

end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success
