import P256.Proofs.Signing.Wrapper.Interface
import P256.Proofs.Program.Stack
import P256.Proofs.Program.State
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

structure State [bindings : Bindings] (initial s : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  loaded : ProgramLoaded s
  directionFlag : DirectionFlagUnset s
  rsp : stackPtr s = stackPtr initial - 520
  output : memLoad s.external (stackPtr initial - 208) 64 = initial.regValue .rcx
  capacity : memLoad s.external (stackPtr initial - 200) 64 = initial.regValue .r8
  savedRbx : memLoad s.external (stackPtr initial - 48) 64 = initial.regValue .rbx
  savedR12 : memLoad s.external (stackPtr initial - 40) 64 = initial.regValue .r12
  savedR13 : memLoad s.external (stackPtr initial - 32) 64 = initial.regValue .r13
  savedR14 : memLoad s.external (stackPtr initial - 24) 64 = initial.regValue .r14
  savedR15 : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .r15
  savedRbp : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .rbp
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  rbp : s.regValue .rbp = 0
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome

structure Pre (initial : RamState) : Prop where
  stack : Stack.Valid initial 5112
  outputBounded : (registerRegion initial .rcx 72).Bounded
  outputAllocated : (registerRegion initial .rcx 72).Allocated initial.external
  separated : (registerRegion initial .rcx 72).Disjoint (Stack.region initial 5112)
  avoids : ∀ r ∈ [registerRegion initial .rcx 72, Stack.region initial 5112],
    r.Avoids (fun a => InProgram a ∨ InPageTables a)
  outside : ¬ InProgram (returnBoundary initial).rip
  capacity : 72 ≤ (initial.regValue .r8).toNat

theorem stack_address {initial t : RamState} (rsp : stackPtr t = stackPtr initial - 520)
    {off : Nat} (ho : off ≤ 520) :
    stackPtr t + BitVec.ofNat 64 off = stackPtr initial - BitVec.ofNat 64 (520-off) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 520 off (by omega) ho, rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem stack_contains {initial : RamState} (pre : Pre initial) {off len : Nat} {a : BitVec 64}
    (ho : off ≤ 5112) (hl : len ≤ off + 8)
    (ha : (Component.mem (stackPtr initial - BitVec.ofNat 64 off) len).Covers a) :
    (Stack.region initial 5112).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := ha
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat pre.stack ho]
    change (stackPtr initial).toNat - 5112 ≤ (stackPtr initial).toNat - off
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack ho]
    have := stack_bounds pre.stack
    omega

theorem frame_read_saved {initial t u : RamState} (pre : Pre initial)
    (frame : MemoryWriteFrame t u #v[registerRegion initial .rcx 72])
    {off : Nat} (ho : off ≤ 520) :
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
    (state : State initial t) {off len : Nat} (bound : off + len ≤ 472) :
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

end P256.Proofs.Signing.Wrapper.Finish
