import P256.Proofs.Verifying.Combination.Table.Memory

set_option autoImplicit false

open P256.Proofs.Program (CalleePre memoryRegion_memReadable stack_region_end)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev Source := Option Slot

def sourceAddress (s : RamState) (point : BitVec 64) : Source → BitVec 64
  | none => point
  | some slot => stackPtr s - BitVec.ofNat 64 (offset slot)

theorem source_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {so : BitVec 64} (pre : TablePre s boundary cursor point) (state : FrameState s t cursor so)
    (src : Source) : MemReadable t (sourceAddress s point src) 96 := by
  apply P256.Proofs.Program.readable_of_grow _ state.allocated
  cases src with
  | none =>
    exact memoryRegion_memReadable pre.pointBounded pre.pointAllocated (Nat.le_refl _) (Nat.le_refl _)
  | some slot =>
    have hb := offset_bounds slot
    exact P256.Proofs.Program.stack_sub_readable pre.stack (by omega) (by omega)

theorem source_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    (pre : TablePre s boundary cursor point) (src : Source) (slot : Slot)
    (ne : src ≠ some slot) :
    (sourceAddress s point src).toNat + 96 ≤
        (stackPtr s - BitVec.ofNat 64 (offset slot)).toNat ∨
      (stackPtr s - BitVec.ofNat 64 (offset slot)).toNat + 96 ≤
        (sourceAddress s point src).toNat := by
  have hd := offset_bounds slot
  have hs := P256.Proofs.Program.stack_bounds pre.stack
  rw [P256.Proofs.Program.stack_sub_toNat pre.stack (by omega)]
  cases src with
  | some src =>
    have hin := offset_bounds src
    have ha := offset_apart (show src ≠ slot from fun he => ne (congrArg some he))
    change (stackPtr s - BitVec.ofNat 64 (offset src)).toNat + 96 ≤ _ ∨
      _ ≤ (stackPtr s - BitVec.ofNat 64 (offset src)).toNat
    rw [P256.Proofs.Program.stack_sub_toNat pre.stack (by omega)]
    omega
  | none =>
    change (point).toNat + 96 ≤ _ ∨ _ ≤ (point).toNat
    apply Classical.byContradiction
    intro h
    have notapart : (point).toNat < (stackPtr s).toNat - offset slot + 96 ∧
        (stackPtr s).toNat - offset slot < (point).toNat + 96 := by omega
    apply pre.pointStack
      (max (point).toNat ((stackPtr s).toNat - offset slot))
    · change (point).toNat ≤ _ ∧ _ < (point).toNat + 96
      constructor <;> omega
    · change (stackPtr s).toNat - 2120 ≤ _ ∧ _ < (Stack.region s 2120).start + (Stack.region s 2120).size
      rw [stack_region_end]
      constructor <;> omega

end P256.Proofs.Verifying.Combination.Table
