import Sha2.Proofs.Common.Encoding.Serialize.Stack
import Sha2.Proofs.Common.Machine.StackRegion
import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Common.Machine.Relocatable

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_frame_address (initial : RamState) {frame offset : Nat} (bound : offset ≤ frame) :
    stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (frame - offset) := by
  have split : frame = (frame - offset) + offset := by omega
  rw [split, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel, Nat.add_sub_cancel]

theorem stack_frame_toNat {initial : RamState} {reserve frame offset : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve) (bound : offset ≤ frame) :
    (stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - frame + offset := by
  rw [stack_frame_address initial bound, stack_valid_sub_toNat stack (by omega)]
  have bounds := stack_valid_bounds stack
  omega

theorem stack_frame_readable {initial s : RamState} {reserve frame offset len : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (bound : offset + len ≤ frame) :
    MemReadable s (stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset) len := by
  rw [stack_frame_address initial (by omega)]
  exact Common.Encoding.Serialize.readable_of_grow
    (stack_valid_sub_readable stack (by omega) (by omega)) grow

theorem stack_frame_writable {initial s : RamState} {reserve frame offset len : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve)
    (avoids : (Stack.region initial reserve).Avoids InPageTables)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (bound : offset + len ≤ frame) (positive : 0 < len) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset) len := by
  rw [stack_frame_address initial (by omega)]
  exact Common.Encoding.Serialize.writable_of_grow
    (stack_valid_sub_writable stack avoids (by omega) (by omega) positive) grow

theorem stack_frame_contains {initial : RamState} {reserve frame offset len : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve)
    (bound : offset + len ≤ frame) {a : BitVec 64}
    (covered : (Component.mem
      (stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset) len).Covers a) :
    (Stack.region initial reserve).Contains a.toNat := by
  rw [stack_frame_address initial (by omega)] at covered
  exact stackRegion_contains_sub stack.2.2.1 (by omega) (by omega) covered

theorem stack_frame_codeApart {initial : RamState} {reserve frame offset len size : Nat}
    {p : BitVec 64} (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve)
    (avoids : (Stack.region initial reserve).Avoids InProgram)
    (bound : offset + len ≤ frame)
    (inside : ∀ j < size, InProgram (p + BitVec.ofNat 64 j)) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset) len p size := by
  intro i hi j hj he
  apply avoids _ (stack_frame_contains stack capacity bound ⟨i, hi, rfl⟩)
  exact he ▸ inside j hj

theorem stack_sub_region_subset {initial : RamState} {reserve offset len : Nat}
    (stack : Stack.Valid initial reserve) (bound : offset ≤ reserve) (size : len ≤ offset + 8)
    {a : Nat} (member : (⟨(stackPtr initial - BitVec.ofNat 64 offset).toNat, len⟩ :
      MemoryRegion).Contains a) : (Stack.region initial reserve).Contains a := by
  change _ ≤ a ∧ a < _ at member
  rw [stack_valid_sub_toNat stack bound] at member
  have bounds := stack_valid_bounds stack
  dsimp only at member
  change (stackPtr initial).toNat - reserve ≤ a ∧
    a < (stackPtr initial).toNat - reserve +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - reserve))
  omega

theorem stack_frame_region_subset {initial : RamState} {reserve frame offset len : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve)
    (bound : offset + len ≤ frame) {a : Nat}
    (member : (⟨(stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset).toNat,
      len⟩ : MemoryRegion).Contains a) : (Stack.region initial reserve).Contains a := by
  rw [stack_frame_address initial (by omega)] at member
  exact stack_sub_region_subset stack (by omega) (by omega) member

theorem stack_frame_bounded {initial : RamState} {reserve frame offset len : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve)
    (bound : offset + len ≤ frame) :
    (⟨(stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset).toNat, len⟩ :
      MemoryRegion).Bounded := by
  change _ + len < 2^32
  rw [stack_frame_toNat stack capacity (by omega)]
  dsimp only
  have bounds := stack_valid_bounds stack
  omega

theorem stack_frame_cover {initial : RamState} {reserve frame base size offset len : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve)
    (bound : base + size ≤ frame) (endBound : offset + len ≤ size) {a : BitVec 64}
    (covered : (Component.mem
      (stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 (base + offset)) len).Covers a) :
    (⟨(stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 base).toNat,
      size⟩ : MemoryRegion).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have address : stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 (base + offset) +
      BitVec.ofNat 64 i = stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 base +
      BitVec.ofNat 64 (offset + i) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  rw [address]
  exact memoryRegion_contains_add (stack_frame_bounded stack capacity bound)
    (Nat.le_refl _) (Nat.le_refl _) (by change offset + i < size; omega)

theorem stack_frame_below_toNat {initial : RamState} {reserve frame below : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame + below ≤ reserve) :
    (stackPtr initial - BitVec.ofNat 64 frame - BitVec.ofNat 64 below).toNat =
      (stackPtr initial).toNat - (frame + below) := by
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact stack_valid_sub_toNat stack capacity

theorem call_slot_contains {initial : RamState} {reserve frame : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame + 344 ≤ reserve)
    {a : BitVec 64}
    (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 frame - 8) 8).Covers a) :
    (⟨(stackPtr initial - BitVec.ofNat 64 frame - 344).toNat, 344⟩ :
      MemoryRegion).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := stack_valid_bounds stack
  have h344 : (stackPtr initial - BitVec.ofNat 64 frame - 344).toNat =
      (stackPtr initial).toNat - (frame + 344) := by
    simpa only [BitVec.ofNat_eq_ofNat] using stack_frame_below_toNat stack capacity
  have h8 : (stackPtr initial - BitVec.ofNat 64 frame - 8).toNat =
      (stackPtr initial).toNat - (frame + 8) := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      stack_frame_below_toNat stack (frame := frame) (below := 8) (by omega)
  apply memoryRegion_contains_add (len := 8)
  · change (stackPtr initial - BitVec.ofNat 64 frame - 344).toNat + 344 < 2^32
    rw [h344]
    omega
  · change (stackPtr initial - BitVec.ofNat 64 frame - 344).toNat ≤ (stackPtr initial - BitVec.ofNat 64 frame - 8).toNat
    rw [h344, h8]
    omega
  · change (stackPtr initial - BitVec.ofNat 64 frame - 8).toNat + 8 ≤ (stackPtr initial - BitVec.ofNat 64 frame - 344).toNat + 344
    rw [h344, h8]
    omega
  · exact hi

theorem callee_stack_contains {initial u : RamState} {reserve frame calleeReserve a : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame + 344 ≤ reserve)
    (rsp : stackPtr u = stackPtr initial - BitVec.ofNat 64 frame - 8)
    (bound : calleeReserve ≤ 336) (contains : (Stack.region u calleeReserve).Contains a) :
    (⟨(stackPtr initial - BitVec.ofNat 64 frame - 344).toNat, 344⟩ :
      MemoryRegion).Contains a := by
  have bounds := stack_valid_bounds stack
  have h344 : (stackPtr initial - BitVec.ofNat 64 frame - 344).toNat =
      (stackPtr initial).toNat - (frame + 344) := by
    simpa only [BitVec.ofNat_eq_ofNat] using stack_frame_below_toNat stack capacity
  have h8 : (stackPtr initial - BitVec.ofNat 64 frame - 8).toNat =
      (stackPtr initial).toNat - (frame + 8) := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      stack_frame_below_toNat stack (frame := frame) (below := 8) (by omega)
  change (Stack.region u calleeReserve).start ≤ a ∧
    a < (Stack.region u calleeReserve).start + (Stack.region u calleeReserve).size at contains
  rw [stack_region_end] at contains
  change (stackPtr u).toNat - calleeReserve ≤ a ∧ a < (stackPtr u).toNat + 8 at contains
  rw [rsp, h8] at contains
  change (stackPtr initial - BitVec.ofNat 64 frame - 344).toNat ≤ a ∧
    a < (stackPtr initial - BitVec.ofNat 64 frame - 344).toNat + 344
  rw [h344]
  omega

theorem stack_frame_below_saved {initial : RamState} {reserve frame offset len allocation : Nat}
    (stack : Stack.Valid initial reserve) (capacity : frame ≤ reserve)
    (bound : offset + len ≤ allocation) (fits : allocation ≤ frame) {a : BitVec 64}
    (covered : (Component.mem
      (stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 offset) len).Covers a) :
    a.toNat < (stackPtr initial).toNat - (frame - allocation) := by
  obtain ⟨i, hi, rfl⟩ := covered
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    stack_frame_toNat stack capacity (by omega)]
  have bounds := stack_valid_bounds stack
  omega

end Sha2.Proofs.Common.Machine
