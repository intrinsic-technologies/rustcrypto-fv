import Hkdf.Proofs.NewExpand.Extract.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Initialize.Pads

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev slot (initial : RamState) (offset : Nat) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 offset

abbrev slotRegion (initial : RamState) (offset size : Nat) : MemoryRegion :=
  ⟨(slot initial offset).toNat, size⟩

theorem slot_add (initial : RamState) {offset delta : Nat} (bound : delta ≤ offset) :
    slot initial offset + BitVec.ofNat 64 delta = slot initial (offset - delta) := by
  have h := congrArg (BitVec.ofNat 64) (Nat.sub_add_cancel bound)
  rw [BitVec.ofNat_add] at h
  dsimp only [slot]
  bv_omega

theorem base_add (initial : RamState) {offset : Nat} (bound : offset ≤ 456) :
    base initial + BitVec.ofNat 64 offset = slot initial (456 - offset) :=
  slot_add initial bound

theorem slotRegion_within {initial : RamState} (stack : Stack.Valid initial 2264)
    {offset size a : Nat} (low : offset ≤ 2264) (high : size ≤ offset + 8)
    (inside : (slotRegion initial offset size).Contains a) :
    (Stack.region initial 2264).Contains a := by
  change (slot initial offset).toNat ≤ a ∧ a < (slot initial offset).toNat + size at inside
  rw [CallFrame.stack_sub_toNat stack low] at inside
  have bounds := CallFrame.stack_bounds stack
  change (stackPtr initial).toNat - 2264 ≤ a ∧ a < _
  rw [stack_region_end]
  omega

theorem slotRegion_disjoint {initial : RamState} (stack : Stack.Valid initial 2264)
    {offset size other width : Nat} (low : offset ≤ 2264) (otherLow : other ≤ 2264)
    (apart : offset + width ≤ other ∨ other + size ≤ offset) :
    (slotRegion initial offset size).Disjoint (slotRegion initial other width) := by
  intro a ha hb
  change (slot initial offset).toNat ≤ a ∧ a < (slot initial offset).toNat + size at ha
  change (slot initial other).toNat ≤ a ∧ a < (slot initial other).toNat + width at hb
  rw [CallFrame.stack_sub_toNat stack low] at ha
  rw [CallFrame.stack_sub_toNat stack otherLow] at hb
  have bounds := (CallFrame.stack_bounds stack).1
  rcases apart with h | h <;> omega

theorem slotBound {initial : RamState} (stack : Stack.Valid initial 2264)
    {offset size : Nat} (low : offset ≤ 2264) (high : size ≤ offset + 8) :
    (slot initial offset).toNat + size ≤ 2^64 := by
  rw [CallFrame.stack_sub_toNat stack low]
  have bounds := CallFrame.stack_bounds stack
  omega

theorem slot_agrees {initial s t : RamState} {n offset size : Nat}
    {regions : Vector MemoryRegion n} (stack : Stack.Valid initial 2264)
    (footprint : MemoryWriteFrame s t regions)
    (low : offset ≤ 2264) (high : size ≤ offset + 8)
    (apart : ∀ r ∈ regions, (slotRegion initial offset size).Disjoint r) :
    (Component.mem (slot initial offset) size).Agrees s t :=
  frame_agrees_of_disjoint footprint (slotBound stack low high) apart

theorem slot_writesWithin {initial : RamState} {offset size : Nat}
    (stack : Stack.Valid initial 2264) (low : offset ≤ 2264) (high : size ≤ offset)
    {a : BitVec 64} (cover : (Component.mem (slot initial offset) size).Covers a) :
    ∃ r ∈ #v[Stack.region initial 2264], r.Contains a.toNat :=
  ⟨_, by simp, stackRegion_contains_sub stack.2.2.1 low high cover⟩

theorem stack_avoids [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm) :
    ∀ r ∈ #v[Stack.region initial 2264], r.Avoids InProgram := by
  intro r hr a ha h
  have same : r = Stack.region initial 2264 := by simpa using hr
  subst r
  exact pre.call.stackAvoid a ha (.inl h)

end Hkdf.Proofs.NewExpand.Extract.Initialize.Pads
