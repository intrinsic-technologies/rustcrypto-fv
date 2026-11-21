import Sha2.Proofs.Common.SHA256.Finalize.Proof.Frame

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable [Bindings] {L : Layout} {initial s : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n}

theorem Context.below_toNat (ctx : Context L initial regions reserve) {offset : Nat}
    (bound : offset ≤ 344) :
    (L.sp initial - BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - (L.frameBytes + offset) := by
  change (stackPtr initial - BitVec.ofNat 64 L.frameBytes - BitVec.ofNat 64 offset).toNat = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact stack_valid_sub_toNat ctx.stack (by have := ctx.wf.capacity; omega)

theorem Context.callSlot_contains (ctx : Context L initial regions reserve)
    {a : BitVec 64} (covered : (Component.mem (L.sp initial - 8) 8).Covers a) :
    (⟨(L.sp initial - 344).toNat, 344⟩ : MemoryRegion).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := stack_valid_bounds ctx.stack
  have capacity := ctx.wf.capacity
  have sp : (L.sp initial - 8).toNat =
      (stackPtr initial).toNat - (L.frameBytes + 8) := by
    simpa using ctx.below_toNat (by decide : 8 ≤ 344)
  apply memoryRegion_contains_add (len := 8)
  · change (L.sp initial - 344).toNat + 344 < 2^32
    rw [ctx.callStack_toNat]
    omega
  · change (L.sp initial - 344).toNat ≤ (L.sp initial - 8).toNat
    rw [ctx.callStack_toNat, sp]
    omega
  · change (L.sp initial - 8).toNat + 8 ≤ (L.sp initial - 344).toNat + 344
    rw [ctx.callStack_toNat, sp]
    omega
  · exact hi

theorem Context.callWrites (ctx : Context L initial regions reserve)
    (rsp : stackPtr s = L.sp initial) (target : RamState → BitVec 64) (ret : BitVec 64) :
    WritesWithin (callEffect target ret s).components (footprint L (L.sp initial)) := by
  intro c member a covered
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact covered.elim
  · refine ⟨⟨(L.sp initial - 344).toNat, 344⟩, by simp [footprint], ?_⟩
    apply ctx.callSlot_contains
    have address : pushAddr s = L.sp initial - 8 := by
      change stackPtr s - 8 = _
      rw [rsp]
    simpa only [address] using covered
  · exact covered.elim

theorem Context.calleeStack_contains (ctx : Context L initial regions reserve)
    {u : RamState} {calleeReserve a : Nat} (rsp : stackPtr u = L.sp initial - 8)
    (bound : calleeReserve ≤ 336) (contains : (Stack.region u calleeReserve).Contains a) :
    (⟨(L.sp initial - 344).toNat, 344⟩ : MemoryRegion).Contains a := by
  have bounds := stack_valid_bounds ctx.stack
  have capacity := ctx.wf.capacity
  have sp : (L.sp initial - 8).toNat =
      (stackPtr initial).toNat - (L.frameBytes + 8) := by
    simpa using ctx.below_toNat (by decide : 8 ≤ 344)
  change (Stack.region u calleeReserve).start ≤ a ∧
    a < (Stack.region u calleeReserve).start + (Stack.region u calleeReserve).size at contains
  rw [stack_region_end] at contains
  change (stackPtr u).toNat - calleeReserve ≤ a ∧ a < (stackPtr u).toNat + 8 at contains
  rw [rsp, sp] at contains
  change (L.sp initial - 344).toNat ≤ a ∧ a < (L.sp initial - 344).toNat + 344
  rw [ctx.callStack_toNat]
  omega

theorem Context.callWritable (ctx : Context L initial regions reserve)
    (state : ExecutionState initial s regions) (rsp : stackPtr s = L.sp initial) :
    MemWritable s (pushAddr s) 8 := by
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (L.frameBytes + 8) := by
    rw [pushAddr, rsp]
    change stackPtr initial - BitVec.ofNat 64 L.frameBytes - 8 = _
    rw [BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  rw [address]
  exact Common.Encoding.Serialize.writable_of_grow
    (stack_valid_sub_writable ctx.stack (fun a ha hp => ctx.avoids a ha (.inr hp))
      (by have := ctx.wf.capacity; omega) (by omega) (by decide)) state.allocated

theorem Context.callApart (ctx : Context L initial regions reserve)
    (rsp : stackPtr s = L.sp initial) {p : BitVec 64} {size : Nat}
    (inside : BlockInProgram p size) : RangeApart (pushAddr s) 8 p size := by
  intro i hi j hj equal
  have address : pushAddr s = L.sp initial - 8 := by
    rw [pushAddr, rsp]
  have contains := ctx.callSlot_contains (a := pushAddr s + BitVec.ofNat 64 i)
    (by rw [address]; exact ⟨i, hi, rfl⟩)
  apply ctx.avoids (pushAddr s + BitVec.ofNat 64 i)
    (ctx.footprint_subset _ (by simp [footprint]) _ contains)
  exact Or.inl (equal ▸ inside j (Nat.le_of_lt hj))

theorem Context.pushPre (ctx : Context L initial regions reserve)
    (state : ExecutionState initial s regions) (rsp : stackPtr s = L.sp initial)
    {p : BitVec 64} {size : Nat} (rip : s.RIP = p) (inside : BlockInProgram p size) :
    PushPre p size s :=
  ⟨rip, ctx.callWritable state rsp, ctx.callApart rsp inside⟩

end Sha2.Proofs.Common.SHA256.Finalize
