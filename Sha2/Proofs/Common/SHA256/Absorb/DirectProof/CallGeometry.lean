import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Geometry

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable [Bindings] {l : Layout} {initial s : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n}

theorem Context.callSlot_contains (ctx : Context l initial regions reserve)
    {a : BitVec 64} (covered : (Component.mem (l.sp initial - 8) 8).Covers a) :
    (⟨(l.sp initial - 344).toNat, 344⟩ : MemoryRegion).Contains a.toNat := by
  exact call_slot_contains ctx.stack ctx.wf.capacity covered

theorem Context.callWrites (ctx : Context l initial regions reserve)
    (rsp : stackPtr s = l.sp initial) (target : RamState → BitVec 64) (ret : BitVec 64) :
    WritesWithin (callEffect target ret s).components (footprint l (l.sp initial)) := by
  intro c member a covered
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact covered.elim
  · refine ⟨⟨(l.sp initial - 344).toNat, 344⟩, by simp [footprint], ?_⟩
    apply ctx.callSlot_contains
    have address : pushAddr s = l.sp initial - 8 := by
      change stackPtr s - 8 = _
      rw [rsp]
    simpa only [address] using covered
  · exact covered.elim

theorem Context.calleeStack_contains (ctx : Context l initial regions reserve)
    {u : RamState} {calleeReserve a : Nat} (rsp : stackPtr u = l.sp initial - 8)
    (bound : calleeReserve ≤ 336) (contains : (Stack.region u calleeReserve).Contains a) :
    (⟨(l.sp initial - 344).toNat, 344⟩ : MemoryRegion).Contains a := by
  exact callee_stack_contains ctx.stack ctx.wf.capacity rsp bound contains

theorem Context.callWritable (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) (rsp : stackPtr s = l.sp initial) :
    MemWritable s (pushAddr s) 8 := by
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (l.frameBytes + 8) := by
    rw [pushAddr, rsp]
    change stackPtr initial - BitVec.ofNat 64 l.frameBytes - 8 = _
    rw [BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  rw [address]
  exact Common.Encoding.Serialize.writable_of_grow
    (stack_valid_sub_writable ctx.stack (fun a ha hp => ctx.avoids a ha (.inr hp))
      (by have := ctx.wf.capacity; omega) (by omega) (by decide)) state.allocated

theorem Context.callApart (ctx : Context l initial regions reserve)
    (rsp : stackPtr s = l.sp initial) {p : BitVec 64} {size : Nat}
    (inside : ∀ i < size, InProgram (p + BitVec.ofNat 64 i)) : RangeApart (pushAddr s) 8 p size := by
  intro i hi j hj equal
  have address : pushAddr s = l.sp initial - 8 := by
    rw [pushAddr, rsp]
  have contains := ctx.callSlot_contains (a := pushAddr s + BitVec.ofNat 64 i)
    (by rw [address]; exact ⟨i, hi, rfl⟩)
  apply ctx.avoids (pushAddr s + BitVec.ofNat 64 i)
    (ctx.footprint_subset _ (by simp [footprint]) _ contains)
  exact Or.inl (equal ▸ inside j hj)

theorem Context.pushPre (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) (rsp : stackPtr s = l.sp initial)
    {p : BitVec 64} {size : Nat} (rip : s.RIP = p) (inside : ∀ i < size, InProgram (p + BitVec.ofNat 64 i)) :
    PushPre p size s :=
  ⟨rip, ctx.callWritable state rsp, ctx.callApart rsp inside⟩

end Sha2.Proofs.Common.SHA256.Absorb.Direct
