import Sha2.Proofs.Common.SHA256.Finalize.Proof.Context
import Sha2.Proofs.Common.Machine.FrameMemory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable [Bindings] {L : Layout} {initial s : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n}

omit [Bindings] in
theorem Layout.address (L : Layout) (initial : RamState) {offset : Nat}
    (bound : offset ≤ L.frameBytes) :
    L.sp initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (L.frameBytes - offset) := by
  exact stack_frame_address initial bound

theorem Context.address_toNat (ctx : Context L initial regions reserve) {offset : Nat}
    (bound : offset ≤ L.frameBytes) :
    (L.sp initial + BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - L.frameBytes + offset := by
  exact stack_frame_toNat ctx.stack (by have := ctx.wf.capacity; omega) bound

theorem Context.sp_toNat (ctx : Context L initial regions reserve) :
    (L.sp initial).toNat = (stackPtr initial).toNat - L.frameBytes :=
  stack_valid_sub_toNat ctx.stack (by have := ctx.wf.capacity; omega)

theorem Context.callStack_toNat (ctx : Context L initial regions reserve) :
    (L.sp initial - 344).toNat = (stackPtr initial).toNat - (L.frameBytes + 344) := by
  change (stackPtr initial - BitVec.ofNat 64 L.frameBytes - BitVec.ofNat 64 344).toNat = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact stack_valid_sub_toNat ctx.stack ctx.wf.capacity

theorem Context.readable (ctx : Context L initial regions reserve)
    (state : ExecutionState initial s regions) {offset len : Nat}
    (bound : offset + len ≤ L.frameBytes) :
    MemReadable s (L.sp initial + BitVec.ofNat 64 offset) len := by
  exact stack_frame_readable ctx.stack (by have := ctx.wf.capacity; omega)
    state.allocated bound

theorem Context.writable (ctx : Context L initial regions reserve)
    (state : ExecutionState initial s regions) {offset len : Nat}
    (bound : offset + len ≤ L.frameBytes) (positive : 0 < len) :
    MemWritable s (L.sp initial + BitVec.ofNat 64 offset) len := by
  exact stack_frame_writable ctx.stack (by have := ctx.wf.capacity; omega)
    (fun a ha hp => ctx.avoids a ha (.inr hp)) state.allocated bound positive

theorem Context.local_contains (ctx : Context L initial regions reserve)
    {offset len : Nat} (bound : offset + len ≤ L.frameBytes)
    {a : BitVec 64} (covered : (Component.mem (L.sp initial + BitVec.ofNat 64 offset) len).Covers a) :
    (Stack.region initial reserve).Contains a.toNat := by
  exact stack_frame_contains ctx.stack (by have := ctx.wf.capacity; omega) bound covered

theorem Context.codeApart (ctx : Context L initial regions reserve)
    {offset len size : Nat} {p : BitVec 64} (bound : offset + len ≤ L.frameBytes)
    (inside : BlockInProgram p size) :
    RangeApart (L.sp initial + BitVec.ofNat 64 offset) len p size := by
  exact stack_frame_codeApart ctx.stack (by have := ctx.wf.capacity; omega)
    (fun a ha hp => ctx.avoids a ha (.inl hp)) bound
    (fun j hj => inside j (Nat.le_of_lt hj))

omit [Bindings] in
theorem footprint_subset_stack (wf : WellFormed L reserve) (stack : Stack.Valid initial reserve) :
    ∀ region ∈ footprint L (L.sp initial), ∀ a, region.Contains a →
      (Stack.region initial reserve).Contains a := by
  have capacity : L.frameBytes ≤ reserve := by have := wf.capacity; omega
  intro region member a ha
  simp only [footprint, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact stack_frame_region_subset stack capacity
      (by have := wf.bufferFits; omega) ha
  · have address : L.hash (L.sp initial) =
        L.sp initial + BitVec.ofNat 64 (L.variant.buffer.value + 64) := by
      simp only [Layout.hash, Layout.buffer, BitVec.ofNat_add, BitVec.add_assoc,
        BitVec.ofNat_eq_ofNat]
    rw [address] at ha
    exact stack_frame_region_subset stack capacity
      (by have := wf.bufferFits; omega) ha
  · exact stack_frame_region_subset stack capacity wf.scratchFits ha
  · have address : L.sp initial - 344 =
        stackPtr initial - BitVec.ofNat 64 (L.frameBytes + 344) := by
      simp only [Layout.sp, BitVec.ofNat_add, BitVec.sub_sub, BitVec.ofNat_eq_ofNat]
    rw [address] at ha
    exact stack_sub_region_subset stack wf.capacity (by omega) ha

theorem Context.footprint_subset (ctx : Context L initial regions reserve) :
    ∀ region ∈ footprint L (L.sp initial), ∀ a, region.Contains a →
      (Stack.region initial reserve).Contains a :=
  footprint_subset_stack ctx.wf ctx.stack

theorem Context.footprint_avoids (ctx : Context L initial regions reserve) :
    ∀ region ∈ footprint L (L.sp initial), region.Avoids InProgram := by
  intro region member a contains program
  exact ctx.avoids a (ctx.footprint_subset region member a.toNat contains) (.inl program)

theorem Context.local_bounded (ctx : Context L initial regions reserve) {offset len : Nat}
    (bound : offset + len ≤ L.frameBytes) :
    (⟨(L.sp initial + BitVec.ofNat 64 offset).toNat, len⟩ : MemoryRegion).Bounded := by
  exact stack_frame_bounded ctx.stack (by have := ctx.wf.capacity; omega) bound

theorem Context.local_cover (ctx : Context L initial regions reserve)
    {base size offset len : Nat} (bound : base + size ≤ L.frameBytes)
    (endBound : offset + len ≤ size) {a : BitVec 64}
    (covered : (Component.mem (L.sp initial + BitVec.ofNat 64 (base + offset)) len).Covers a) :
    (⟨(L.sp initial + BitVec.ofNat 64 base).toNat, size⟩ : MemoryRegion).Contains a.toNat := by
  exact stack_frame_cover ctx.stack (by have := ctx.wf.capacity; omega) bound endBound covered

end Sha2.Proofs.Common.SHA256.Finalize
