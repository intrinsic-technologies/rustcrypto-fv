import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Footprint
import Hkdf.Proofs.NewExpand.Expand.LoopState
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Footprint

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem localSlot {s t : RamState} {k off : Nat} {regions : Vector MemoryRegion k}
    (frame : MemoryWriteFrame s t regions) (sp : stackPtr t = stackPtr s)
    (bounded : (stackPtr s).toNat + 544 < 2^32) (fit : off + 8 ≤ 544)
    (apart : ∀ r ∈ regions, r.start + r.size ≤ (stackPtr s).toNat + off ∨
      (stackPtr s).toNat + off + 8 ≤ r.start) : slot t (BitVec.ofNat 64 off) = slot s (BitVec.ofNat 64 off) := by
  change memLoad t.external (stackPtr t + _) 64 = _
  rw [sp]
  apply agrees_memLoad
  apply frame_agrees_of_disjoint frame
  · rw [Info.offset_toNat bounded (by omega)]
    omega
  · intro r hr a ha write
    change (stackPtr s + BitVec.ofNat 64 off).toNat ≤ a ∧ a < (stackPtr s + BitVec.ofNat 64 off).toNat + 8 at ha
    rw [Info.offset_toNat bounded (by omega)] at ha
    have := apart r hr
    have low := write.1
    have high := write.2
    omega

theorem stackFrameOfLocal [Bindings] {entry s t : RamState} {boundary : ReturnBoundary} {length k : Nat}
    {regions : Vector MemoryRegion k} (stack : Stack.Valid entry 2264)
    (saved : SavedFrame entry s boundary length) (frame : MemoryWriteFrame s t regions)
    (within : ∀ r ∈ regions, (stackPtr s).toNat - 344 ≤ r.start ∧
      r.start + r.size ≤ (stackPtr s).toNat + 536) : MemoryWriteFrame s t #v[Stack.region entry 2264] := by
  have sp : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [show stackPtr s = stackPtr entry - 536 from saved.sp]
    apply stack_sub_toNat stack (offset := 536) (by decide)
  have cap := (stack_bounds stack).1
  apply frame_mono frame
  intro r hr a ha
  have bounds := within r hr
  have low := ha.1
  have high := ha.2
  refine ⟨_, Vector.mem_singleton_self _, ?_⟩
  change (Stack.region entry 2264).start ≤ a ∧ a < (Stack.region entry 2264).start + (Stack.region entry 2264).size
  rw [stack_region_end]
  change (stackPtr entry).toNat - 2264 ≤ a ∧ a < (stackPtr entry).toNat + 8
  rw [sp] at bounds
  exact ⟨Nat.le_trans (by omega) (Nat.le_trans bounds.1 low),
    Nat.lt_of_lt_of_le high (Nat.le_trans bounds.2 (by omega))⟩

theorem LoopState.outputOfStack [Bindings] {entry s t : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (head : LoopState entry s boundary key info length n)
    (pre : ExpandPre entry boundary key info ptr length) (more : 32 * n < length) (limit : length ≤ 8160)
    (frame : MemoryWriteFrame s t #v[Stack.region entry 2264]) :
    (registerRegion entry .rcx (min (32*n) length)).HasBytes t.external
      ((blocks .sha256 key info n).1.extract 0 length) := by
  have apart := (pre.separation (by omega) limit).1 0 1 (by decide)
  have bounds := (pre.output (by omega) limit).1
  change (entry.regValue .rcx).toNat + length < 2^32 at bounds
  apply frame_hasBytes frame _ _ head.output
  · intro r hr a ha
    obtain rfl := Vector.mem_singleton.mp hr
    apply apart a
    change (entry.regValue .rcx).toNat ≤ a ∧ a < (entry.regValue .rcx).toNat + length
    change (entry.regValue .rcx).toNat ≤ a ∧ a < (entry.regValue .rcx).toNat + min (32*n) length at ha
    omega
  · change (entry.regValue .rcx).toNat + min (32*n) length ≤ 2^64
    omega

theorem infoFrame [Bindings] {entry s t : RamState} {boundary : ReturnBoundary} {length : Nat}
    (stack : Stack.Valid entry 2264) (saved : SavedFrame entry s boundary length)
    (afterInfo : SavedFrame entry t boundary length) (writes : MemoryWriteFrame s t (Info.regions (stackPtr s))) :
    MemoryWriteFrame s t #v[Stack.region entry 2264] ∧
    ∀ off ∈ ([8,232,240,248,256,264,416,424,440] : List Nat),
      slot t (BitVec.ofNat 64 off) = slot s (BitVec.ofNat 64 off) := by
  have bounds := Info.workBounds stack saved
  have sp : stackPtr t = stackPtr s := afterInfo.sp.trans saved.sp.symm
  have options (r : MemoryRegion) (hr : r ∈ Info.regions (stackPtr s)) :
      r = ⟨(stackPtr s).toNat + 272,104⟩ ∨ r = ⟨(stackPtr s).toNat - 344,344⟩ ∨
      r = ⟨(stackPtr s).toNat + 432,8⟩ := by
    have lo : (stackPtr s + 272).toNat = (stackPtr s).toNat + 272 := Info.offset_toNat (offset := 272) bounds.2 (by decide)
    have hi : (stackPtr s + 432).toNat = (stackPtr s).toNat + 432 := Info.offset_toNat (offset := 432) bounds.2 (by decide)
    simpa only [Info.regions, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false, lo, hi] using hr
  constructor
  · apply stackFrameOfLocal stack saved writes
    intro r hr
    rcases options r hr with rfl | rfl | rfl <;> dsimp <;> omega
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    apply localSlot writes sp bounds.2 (by omega)
    intro r hr
    rcases options r hr with rfl | rfl | rfl <;> dsimp <;> omega

theorem counterFrame [Bindings] {entry s t : RamState} {boundary : ReturnBoundary} {length : Nat}
    (stack : Stack.Valid entry 2264) (saved : SavedFrame entry s boundary length)
    (afterCounter : SavedFrame entry t boundary length) (writes : MemoryWriteFrame s t (Counter.writes entry)) :
    MemoryWriteFrame s t #v[Stack.region entry 2264] ∧
    ∀ off ∈ ([232,240,248,256,264,416,424,432,440] : List Nat),
      slot t (BitVec.ofNat 64 off) = slot s (BitVec.ofNat 64 off) := by
  constructor
  · apply stackFrameOfLocal stack saved writes
    have sp : (stackPtr s).toNat = (stackPtr entry).toNat - 536 :=
      (congrArg BitVec.toNat saved.sp).trans (stack_sub_toNat stack (offset := 536) (by decide))
    have cap := (stack_bounds stack).1
    intro r member
    simp only [Counter.writes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rw [sp]
    all_goals first
      | (rw [Counter.area_start stack (by decide)]; dsimp; omega)
      | (rw [Counter.scratch_start stack (by decide)]; dsimp; omega)
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    apply Counter.unchanged_slot (entry := entry) saved.sp afterCounter.sp
    exact Counter.preserves_area stack writes (by omega) (by omega) (by omega)

end Hkdf.Proofs.NewExpand.Expand
