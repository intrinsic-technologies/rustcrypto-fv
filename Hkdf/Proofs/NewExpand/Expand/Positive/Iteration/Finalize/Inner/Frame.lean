import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Block
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.StackWrites

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Inner

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Prelude X86 X86.Machine X86Proofs

def writes (sp : BitVec 64) : Vector MemoryRegion 4 :=
  #v[⟨(sp + 16).toNat, 64⟩, ⟨(sp + 136).toNat, 40⟩,
    ⟨(sp + 256).toNat, 8⟩, ⟨sp.toNat - 344, 344⟩]

theorem local_bounds {entry s : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) :
    344 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 544 < 2^32 := by
  have base : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [sp]
    exact stack_sub_toNat stack (by decide)
  obtain ⟨lo, hi⟩ := stack_bounds stack
  omega

private theorem offset_nat {sp : BitVec 64} (high : sp.toNat + 544 < 2^32)
    (offset : Nat) (bound : offset ≤ 544) :
    (sp + BitVec.ofNat 64 offset).toNat = sp.toNat + offset := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
    Nat.mod_eq_of_lt (by omega)]

private theorem contains_offset {sp : BitVec 64} (high : sp.toNat + 544 < 2^32)
    {off size : Nat} (bound : off + size ≤ 544) {a : BitVec 64}
    (covers : (Component.mem (sp + BitVec.ofNat 64 off) size).Covers a) :
    (⟨(sp + BitVec.ofNat 64 off).toNat, size⟩ : MemoryRegion).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covers
  change (sp + BitVec.ofNat 64 off).toNat ≤ _ ∧
    _ < (sp + BitVec.ofNat 64 off).toNat + size
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, offset_nat high (off + i) (by omega),
    offset_nat high off (by omega)]
  omega

private theorem local_subset {sp : BitVec 64} (high : sp.toNat + 544 < 2^32)
    {src dst size span : Nat} (lo : dst ≤ src) (hi : src + size ≤ dst + span)
    (bound : dst + span ≤ 544) {a : Nat}
    (inside : (⟨(sp + BitVec.ofNat 64 src).toNat, size⟩ : MemoryRegion).Contains a) :
    (⟨(sp + BitVec.ofNat 64 dst).toNat, span⟩ : MemoryRegion).Contains a := by
  change (sp + BitVec.ofNat 64 src).toNat ≤ a ∧
    a < (sp + BitVec.ofNat 64 src).toNat + size at inside
  change (sp + BitVec.ofNat 64 dst).toNat ≤ a ∧ a < (sp + BitVec.ofNat 64 dst).toNat + span
  rw [offset_nat high src (by omega)] at inside
  rw [offset_nat high dst (by omega)]
  omega

theorem precise_effect {s t : RamState} {components : List Component}
    {sp : BitVec 64} {ranges : List (Nat × Nat)}
    (high : sp.toNat + 544 < 2^32)
    (effect : AgreesExcept components s t) (footprint : StackWrites components sp ranges)
    (within : ∀ r ∈ ranges, r = (72, 8) ∨ r = (136, 8) ∨ r = (256, 8)) :
    MemoryWriteFrame s t (writes sp) := by
  apply effect.memoryWriteFrame
  intro c hc a covered
  obtain ⟨r, hr, h⟩ := footprint c hc a covered
  rcases within r hr with rfl | rfl | rfl
  · refine ⟨⟨(sp + 16).toNat, 64⟩, by simp [writes], ?_⟩
    exact local_subset high (src := 72) (dst := 16) (by decide) (by decide) (by decide)
      (contains_offset high (by decide) h)
  · refine ⟨⟨(sp + 136).toNat, 40⟩, by simp [writes], ?_⟩
    exact local_subset high (src := 136) (dst := 136) (by decide) (by decide) (by decide)
      (contains_offset high (by decide) h)
  · exact ⟨⟨(sp + 256).toNat, 8⟩, by simp [writes], contains_offset high (by decide) h⟩

theorem compression_frame {s t : RamState} {sp : BitVec 64}
    (high : sp.toNat + 544 < 2^32)
    (frame : MemoryWriteFrame s t (CompressionSite.blockWrites .inner sp)) :
    MemoryWriteFrame s t (writes sp) := by
  apply frame_mono frame
  intro r hr a inside
  have choices : r = (⟨(sp + 16).toNat, 56⟩ : MemoryRegion) ∨
      r = ⟨(sp + 144).toNat, 32⟩ ∨ r = ⟨sp.toNat - 344, 344⟩ := by
    simpa only [CompressionSite.blockWrites, CompressionSite.hashOffset, Vector.mem_mk,
      List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, BitVec.ofNat_eq_ofNat] using hr
  rcases choices with rfl | rfl | rfl
  · refine ⟨⟨(sp + 16).toNat, 64⟩, by simp [writes], ?_⟩
    exact local_subset high (src := 16) (dst := 16) (by decide) (by decide) (by decide) inside
  · refine ⟨⟨(sp + 136).toNat, 40⟩, by simp [writes], ?_⟩
    exact local_subset high (src := 144) (dst := 136) (by decide) (by decide) (by decide) inside
  · exact ⟨_, by simp [writes], inside⟩

theorem agrees {s t : RamState} {sp : BitVec 64} {off size : Nat}
    (base : 344 ≤ sp.toNat) (high : sp.toNat + 544 < 2^32)
    (frame : MemoryWriteFrame s t (writes sp))
    (bound : off + size ≤ 544)
    (apart : off + size ≤ 16 ∨
      (80 ≤ off ∧ off + size ≤ 136) ∨ (176 ≤ off ∧ off + size ≤ 256) ∨ 264 ≤ off) :
    (Component.mem (sp + BitVec.ofNat 64 off) size).Agrees s t := by
  apply frame_agrees_of_disjoint frame
  · rw [offset_nat high off (by omega)]
    omega
  · intro r hr a has written
    have choices : r = (⟨(sp + 16).toNat, 64⟩ : MemoryRegion) ∨
        r = ⟨(sp + 136).toNat, 40⟩ ∨ r = ⟨(sp + 256).toNat, 8⟩ ∨
        r = ⟨sp.toNat - 344, 344⟩ := by
      simpa only [writes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] using hr
    change (sp + BitVec.ofNat 64 off).toNat ≤ a ∧
      a < (sp + BitVec.ofNat 64 off).toNat + size at has
    rw [offset_nat high off (by omega)] at has
    rcases choices with rfl | rfl | rfl | rfl
    · change (sp + BitVec.ofNat 64 16).toNat ≤ a ∧ a < (sp + BitVec.ofNat 64 16).toNat + 64 at written
      rw [offset_nat high 16 (by decide)] at written
      omega
    · change (sp + BitVec.ofNat 64 136).toNat ≤ a ∧ a < (sp + BitVec.ofNat 64 136).toNat + 40 at written
      rw [offset_nat high 136 (by decide)] at written
      omega
    · change (sp + BitVec.ofNat 64 256).toNat ≤ a ∧ a < (sp + BitVec.ofNat 64 256).toNat + 8 at written
      rw [offset_nat high 256 (by decide)] at written
      omega
    · change sp.toNat - 344 ≤ a ∧ a < sp.toNat - 344 + 344 at written
      omega

theorem compression_counter {s t : RamState} {sp : BitVec 64}
    (base : 344 ≤ sp.toNat) (high : sp.toNat + 544 < 2^32)
    (frame : MemoryWriteFrame s t (CompressionSite.blockWrites .inner sp)) :
    (Component.mem (sp + BitVec.ofNat 64 256) 8).Agrees s t := by
  apply frame_agrees_of_disjoint frame
  · rw [offset_nat high 256 (by decide)]
    omega
  · intro r hr a counter written
    have choices : r = (⟨(sp + 16).toNat, 56⟩ : MemoryRegion) ∨
        r = ⟨(sp + 144).toNat, 32⟩ ∨ r = ⟨sp.toNat - 344, 344⟩ := by
      simpa only [CompressionSite.blockWrites, CompressionSite.hashOffset, Vector.mem_mk,
        List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, BitVec.ofNat_eq_ofNat] using hr
    change (sp + BitVec.ofNat 64 256).toNat ≤ a ∧
      a < (sp + BitVec.ofNat 64 256).toNat + 8 at counter
    rw [offset_nat high 256 (by decide)] at counter
    rcases choices with rfl | rfl | rfl
    · change (sp + BitVec.ofNat 64 16).toNat ≤ a ∧ a < (sp + BitVec.ofNat 64 16).toNat + 56 at written
      rw [offset_nat high 16 (by decide)] at written
      omega
    · change (sp + BitVec.ofNat 64 144).toNat ≤ a ∧ a < (sp + BitVec.ofNat 64 144).toNat + 32 at written
      rw [offset_nat high 144 (by decide)] at written
      omega
    · change sp.toNat - 344 ≤ a ∧ a < sp.toNat - 344 + 344 at written
      omega

theorem within_stack {entry s : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) :
    ∀ r ∈ writes (stackPtr s), ∀ a, r.Contains a → (Stack.region entry 2264).Contains a := by
  obtain ⟨lo, high⟩ := local_bounds stack sp
  have start : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [sp]
    exact stack_sub_toNat stack (by decide)
  have base : 2264 ≤ (stackPtr entry).toNat := stack.2.2.1
  have stackEnd := stack_region_end entry 2264
  intro r hr a inside
  have choices : r = (⟨(stackPtr s + 16).toNat, 64⟩ : MemoryRegion) ∨
      r = ⟨(stackPtr s + 136).toNat, 40⟩ ∨ r = ⟨(stackPtr s + 256).toNat, 8⟩ ∨
      r = ⟨(stackPtr s).toNat - 344, 344⟩ := by
    simpa only [writes, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] using hr
  change (stackPtr entry).toNat - 2264 ≤ a ∧
    a < (Stack.region entry 2264).start + (Stack.region entry 2264).size
  rw [stackEnd]
  rcases choices with rfl | rfl | rfl | rfl
  · change (stackPtr s + BitVec.ofNat 64 16).toNat ≤ a ∧
      a < (stackPtr s + BitVec.ofNat 64 16).toNat + 64 at inside
    rw [offset_nat high 16 (by decide)] at inside
    omega
  · change (stackPtr s + BitVec.ofNat 64 136).toNat ≤ a ∧
      a < (stackPtr s + BitVec.ofNat 64 136).toNat + 40 at inside
    rw [offset_nat high 136 (by decide)] at inside
    omega
  · change (stackPtr s + BitVec.ofNat 64 256).toNat ≤ a ∧
      a < (stackPtr s + BitVec.ofNat 64 256).toNat + 8 at inside
    rw [offset_nat high 256 (by decide)] at inside
    omega
  · change (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat - 344 + 344 at inside
    have edge : (stackPtr entry).toNat - 2264 ≤ (stackPtr s).toNat - 344 := by
      rw [start, Nat.sub_sub]
      exact Nat.sub_le_sub_left (by decide : 536 + 344 ≤ 2264) _
    have upper : a < (stackPtr s).toNat := by
      simpa only [Nat.sub_add_cancel lo] using inside.2
    exact ⟨Nat.le_trans edge inside.1, Nat.lt_of_lt_of_le upper (by rw [start]; exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _))⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.Inner
