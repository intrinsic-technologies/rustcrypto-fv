import Hkdf.Proofs.Standard.Finalize.Suffix.State
import Hkdf.Proofs.Common.Pad.Permissions

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Rekey

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.StreamPadding (base regions)
open Hkdf.Proofs.Common.StreamPadding.Execution
open Hkdf.Proofs.Common.Machine (stack_region_end)

def writes (initial : RamState) : Vector MemoryRegion 3 :=
  #v[⟨(base .hmac initial - 344).toNat, 344⟩,
    ⟨(base .hmac initial + 8).toNat, 128⟩,
    ⟨(base .hmac initial + 248).toNat, 120⟩]

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}

theorem writes_within
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264) :
    ∀ region ∈ writes initial, ∀ a, region.Contains a →
      ∃ outer ∈ regions .hmac initial, outer.Contains a := by
  have bounds := stack_bounds pre.stack
  intro region member a contains
  refine ⟨Stack.region initial 1264, by simp [regions, Common.StreamPadding.Variant.outputBytes, Common.StreamPadding.Variant.reserve], ?_⟩
  have cases : region = ⟨(base .hmac initial - 344).toNat, 344⟩ ∨
      region = ⟨(base .hmac initial + 8).toNat, 128⟩ ∨
      region = ⟨(base .hmac initial + 248).toNat, 120⟩ := by
    simpa only [writes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] using member
  change (stackPtr initial).toNat - 1264 ≤ a ∧
    a < (Stack.region initial 1264).start + (Stack.region initial 1264).size
  rw [stack_region_end]
  rcases cases with rfl | rfl | rfl
  · change (base .hmac initial - BitVec.ofNat 64 344).toNat ≤ a ∧
      a < (base .hmac initial - BitVec.ofNat 64 344).toNat + 344 at contains
    rw [below_toNat .hmac pre 344 (by decide)] at contains
    simp only [Common.StreamPadding.Variant.frame, Nat.reduceAdd] at contains
    constructor <;> omega
  · change (base .hmac initial + BitVec.ofNat 64 8).toNat ≤ a ∧
      a < (base .hmac initial + BitVec.ofNat 64 8).toNat + 128 at contains
    rw [local_toNat .hmac pre 8 (by decide)] at contains
    simp only [Common.StreamPadding.Variant.frame] at contains
    constructor <;> omega
  · change (base .hmac initial + BitVec.ofNat 64 248).toNat ≤ a ∧
      a < (base .hmac initial + BitVec.ofNat 64 248).toNat + 120 at contains
    rw [local_toNat .hmac pre 248 (by decide)] at contains
    simp only [Common.StreamPadding.Variant.frame] at contains
    constructor <;> omega

theorem local_within (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (rsp : stackPtr s = stackPtr initial - 408)
    (offset len : Nat)
    (within : (8 ≤ offset ∧ offset + len ≤ 136) ∨
      (248 ≤ offset ∧ offset + len ≤ 368)) :
    ∀ a, (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a →
      ∃ region ∈ writes initial, region.Contains a.toNat := by
  have sp : stackPtr s = base .hmac initial := rsp
  have bounds := local_bounds .hmac pre sp
  rw [sp]
  rcases within with ⟨low, high⟩ | ⟨low, high⟩
  · intro a covered
    refine ⟨⟨(base .hmac initial + 8).toNat, 128⟩, by simp [writes], ?_⟩
    exact offset_component (base .hmac initial) offset len 8 128
      (by rw [← sp]; simp only [Common.StreamPadding.Variant.frame] at bounds; omega)
      low high a covered
  · intro a covered
    refine ⟨⟨(base .hmac initial + 248).toNat, 120⟩, by simp [writes], ?_⟩
    exact offset_component (base .hmac initial) offset len 248 120
      (by rw [← sp]; simp only [Common.StreamPadding.Variant.frame] at bounds; omega)
      low high a covered

theorem preserved
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (frame : MemoryWriteFrame s t (writes initial))
    (offset size : Nat)
    (apart : (136 ≤ offset ∧ offset + size ≤ 248) ∨
      (368 ≤ offset ∧ offset + size ≤ 416)) :
    (Component.mem (base .hmac initial + BitVec.ofNat 64 offset) size).Agrees s t := by
  have bounds := stack_bounds pre.stack
  have high : offset + size ≤ 416 := by omega
  have toNat (n : Nat) (hn : n ≤ 416) := local_toNat .hmac pre n hn
  apply frame_agrees_of_disjoint frame
  · rw [toNat offset (by omega)]
    simp only [Common.StreamPadding.Variant.frame]
    omega
  · intro region member a contains written
    have cases : region = ⟨(base .hmac initial - 344).toNat, 344⟩ ∨
        region = ⟨(base .hmac initial + 8).toNat, 128⟩ ∨
        region = ⟨(base .hmac initial + 248).toNat, 120⟩ := by
      simpa only [writes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] using member
    change (base .hmac initial + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (base .hmac initial + BitVec.ofNat 64 offset).toNat + size at contains
    rw [toNat offset (by omega)] at contains
    rcases cases with rfl | rfl | rfl
    · change (base .hmac initial - BitVec.ofNat 64 344).toNat ≤ a ∧
        a < (base .hmac initial - BitVec.ofNat 64 344).toNat + 344 at written
      rw [below_toNat .hmac pre 344 (by decide)] at written
      simp only [Common.StreamPadding.Variant.frame, Nat.reduceAdd] at contains written
      omega
    · change (base .hmac initial + BitVec.ofNat 64 8).toNat ≤ a ∧
        a < (base .hmac initial + BitVec.ofNat 64 8).toNat + 128 at written
      rw [toNat 8 (by decide)] at written
      simp only [Common.StreamPadding.Variant.frame] at contains written
      omega
    · change (base .hmac initial + BitVec.ofNat 64 248).toNat ≤ a ∧
        a < (base .hmac initial + BitVec.ofNat 64 248).toNat + 120 at written
      rw [toNat 248 (by decide)] at written
      simp only [Common.StreamPadding.Variant.frame] at contains written
      omega

theorem saved_after
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (frame : MemoryWriteFrame s t (writes initial)) :
    (Component.mem (stackPtr initial - 40) 48).Agrees s t := by
  have saved := preserved pre frame 368 48 (by right; constructor <;> decide)
  simpa only [local_address .hmac pre 368 (by decide), Common.StreamPadding.Variant.frame, Nat.reduceSub,
    BitVec.ofNat_eq_ofNat] using saved

theorem digest_after
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (frame : MemoryWriteFrame s t (writes initial)) {digest : ByteArray}
    (bytes : (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes
      s.external digest) :
    (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes t.external digest := by
  have same := preserved pre frame 216 32 (by left; constructor <;> decide)
  rw [local_address .hmac pre 216 (by decide)] at same
  change (Component.mem (stackPtr initial - 192) 32).Agrees s t at same
  refine ⟨bytes.1, fun i ↦ ?_⟩
  have hi : i.val < 32 := by
    have size : digest.size = 32 := bytes.1
    have := i.isLt
    omega
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    (same i.val hi).trans (by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using bytes.2 i)

end Hkdf.Proofs.Standard.Finalize.Suffix.Rekey
