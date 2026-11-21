import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine

abbrev area (entry : RamState) (off size : Nat) : MemoryRegion :=
  ⟨(base entry + BitVec.ofNat 64 off).toNat, size⟩

abbrev scratch (entry : RamState) (size : Nat) : MemoryRegion :=
  ⟨(base entry - BitVec.ofNat 64 size).toNat, size⟩

def writes (entry : RamState) : Vector MemoryRegion 4 :=
  #v[area entry 8 8, area entry 80 144, area entry 272 104, scratch entry 344]

theorem area_start {entry : RamState} {off size : Nat} (stack : Stack.Valid entry 2264)
    (bound : off ≤ 536) : (area entry off size).start = (stackPtr entry).toNat - 536 + off := by
  change (base entry + BitVec.ofNat 64 off).toNat = _
  rw [base_add bound, stack_sub_toNat stack (by omega : 536 - off ≤ 2264)]
  have := (stack_bounds stack).1
  omega

theorem scratch_start {entry : RamState} {size : Nat} (stack : Stack.Valid entry 2264)
    (bound : size ≤ 1728) : (scratch entry size).start = (stackPtr entry).toNat - 536 - size := by
  change (base entry - BitVec.ofNat 64 size).toNat = _
  rw [base, BitVec.sub_sub, show (536 : BitVec 64) = BitVec.ofNat 64 536 from rfl, ← BitVec.ofNat_add,
    stack_sub_toNat stack (by omega : 536 + size ≤ 2264)]
  omega

theorem area_bounded {entry : RamState} {off size : Nat} (stack : Stack.Valid entry 2264)
    (bound : off ≤ 536) (fit : off + size ≤ 544) :
    (area entry off size).Bounded := by
  change (area entry off size).start + size < 2^32
  rw [area_start stack bound]
  have := (stack_bounds stack).2
  omega

theorem area_subset {entry : RamState} {off off' size size' : Nat}
    (stack : Stack.Valid entry 2264) (left : off ≤ 536) (right : off' ≤ 536)
    (lower : off' ≤ off) (upper : off + size ≤ off' + size') :
    ∀ a, (area entry off size).Contains a → (area entry off' size').Contains a := by
  intro a ha
  change (area entry off size).start ≤ a ∧ a < (area entry off size).start + size at ha
  change (area entry off' size').start ≤ a ∧ a < (area entry off' size').start + size'
  rw [area_start stack right]
  rw [area_start stack left] at ha
  omega

theorem scratch_subset {entry : RamState} {size size' : Nat}
    (stack : Stack.Valid entry 2264) (le : size ≤ size') (bound : size' ≤ 1728) :
    ∀ a, (scratch entry size).Contains a → (scratch entry size').Contains a := by
  intro a ha
  change (scratch entry size).start ≤ a ∧ a < (scratch entry size).start + size at ha
  change (scratch entry size').start ≤ a ∧ a < (scratch entry size').start + size'
  rw [scratch_start stack bound]
  rw [scratch_start stack (by omega : size ≤ 1728)] at ha
  have := (stack_bounds stack).1
  omega

theorem area_disjoint {entry : RamState} {off off' size size' : Nat} (stack : Stack.Valid entry 2264)
    (left : off ≤ 536) (right : off' ≤ 536)
    (apart : off + size ≤ off' ∨ off' + size' ≤ off) :
    (area entry off size).Disjoint (area entry off' size') := by
  intro a ha hb
  change (area entry off size).start ≤ a ∧ a < (area entry off size).start + size at ha
  change (area entry off' size').start ≤ a ∧ a < (area entry off' size').start + size' at hb
  rw [area_start stack left] at ha
  rw [area_start stack right] at hb
  omega

theorem area_disjoint_scratch {entry : RamState} {off size depth : Nat} (stack : Stack.Valid entry 2264)
    (bound : off ≤ 536) (depthBound : depth ≤ 1728) :
    (area entry off size).Disjoint (scratch entry depth) := by
  intro a ha hb
  have low : (area entry off size).start ≤ a := ha.1
  have high : a < (scratch entry depth).start + depth := hb.2
  rw [area_start stack bound] at low
  rw [scratch_start stack depthBound] at high
  have := (stack_bounds stack).1
  omega

theorem area_agrees {entry s t : RamState} {off size n : Nat} {regions : Vector MemoryRegion n}
    (stack : Stack.Valid entry 2264) (frame : MemoryWriteFrame s t regions)
    (bound : off ≤ 536) (fit : off + size ≤ 544)
    (apart : ∀ r ∈ regions, (area entry off size).Disjoint r) :
    (Component.mem (base entry + BitVec.ofNat 64 off) size).Agrees s t := by
  apply frame_agrees_of_disjoint frame _ apart
  have h := area_bounded stack bound fit
  change (base entry + BitVec.ofNat 64 off).toNat + size < 2^32 at h
  omega

theorem preserves_area {entry s t : RamState} {off size : Nat} (stack : Stack.Valid entry 2264)
    (frame : MemoryWriteFrame s t (writes entry)) (bound : off ≤ 536) (fit : off + size ≤ 544)
    (apart : 16 ≤ off ∧ off + size ≤ 80 ∨ 224 ≤ off ∧ off + size ≤ 272 ∨ 376 ≤ off) :
    (Component.mem (base entry + BitVec.ofNat 64 off) size).Agrees s t := by
  apply area_agrees stack frame bound fit
  intro r member
  have cases : r = area entry 8 8 ∨ r = area entry 80 144 ∨
      r = area entry 272 104 ∨ r = scratch entry 344 := by simpa [writes] using member
  rcases cases with rfl | rfl | rfl | rfl
  · exact area_disjoint stack bound (by decide) (by omega)
  · exact area_disjoint stack bound (by decide) (by omega)
  · exact area_disjoint stack bound (by decide) (by omega)
  · exact area_disjoint_scratch stack bound (by decide)

theorem contains_byte {entry : RamState} {off size i : Nat} (stack : Stack.Valid entry 2264)
    (bound : off ≤ 536) (fit : off + size ≤ 544) (small : i < size) :
    (area entry off size).Contains (base entry + BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add (area_bounded stack bound fit) (Nat.le_refl _) (Nat.le_refl _) small

theorem agrees_write_frame {entry s t : RamState} {off size : Nat} {components : List Component}
    (stack : Stack.Valid entry 2264) (bound : off ≤ 536) (fit : off + size ≤ 544)
    (agrees : AgreesExcept components s t)
    (writesIn : ∀ c ∈ components, ∀ a, c.Covers a →
      (Component.mem (base entry + BitVec.ofNat 64 off) size).Covers a) :
    MemoryWriteFrame s t #v[area entry off size] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  obtain ⟨i, hi, eq⟩ := writesIn c hc a ha
  exact ⟨_, by simp, eq ▸ contains_byte stack bound fit hi⟩

theorem unchanged_slot {entry s t : RamState} {off : Nat}
    (spS : stackPtr s = base entry) (spT : stackPtr t = base entry)
    (same : (Component.mem (base entry + BitVec.ofNat 64 off) 8).Agrees s t) :
    slot t (BitVec.ofNat 64 off) = slot s (BitVec.ofNat 64 off) := by
  change memLoad t.external (stackPtr t + _) 64 = memLoad s.external (stackPtr s + _) 64
  rw [spT, spS]
  exact agrees_memLoad same

end Hkdf.Proofs.NewExpand.Expand.Counter
