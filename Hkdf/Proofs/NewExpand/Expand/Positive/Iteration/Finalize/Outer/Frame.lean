import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.StackWrites
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Store

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Outer

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Prelude X86 X86.Machine X86.UserProcess X86Proofs

def writeRegions (sp : BitVec 64) : Vector MemoryRegion 3 :=
  #v[⟨sp.toNat - 344, 344⟩, ⟨sp.toNat + 16, 128⟩, ⟨sp.toNat + 184, 32⟩]

theorem stack_address {entry s : RamState}
    (sp : stackPtr s = stackPtr entry - 536) {offset : Nat} (fit : offset ≤ 536) :
    stackPtr s + BitVec.ofNat 64 offset = stackPtr entry - BitVec.ofNat 64 (536 - offset) := by
  rw [sp, ← BitVec.ofNat_sub_ofNat_of_le 536 offset (by omega) fit]
  bv_omega

theorem stack_toNat {entry s : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) {offset : Nat} (fit : offset ≤ 536) :
    (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
  have base : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [sp, show (stackPtr entry - 536).toNat = _ from
      stack_sub_toNat stack (offset := 536) (by decide)]
  rw [stack_address sp fit, stack_sub_toNat stack (by omega), base]
  have := (stack_bounds stack).1
  omega

theorem local_readable {entry s : RamState} (stack : Stack.Valid entry 2264)
    (grow : ∀ a : BitVec 64, (entry.external[a]?).isSome → (s.external[a]?).isSome)
    (sp : stackPtr s = stackPtr entry - 536) {offset len : Nat} (fit : offset + len ≤ 544)
    (start : offset ≤ 536) : MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  rw [stack_address sp start]
  exact stack_readable stack grow (by omega) (by omega)

theorem local_writable {entry s : RamState} (stack : Stack.Valid entry 2264)
    (avoid : (Stack.region entry 2264).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (grow : ∀ a : BitVec 64, (entry.external[a]?).isSome → (s.external[a]?).isSome)
    (sp : stackPtr s = stackPtr entry - 536) {offset len : Nat} (fit : offset + len ≤ 536)
    (pos : 0 < len) : Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s
      (stackPtr s + BitVec.ofNat 64 offset) len := by
  have read := local_readable stack grow sp (offset := offset) (len := len) (by omega) (by omega)
  refine ⟨read, tables_of_not_reserved pos read.low ?_⟩
  intro i hi reserved
  have covered : (Component.mem (stackPtr entry - BitVec.ofNat 64 (536 - offset)) len).Covers
      (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) :=
    ⟨i, hi, by rw [stack_address sp (by omega : offset ≤ 536)]⟩
  exact avoid _ (stackRegion_contains_sub stack.2.2.1 (by omega) (by omega) covered) (.inr reserved)

theorem local_codeApart {entry s : RamState} (stack : Stack.Valid entry 2264)
    (avoid : (Stack.region entry 2264).Avoids InProgram)
    (sp : stackPtr s = stackPtr entry - 536) {offset len codeOffset codeLen : Nat}
    (fit : offset + len ≤ 544) (start : offset ≤ 536) (bound : codeOffset + codeLen ≤ 115149) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  rw [stack_address sp start]
  exact stack_codeApart stack avoid (by omega) (by omega) bound

theorem local_frame {entry s t : RamState} {components : List Component}
    (stack : Stack.Valid entry 2264) (sp : stackPtr s = stackPtr entry - 536)
    (agree : AgreesExcept components s t) {ranges : List (Nat × Nat)}
    (writes : StackWrites components (stackPtr s) ranges)
    (within : ∀ r ∈ ranges, 16 ≤ r.1 ∧ r.1 + r.2 ≤ 144) :
    MemoryWriteFrame s t (writeRegions (stackPtr s)) := by
  apply agree.memoryWriteFrame
  intro c member a covered
  obtain ⟨⟨offset, len⟩, hr, i, hi, rfl⟩ := writes c member a covered
  obtain ⟨low, high⟩ := within _ hr
  change 16 ≤ offset at low
  change offset + len ≤ 144 at high
  refine ⟨⟨(stackPtr s).toNat + 16, 128⟩, by simp [writeRegions], ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, stack_toNat stack sp (by omega)]
  change (stackPtr s).toNat + 16 ≤ _ ∧ _ < (stackPtr s).toNat + 16 + 128
  omega

theorem writeRegions_inside {entry s : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) {r : MemoryRegion}
    (member : r ∈ writeRegions (stackPtr s)) {a : Nat} (contained : r.Contains a) :
    (Stack.region entry 2264).Contains a := by
  have base : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [sp]
    exact stack_sub_toNat stack (offset := 536) (by decide)
  have capacity := (stack_bounds stack).1
  have bounds : (Stack.region entry 2264).start ≤ a ∧
      a < (Stack.region entry 2264).start + (Stack.region entry 2264).size := by
    rw [stack_region_end]
    change (stackPtr entry).toNat - 2264 ≤ a ∧ a < (stackPtr entry).toNat + 8
    simp only [writeRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · change (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat - 344 + 344 at contained
      have bottom : (stackPtr s).toNat - 344 = (stackPtr entry).toNat - 880 := by
        rw [base, Nat.sub_sub]
      have lower : (stackPtr entry).toNat - 2264 ≤ (stackPtr s).toNat - 344 := by
        rw [bottom]
        exact Nat.sub_le_sub_left (by decide : 880 ≤ 2264) _
      have higher : (stackPtr s).toNat - 344 + 344 ≤ (stackPtr entry).toNat + 8 := by
        rw [bottom]
        omega
      exact ⟨Nat.le_trans lower contained.1, Nat.lt_of_lt_of_le contained.2 higher⟩
    · change (stackPtr s).toNat + 16 ≤ a ∧ a < (stackPtr s).toNat + 16 + 128 at contained
      omega
    · change (stackPtr s).toNat + 184 ≤ a ∧ a < (stackPtr s).toNat + 184 + 32 at contained
      omega
  exact bounds

theorem frame_agrees_local {entry s t : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536)
    (frame : MemoryWriteFrame s t (writeRegions (stackPtr s))) {offset len : Nat}
    (fit : offset + len ≤ 544) (start : offset ≤ 536)
    (apartWork : offset + len ≤ 16 ∨ 144 ≤ offset)
    (apartHash : offset + len ≤ 184 ∨ 216 ≤ offset) :
    (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Agrees s t := by
  have base : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [sp, show (stackPtr entry - 536).toNat = _ from
      stack_sub_toNat stack (offset := 536) (by decide)]
  have capacity := (stack_bounds stack).1
  apply frame_agrees_of_disjoint frame
  · rw [stack_toNat stack sp start]
    have := (stack_bounds stack).2
    omega
  · intro region member a ha hb
    simp only [writeRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rw [show (stackPtr s + BitVec.ofNat 64 offset).toNat = _ from stack_toNat stack sp start] at ha
    change (stackPtr s).toNat + offset ≤ a ∧ a < (stackPtr s).toNat + offset + len at ha
    rcases member with rfl | rfl | rfl
    · change (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat - 344 + 344 at hb
      omega
    · change (stackPtr s).toNat + 16 ≤ a ∧ a < (stackPtr s).toNat + 16 + 128 at hb
      omega
    · change (stackPtr s).toNat + 184 ≤ a ∧ a < (stackPtr s).toNat + 184 + 32 at hb
      omega

theorem slot_of_frame {entry s t : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) (spT : stackPtr t = stackPtr s)
    (frame : MemoryWriteFrame s t (writeRegions (stackPtr s))) {offset : Nat}
    (fit : offset ≤ 536)
    (apartWork : offset + 8 ≤ 16 ∨ 144 ≤ offset)
    (apartHash : offset + 8 ≤ 184 ∨ 216 ≤ offset) :
    slot t (BitVec.ofNat 64 offset) = slot s (BitVec.ofNat 64 offset) := by
  change memLoad t.external (stackPtr t + BitVec.ofNat 64 offset) 64 =
    memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64
  rw [spT]
  exact agrees_memLoad (frame_agrees_local stack sp frame (by omega) fit apartWork apartHash)

theorem abi_of_agreement {s t : RamState} {components : List Component}
    (agree : AgreesExcept components s t) (dir : RFLAGS.DirectionFlagClear s.RFLAGS)
    (registers : ∀ r ∈ ([3,5,12,13,14,15] : List (BitVec 5)), .reg r ∉ components)
    (df : .df ∉ components) (mxcsr : .mxcsr ∉ components) (fcw : .fcw ∉ components) :
    PreservesABI s t := by
  apply preservesABI_of_agrees agree dir ?_ df mxcsr fcw
  intro r member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact agree.read (n := 64) (registers 3 (by decide))
  · exact agree.read (n := 64) (registers 5 (by decide))
  · exact agree.read (n := 64) (registers 12 (by decide))
  · exact agree.read (n := 64) (registers 13 (by decide))
  · exact agree.read (n := 64) (registers 14 (by decide))
  · exact agree.read (n := 64) (registers 15 (by decide))

end Hkdf.Proofs.NewExpand.Expand.Finalize.Outer
