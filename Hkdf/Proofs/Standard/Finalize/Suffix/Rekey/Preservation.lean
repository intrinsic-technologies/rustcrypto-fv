import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Stages
import Hkdf.Proofs.Common.Pad.Layout
import Hkdf.Proofs.Common.CallFrame

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Rekey

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem disjoint_slot (p : BitVec 64) {offset len slot n i : Nat}
    (bound : offset + len ≤ 416) (slotBound : slot + n ≤ 416)
    (apart : offset + len ≤ slot ∨ slot + n ≤ offset) (hi : i < len) :
    ¬ (Component.mem (p + BitVec.ofNat 64 slot) n).Covers
      (p + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  rintro ⟨j, hj, eq⟩
  exact RangeApart.offsets p (by omega) (by omega) apart i hi j hj eq

theorem setup_preserves (outer : Bool) {s t : RamState}
    (effect : (Stages.setupEffect outer s).Holds s t) (offset len : Nat)
    (bound : offset + len ≤ 416)
    (apart : offset + len ≤ (if outer then 8 else 248) ∨
      (if outer then 48 else 288) ≤ offset) :
    (Component.mem (rspOf s + BitVec.ofNat 64 offset) len).Agrees s t := by
  intro i hi
  apply effect.agrees.byte
  intro c member covered
  cases outer <;>
    simp only [Stages.setupEffect, Bool.false_eq_true, ite_false, ite_true, Effect.components,
      List.map_append, List.map_cons, List.map_nil, Write.component, Operand.component,
      List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  · change offset + len ≤ 248 ∨ 288 ≤ offset at apart
    rcases member with ((rfl | rfl | rfl | rfl) |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered
    · exact disjoint_slot (rspOf s) (slot := 272) (n := 8) bound (by decide) (by omega) hi covered
    · exact disjoint_slot (rspOf s) (slot := 264) (n := 8) bound (by decide) (by omega) hi covered
    · exact disjoint_slot (rspOf s) (slot := 256) (n := 8) bound (by decide) (by omega) hi covered
    · exact disjoint_slot (rspOf s) (slot := 248) (n := 8) bound (by decide) (by omega) hi covered
    · exact disjoint_slot (rspOf s) (slot := 280) (n := 8) bound (by decide) (by omega) hi covered
  · change offset + len ≤ 8 ∨ 48 ≤ offset at apart
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered
    · exact disjoint_slot (rspOf s) (slot := 32) (n := 8) bound (by decide) (by omega) hi covered
    · exact disjoint_slot (rspOf s) (slot := 24) (n := 8) bound (by decide) (by omega) hi covered
    · exact disjoint_slot (rspOf s) (slot := 16) (n := 8) bound (by decide) (by omega) hi covered
    · exact disjoint_slot (rspOf s) (slot := 8) (n := 8) bound (by decide) (by omega) hi covered
    · exact disjoint_slot (rspOf s) (slot := 40) (n := 8) bound (by decide) (by omega) hi covered

theorem pad_preserves {s t : RamState} (p : BitVec 64)
    (effect : AgreesExcept (Common.Pad.components (p + 72)) s t) (offset len : Nat)
    (bound : offset + len ≤ 416) (apart : offset + len ≤ 72 ∨ 136 ≤ offset) :
    (Component.mem (p + BitVec.ofNat 64 offset) len).Agrees s t := by
  intro i hi
  apply effect.byte
  intro c member covered
  simp only [Common.Pad.components, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals try exact covered
  exact disjoint_slot p (slot := 72) (n := 64) bound (by decide) apart hi covered

theorem compress_preserves (p : BitVec 64) {s t : RamState} (slot : Nat)
    (frame : MemoryWriteFrame s t #v[
      MemoryRegion.mk (p + BitVec.ofNat 64 slot).toNat 32, MemoryRegion.mk (p - 344).toNat 344])
    (bounds : 344 ≤ p.toNat ∧ p.toNat + 408 + 8 < 2^32) (offset len : Nat)
    (bound : offset + len ≤ 416) (slotBound : slot + 32 ≤ 416)
    (apart : offset + len ≤ slot ∨ slot + 32 ≤ offset) :
    (Component.mem (p + BitVec.ofNat 64 offset) len).Agrees s t := by
  have addr (n : Nat) (hn : n ≤ 416) : (p + BitVec.ofNat 64 n).toNat = p.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  have below : (p - 344).toNat = p.toNat - 344 := by
    rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def, BitVec.reduceToNat] using bounds.1)]
    rfl
  apply frame_agrees_of_disjoint frame
  · rw [addr offset (by omega)]
    omega
  · intro r member a kept written
    change (p + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (p + BitVec.ofNat 64 offset).toNat + len at kept
    rw [addr offset (by omega)] at kept
    have cases : r = ⟨(p + BitVec.ofNat 64 slot).toNat, 32⟩ ∨ r = ⟨(p - 344).toNat, 344⟩ := by
      simpa using member
    rcases cases with rfl | rfl
    · change (p + BitVec.ofNat 64 slot).toNat ≤ a ∧ a < (p + BitVec.ofNat 64 slot).toNat + 32 at written
      rw [addr slot (by omega)] at written
      omega
    · change (p - 344).toNat ≤ a ∧ a < (p - 344).toNat + 344 at written
      rw [below] at written
      omega

end Hkdf.Proofs.Standard.Finalize.Suffix.Rekey
