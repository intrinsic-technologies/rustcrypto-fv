import Hkdf.Proofs.Common.Pad.Layout
import Hkdf.Proofs.Common.Refine

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common

abbrev regions (pointer : BitVec 64) : Vector MemoryRegion 1 := #v[⟨pointer.toNat, 64⟩]

theorem address_nat {pointer : BitVec 64} (low : pointer.toNat + 64 ≤ 2^32)
    {index : Nat} (within : index < 64) :
    (pointer + BitVec.ofNat 64 index).toNat = pointer.toNat + index := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show index < 2^64 by omega), Nat.mod_eq_of_lt (by omega)]

theorem writesWithin {pointer : BitVec 64} (low : pointer.toNat + 64 ≤ 2^32) :
    WritesWithin (components pointer) (regions pointer) := by
  intro component member address covered
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact covered.elim
  · exact covered.elim
  · obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨⟨pointer.toNat, 64⟩, by simp [regions], ?_⟩
    rw [address_nat low hi]
    change pointer.toNat ≤ pointer.toNat + i ∧ pointer.toNat + i < pointer.toNat + 64
    constructor <;> omega
  · exact covered.elim

theorem buffer_avoids {s : RamState} {pointer : BitVec 64}
    (writable : Hkdf.Proofs.Refine.Writable Extracted.programImage s.external pointer 64) :
    ∀ region ∈ regions pointer, region.Avoids InProgram := by
  intro region member
  have eq : region = ⟨pointer.toNat, 64⟩ := by simpa only [regions, Vector.mem_singleton] using member
  subst region
  intro address inside forbidden
  obtain ⟨byte, code⟩ := forbidden
  change pointer.toNat ≤ address.toNat ∧ address.toNat < pointer.toNat + 64 at inside
  let index := address.toNat - pointer.toNat
  have bound : index < 64 := by dsimp [index]; omega
  have same : address = pointer + BitVec.ofNat 64 index := by
    apply BitVec.eq_of_toNat_eq
    rw [address_nat writable.readable.low bound]
    dsimp [index]
    omega
  exact writable.notCode (address, byte) code index bound same

theorem widen_byte {s t : RamState} {pointer : BitVec 64} {index : Nat}
    (within : index < 64)
    (agrees : AgreesExcept [.mem (pointer + BitVec.ofNat 64 index) 1, .flags, .rip] s t) :
    AgreesExcept (components pointer) s t := by
  apply agrees.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp_all [Component.isMem, components]
  · intro a c hc cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨j, hj, rfl⟩ := cover
      refine ⟨.mem pointer 64, by simp [components], index + j, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
    · exact cover.elim
    · exact cover.elim

theorem writable_running [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {pointer : BitVec 64} (running : CallFrame.Running initial boundary (regions pointer) s)
    (writable : Hkdf.Proofs.Refine.Writable Extracted.programImage initial.external pointer 64) :
    Hkdf.Proofs.Refine.Writable Extracted.programImage s.external pointer 64 :=
  ⟨⟨writable.readable.low, fun i hi ↦ running.allocated _ (writable.readable.present i hi)⟩,
    writable.tables, writable.notCode⟩

theorem agrees_trans {s t u : RamState} {pointer : BitVec 64}
    (left : AgreesExcept (components pointer) s t)
    (right : AgreesExcept (components pointer) t u) :
    AgreesExcept (components pointer) s u :=
  (left.trans right).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)

end Hkdf.Proofs.Common.Pad
