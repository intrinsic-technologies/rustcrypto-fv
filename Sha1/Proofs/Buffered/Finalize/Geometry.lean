import Sha1.Proofs.Buffered.Finalize.Contracts
import Sha1.Proofs.Common.Instructions.StorePre
import Sha1.Proofs.MemoryRoutines.Ranges
import Sha1.Proofs.Compress.Machine.Code
import X86Proofs.Program.Compose

namespace Sha1.Proofs.Buffered.Finalize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
abbrev Writable := Sha1.Proofs.Common.Instructions.StorePre.MemWritable

variable {kind : Kind} {boundary : ReturnBoundary} {message : ByteArray}
  {s t : RamState}

theorem Kind.frameBytes_eq : Kind.frameBytes = 344 := rfl

theorem memWritable_of_region {s : RamState} {addr : BitVec 64} {len : Nat}
    {region : Prelude.MemoryRegion} (hbounded : region.Bounded)
    (hallocated : region.Allocated s.external)
    (htables : region.Avoids InPageTables)
    (hstart : region.start ≤ addr.toNat) (hend : addr.toNat + len ≤ region.start + region.size) :
    Writable s addr len := by
  have hlow : addr.toNat + len ≤ 2^32 := by
    have : region.start + region.size < 2^32 := hbounded
    (have := Kind.frameBytes_eq; omega)
  have hcontains (i : Nat) (hi : i < len) :
      region.Contains (addr + BitVec.ofNat 64 i).toNat := by
    change region.start ≤ (addr + BitVec.ofNat 64 i).toNat ∧
      (addr + BitVec.ofNat 64 i).toNat < region.start + region.size
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by (have := Kind.frameBytes_eq; omega)),
      Nat.mod_eq_of_lt (show addr.toNat + i < 2^64 by (have := Kind.frameBytes_eq; omega))]
    (have := Kind.frameBytes_eq; omega)
  exact ⟨hlow, fun i hi ↦ Option.isSome_iff_exists.mpr (hallocated _ (hcontains i hi)),
    fun i hi ↦ htables _ (hcontains i hi)⟩

theorem writable_of_agrees {s t : RamState} {addr : BitVec 64} {len : Nat}
    {cs : List Component} (h : Writable s addr len)
    (he : AgreesExcept cs s t) : Writable t addr len :=
  ⟨h.low, fun i hi ↦ he.grow _ (h.mem i hi), h.tables⟩

theorem writable_of_holds {e : Effect} {s s' : RamState} {a : BitVec 64} {len : Nat}
    (h : e.Holds s s') (hm : Writable s a len) : Writable s' a len :=
  ⟨hm.low, fun i hi ↦ h.agrees.grow _ (hm.mem i hi), hm.tables⟩

theorem storePre_of_holds {e : Effect} {s s' : RamState} {p nxt : BitVec 64} {am : AddrMode}
    {len codeLen : Nat}
    (h : e.Holds s s') (ho : Obs (e.after s true) s') (hrip : e.rip = p)
    (hw : Writable s (am.addr (e.after s true) nxt) len)
    (hap : RangeApart (am.addr (e.after s true) nxt) len p codeLen) :
    Sha1.Proofs.Common.Instructions.StorePre.StorePre p codeLen (fun t ↦ am.addr t nxt) len s' :=
  ⟨h.rip_of hrip, by rw [← AddrMode.addr_obs ho]; exact writable_of_holds h hw,
    by rw [← AddrMode.addr_obs ho]; exact hap⟩

theorem readable_of_agrees {s t : RamState} {addr : BitVec 64} {len : Nat}
    {cs : List Component} (h : MemReadable s addr len) (he : AgreesExcept cs s t) :
    MemReadable t addr len :=
  ⟨h.low, fun i hi ↦ he.grow _ (h.mem i hi)⟩

theorem rangeApart_text {addr : BitVec 64} {len offset count : Nat}
    (ha : ∀ i < len, ¬ InProgram (addr + BitVec.ofNat 64 i))
    (hb : offset + count ≤ Extracted.textBytes.size) :
    RangeApart addr len (Extracted.textAddress + BitVec.ofNat 64 offset) count := by
  intro i hi j hj he
  apply ha i hi
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Sha1.Proofs.Compress.Machine.text_address_in_program (offset + j) (by (have := Kind.frameBytes_eq; omega))

theorem text_address_ne_return {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro hEq
  exact hOutside (hEq ▸ Sha1.Proofs.Compress.Machine.text_address_in_program offset h)

theorem Storage.stackBounded (h : Storage kind s) : (kind.stackRegion s).Bounded := by
  change (stackPtr s).toNat - Kind.frameBytes + (Kind.frameBytes + kind.stackBytes) < userAddressLimit
  have := h.stackLow
  have := h.stackHigh
  (have := Kind.frameBytes_eq; omega)

theorem Storage.stackAddress (h : Storage kind s) {offset : Nat}
    (ho : offset ≤ kind.stackBytes) :
    (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
  have hh : (stackPtr s).toNat + kind.stackBytes < 2^32 := h.stackHigh
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2^64 by (have := Kind.frameBytes_eq; omega)),
    Nat.mod_eq_of_lt (show (stackPtr s).toNat + offset < 2^64 by (have := Kind.frameBytes_eq; omega))]

theorem Storage.stackCover (h : Storage kind s) {offset len : Nat}
    (ho : offset + len ≤ kind.stackBytes) {address : BitVec 64}
    (hc : Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 offset) len) address) :
    (kind.stackRegion s).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.stackAddress (by (have := Kind.frameBytes_eq; omega))]
  change (stackPtr s).toNat - Kind.frameBytes ≤ (stackPtr s).toNat + (offset + i) ∧
    (stackPtr s).toNat + (offset + i) < (stackPtr s).toNat - Kind.frameBytes + (Kind.frameBytes + kind.stackBytes)
  have := h.stackLow
  (have := Kind.frameBytes_eq; omega)

theorem Storage.stackWritable (h : Storage kind s) (offset len : Nat)
    (ho : offset + len ≤ kind.stackBytes) :
    Writable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  apply memWritable_of_region h.stackBounded h.stackAllocated
    (fun a ha hp ↦ h.stackAvoids a ha (.inr hp))
  · rw [h.stackAddress (by (have := Kind.frameBytes_eq; omega))]
    change (stackPtr s).toNat - Kind.frameBytes ≤ _
    (have := Kind.frameBytes_eq; omega)
  · rw [h.stackAddress (by (have := Kind.frameBytes_eq; omega))]
    change _ ≤ (stackPtr s).toNat - Kind.frameBytes + (Kind.frameBytes + kind.stackBytes)
    have := h.stackLow
    (have := Kind.frameBytes_eq; omega)

theorem Storage.stackRange (h : Storage kind s) (offset len : Nat)
    (ho : offset + len ≤ kind.stackBytes) :
    MemoryRoutines.WritableRange s (stackPtr s + BitVec.ofNat 64 offset) len := by
  have hw := h.stackWritable offset len ho
  refine ⟨hw.readable, hw.tables, ?_⟩
  intro i hi hp
  exact h.stackAvoids _ (h.stackCover ho ⟨i, hi, rfl⟩) (.inl hp)

theorem Storage.stackApart (h : Storage kind s) {offset len codeOffset codeLen : Nat}
    (he : offset + len ≤ kind.stackBytes) (hc : codeOffset + codeLen ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  apply rangeApart_text _ hc
  exact (h.stackRange offset len he).code

theorem Storage.belowAddress (h : Storage kind s) :
    (stackPtr s - Kind.frameBytes).toNat = (stackPtr s).toNat - Kind.frameBytes := by
  rw [BitVec.toNat_sub_of_le]
  · rfl
  · exact h.stackLow

theorem Storage.localCover (h : Storage kind s) {address : BitVec 64}
    (hc : Component.Covers (.mem (stackPtr s - Kind.frameBytes) (Kind.frameBytes + kind.stackBytes)) address) :
    (kind.stackRegion s).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  have hh : (stackPtr s).toNat + kind.stackBytes < 2^32 := h.stackHigh
  rw [BitVec.toNat_add, h.belowAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2^64 by (have := Kind.frameBytes_eq; omega)),
    Nat.mod_eq_of_lt (show (stackPtr s).toNat - Kind.frameBytes + i < 2^64 by (have := Kind.frameBytes_eq; omega))]
  change (stackPtr s).toNat - Kind.frameBytes ≤ (stackPtr s).toNat - Kind.frameBytes + i ∧
    (stackPtr s).toNat - Kind.frameBytes + i < (stackPtr s).toNat - Kind.frameBytes + (Kind.frameBytes + kind.stackBytes)
  (have := Kind.frameBytes_eq; omega)

theorem Storage.belowRange (h : Storage kind s) :
    MemoryRoutines.WritableRange s (stackPtr s - Kind.frameBytes) Kind.frameBytes := by
  have hw : Writable s (stackPtr s - Kind.frameBytes) Kind.frameBytes := by
    apply memWritable_of_region h.stackBounded h.stackAllocated
      (fun a ha hp ↦ h.stackAvoids a ha (.inr hp))
    · rw [h.belowAddress]
      exact Nat.le_refl _
    · rw [h.belowAddress]
      change _ ≤ (stackPtr s).toNat - Kind.frameBytes + (Kind.frameBytes + kind.stackBytes)
      (have := Kind.frameBytes_eq; omega)
  refine ⟨hw.readable, hw.tables, ?_⟩
  intro i hi hp
  have hc : Component.Covers (.mem (stackPtr s - Kind.frameBytes) (Kind.frameBytes + kind.stackBytes))
      (stackPtr s - Kind.frameBytes + BitVec.ofNat 64 i) := ⟨i, by (have := Kind.frameBytes_eq; omega), rfl⟩
  exact h.stackAvoids _ (h.localCover hc) (.inl hp)

theorem Storage.localWithin (h : Storage kind s) {offset len : Nat}
    (ho : offset + len ≤ kind.stackBytes) {address : BitVec 64}
    (hc : Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 offset) len) address) :
    Component.Covers (.mem (stackPtr s - Kind.frameBytes) (Kind.frameBytes + kind.stackBytes)) address := by
  obtain ⟨i, hi, rfl⟩ := hc
  refine ⟨Kind.frameBytes + offset + i, by (have := Kind.frameBytes_eq; omega), ?_⟩
  apply BitVec.eq_of_toNat_eq
  have hh : (stackPtr s).toNat + kind.stackBytes < 2^32 := h.stackHigh
  have hl := h.stackLow
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.stackAddress (by (have := Kind.frameBytes_eq; omega)),
    BitVec.toNat_add, h.belowAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show Kind.frameBytes + offset + i < 2^64 by (have := Kind.frameBytes_eq; omega))]
  (have := Kind.frameBytes_eq; omega)

theorem Kind.changes_eq_of_rsp (kind : Kind) {s t : RamState}
    (h : stackPtr t = stackPtr s) (hkind : kind ≠ .updateFinalizeCopy) :
    kind.changes t = kind.changes s := by
  cases kind with
  | updateFinalizeCopy => exact False.elim (hkind rfl)
  | digestCopy => simp only [Kind.changes, Kind.localChanges, h]
  | finalizeFixedResetFirst => simp only [Kind.changes, Kind.localChanges, h]
  | finalizeFixedResetSecond => simp only [Kind.changes, Kind.localChanges, h]
  | finalizeIntoResetFirst => simp only [Kind.changes, Kind.localChanges, h]
  | finalizeIntoResetSecond => simp only [Kind.changes, Kind.localChanges, h]
  | finalizeResetFirst => simp only [Kind.changes, Kind.localChanges, h]
  | finalizeResetSecond => simp only [Kind.changes, Kind.localChanges, h]
  | resetCopy => simp only [Kind.changes, Kind.localChanges, h]
  | updateResetCopy => simp only [Kind.changes, Kind.localChanges, h]

theorem agrees_changes {cs : List Component}
    (h : AgreesExcept cs s t)
    (hreg : ∀ c ∈ cs, c.isMem = false → c ∈ kind.changes s)
    (hmem : ∀ x, ∀ c ∈ cs, c.Covers x →
      Component.Covers (.mem (stackPtr s - Kind.frameBytes) (Kind.frameBytes + kind.stackBytes)) x) :
    AgreesExcept (kind.changes s) s t := by
  apply h.widen hreg
  intro x c hc hcover
  exact ⟨_, by simp [Kind.changes, Kind.localChanges], hmem x c hc hcover⟩

theorem hasBytes_of_copy {source destination : Ram} {src dst : BitVec 64} {bytes : ByteArray}
    (h : ∀ i < bytes.size, destination[dst + BitVec.ofNat 64 i]? =
      source[src + BitVec.ofNat 64 i]?)
    (hb : (⟨src.toNat, bytes.size⟩ : MemoryRegion).HasBytes source bytes) :
    (⟨dst.toNat, bytes.size⟩ : MemoryRegion).HasBytes destination bytes := by
  refine ⟨rfl, ?_⟩
  intro i
  have hb' := hb.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb' ⊢
  exact (h i.val i.isLt).trans hb'

theorem pageApart_of_avoids {a : BitVec 64} {len : Nat} (hlen : 0 < len)
    (hlow : a.toNat + len ≤ 2^32)
    (h : ∀ i < len, ¬ InPageTables (a + BitVec.ofNat 64 i)) :
    PageTableEntriesApart a.toNat len := by
  have hat (i : Nat) (hi : i < len) : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by (have := Kind.frameBytes_eq; omega)),
      Nat.mod_eq_of_lt (show a.toNat + i < 2^64 by (have := Kind.frameBytes_eq; omega))]
  constructor
  · refine Classical.byContradiction fun hn ↦ ?_
    let i := if a.toNat ≤ 0x1000 then 0x1000 - a.toNat else 0
    have hi : i < len := by simp only [i]; split <;> (have := Kind.frameBytes_eq; omega)
    apply h i hi
    refine ⟨⟨0x1000, 8⟩, by simp, ?_⟩
    change 0x1000 ≤ (a + BitVec.ofNat 64 i).toNat ∧ (a + BitVec.ofNat 64 i).toNat < 0x1000 + 8
    rw [hat i hi]
    simp only [i]
    split <;> (have := Kind.frameBytes_eq; omega)
  · refine Classical.byContradiction fun hn ↦ ?_
    let i := if a.toNat ≤ 0x2000 then 0x2000 - a.toNat else 0
    have hi : i < len := by simp only [i]; split <;> (have := Kind.frameBytes_eq; omega)
    apply h i hi
    refine ⟨⟨0x2000, 32⟩, by simp, ?_⟩
    change 0x2000 ≤ (a + BitVec.ofNat 64 i).toNat ∧ (a + BitVec.ofNat 64 i).toNat < 0x2000 + 32
    rw [hat i hi]
    simp only [i]
    split <;> (have := Kind.frameBytes_eq; omega)

theorem Storage.pushAddress (h : Storage kind s) :
    (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
  rw [pushAddr, BitVec.toNat_sub_of_le]
  · rfl
  · change 8 ≤ (stackPtr s).toNat
    have := h.stackLow
    (have := Kind.frameBytes_eq; omega)

theorem Storage.pushRange (h : Storage kind s) :
    MemoryRoutines.WritableRange s (pushAddr s) 8 := by
  have he : stackPtr s - Kind.frameBytes + BitVec.ofNat 64 336 = pushAddr s := by
    simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  exact he ▸ h.belowRange.slice 336 8 (by decide)

theorem Storage.pushWritable (h : Storage kind s) : X86Proofs.MemWritable s (pushAddr s) 8 :=
  ⟨h.pushRange.readable.low, h.pushRange.readable.mem,
    pageApart_of_avoids (by decide) h.pushRange.readable.low h.pushRange.tables⟩

theorem Storage.pushPre (h : Storage kind s) {p : BitVec 64} {codeOffset codeLen : Nat}
    (hp : s.RIP = p) (he : p = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hc : codeOffset + codeLen ≤ Extracted.textBytes.size) :
    X86Proofs.PushPre p codeLen s :=
  ⟨hp, h.pushWritable, he ▸ rangeApart_text h.pushRange.code hc⟩

theorem Storage.stackApartPush (h : Storage kind s) {offset len : Nat}
    (he : offset + len ≤ kind.stackBytes) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len (pushAddr s) 8 := by
  have hh : (stackPtr s).toNat + kind.stackBytes < 2^32 := h.stackHigh
  have hl := h.stackLow
  apply RangeApart.of_toNat
  · rw [h.stackAddress (by (have := Kind.frameBytes_eq; omega))]
    (have := Kind.frameBytes_eq; omega)
  · rw [h.pushAddress]
    (have := Kind.frameBytes_eq; omega)
  · rw [h.stackAddress (by (have := Kind.frameBytes_eq; omega)), h.pushAddress]
    (have := Kind.frameBytes_eq; omega)

theorem Storage.x86Writable (h : Storage kind s) (offset len : Nat) (hlen : 0 < len)
    (ho : offset + len ≤ kind.stackBytes) :
    X86Proofs.MemWritable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  have hw := h.stackWritable offset len ho
  exact ⟨hw.low, hw.mem, pageApart_of_avoids hlen hw.low hw.tables⟩

theorem outside_text_range {address : BitVec 64}
    (h : ¬ InProgram address) (lo hi : Nat) (hlo : 0x100000 ≤ lo)
    (hhi : hi ≤ 0x100000 + Extracted.textBytes.size) :
    address.toNat < lo ∨ hi ≤ address.toNat := by
  apply Classical.byContradiction
  intro hn
  have hoff : address.toNat - 0x100000 < Extracted.textBytes.size := by (have := Kind.frameBytes_eq; omega)
  have heq : Extracted.textAddress + BitVec.ofNat 64 (address.toNat - 0x100000) = address := by
    change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (address.toNat - 0x100000) = address
    rw [← BitVec.ofNat_add, show 0x100000 + (address.toNat - 0x100000) = address.toNat by (have := Kind.frameBytes_eq; omega),
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact h (heq ▸ Sha1.Proofs.Compress.Machine.text_address_in_program _ hoff)

end Sha1.Proofs.Buffered.Finalize
