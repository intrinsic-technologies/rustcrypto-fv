import Md5.Proofs.Buffered.Update.Contracts
import Md5.Proofs.MemoryRoutines.Contracts
import Md5.Proofs.Memory.Basic

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem hasBytes_extract {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes memory bytes) (start stop : Nat) :
    (⟨region.start + start, (bytes.extract start stop).size⟩ : MemoryRegion).HasBytes
      memory (bytes.extract start stop) := by
  refine ⟨rfl, ?_⟩
  intro i
  have hi : start + i.val < bytes.size := ByteArray.getElem_extract_aux i.isLt
  simpa only [Nat.add_assoc, ByteArray.getElem_extract] using h.2 ⟨start + i.val, hi⟩

theorem hasBytes_append {memory : Ram} {start : Nat} {a b : ByteArray}
    (ha : (⟨start, a.size⟩ : MemoryRegion).HasBytes memory a)
    (hb : (⟨start + a.size, b.size⟩ : MemoryRegion).HasBytes memory b) :
    (⟨start, (a ++ b).size⟩ : MemoryRegion).HasBytes memory (a ++ b) := by
  refine ⟨rfl, ?_⟩
  intro i
  by_cases hi : i.val < a.size
  · simpa only [ByteArray.getElem_append_left hi] using ha.2 ⟨i.val, hi⟩
  · have hj : i.val - a.size < b.size := by
      have : i.val < a.size + b.size := by
        simpa only [ByteArray.size_append] using i.isLt
      omega
    have he : start + a.size + (i.val - a.size) = start + i.val := by omega
    rw [ByteArray.getElem_append_right (by omega)]
    simpa only [he] using hb.2 ⟨i.val - a.size, hj⟩

theorem allocated_of_hasBytes {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes memory bytes) : region.Allocated memory := by
  intro address ha
  have hi : address.toNat - region.start < bytes.size := by
    have hs := h.1
    change bytes.size = region.size at hs
    rcases ha with ⟨_, _⟩
    omega
  refine ⟨bytes[address.toNat - region.start], ?_⟩
  have he : region.start + (address.toNat - region.start) = address.toNat := by
    exact Nat.add_sub_of_le ha.1
  simpa only [he, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.2 ⟨_, hi⟩

theorem allocated_of_agrees {s t : RamState} {changes : List Component} {region : MemoryRegion}
    (h : AgreesExcept changes s t) (ha : region.Allocated s.external) :
    region.Allocated t.external := by
  intro address hx
  exact Option.isSome_iff_exists.mp (h.grow address (Option.isSome_iff_exists.mpr (ha address hx)))

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

theorem hasBytes_of_memcpy [Bindings] {s t : RamState} {bytes : ByteArray}
    (h : MemoryRoutines.MemcpyResult s t)
    (hlen : (MemoryRoutines.rdx.read s).toNat = bytes.size)
    (hb : (⟨(rsi.read s).toNat, bytes.size⟩ : MemoryRegion).HasBytes s.external bytes) :
    (⟨(rdi.read s).toNat, bytes.size⟩ : MemoryRegion).HasBytes t.external bytes :=
  hasBytes_of_copy (fun i hi ↦ h.copy i (by simpa only [hlen] using hi)) hb

theorem UpdatePre.context_toNat [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    (kind.context s).toNat = (stackPtr s).toNat + kind.contextOffset := by
  have hh := h.stackHigh
  change (stackPtr s).toNat + kind.contextOffset + 88 < 2^32 at hh
  simp only [UpdateKind.context, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show kind.contextOffset < 2^64 by omega),
    Nat.mod_eq_of_lt (show (stackPtr s).toNat + kind.contextOffset < 2^64 by omega)]

theorem UpdatePre.contextBounded [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) : (kind.contextRegion s).Bounded := by
  change (kind.context s).toNat + 88 < userAddressLimit
  rw [h.context_toNat]
  exact h.stackHigh

theorem UpdatePre.scratchBounded [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) : (UpdateKind.scratchRegion s).Bounded := by
  change (stackPtr s).toNat - 320 + 320 < userAddressLimit
  have := h.stackLow
  have := h.stackHigh
  omega

theorem UpdatePre.inputBytes_of_agrees [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdatePre kind boundary message input s)
    (ha : AgreesExcept (kind.changes s) s t) :
    (kind.inputRegion s input).HasBytes t.external input := by
  apply hasBytes_of_memoryWriteFrame
    (UpdateKind.frame ha h.scratchBounded h.contextBounded) h.inputBytes h.inputBounded
  intro region hr
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.inputScratch
  · exact h.inputContext

theorem UpdatePre.contextReadable_of_agrees [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdatePre kind boundary message input s) {changes : List Component}
    (ha : AgreesExcept changes s t) (i n : Nat) (hi : i + n ≤ 88) :
    MemReadable t (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + i)) n := by
  have hh := h.stackHigh
  change (stackPtr s).toNat + kind.contextOffset + 88 < 2^32 at hh
  have he : (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + i)).toNat =
      (stackPtr s).toNat + kind.contextOffset + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show kind.contextOffset + i < 2^64 by omega),
      Nat.mod_eq_of_lt (show (stackPtr s).toNat + (kind.contextOffset + i) < 2^64 by omega),
      Nat.add_assoc]
  apply memReadable_of_allocated (allocated_of_agrees ha h.contextAllocated)
  · rw [he]
    unfold userAddressLimit
    omega
  · change (kind.context s).toNat ≤ _
    rw [he, h.context_toNat]
    omega
  · change _ ≤ (kind.context s).toNat + 88
    rw [he, h.context_toNat]
    omega

theorem UpdatePre.contextReadable [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) (i n : Nat) (hi : i + n ≤ 88) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + i)) n :=
  h.contextReadable_of_agrees (AgreesExcept.refl [] s) i n hi

theorem writableRange_of_region {s : RamState} {region : MemoryRegion}
    {address : BitVec 64} {length : Nat} (hb : region.Bounded)
    (ha : region.Allocated s.external)
    (hav : region.Avoids (fun x ↦ InProgram x ∨ InPageTables x))
    (hstart : region.start ≤ address.toNat)
    (hend : address.toNat + length ≤ region.start + region.size) :
    MemoryRoutines.WritableRange s address length := by
  have hlow : address.toNat + length ≤ 2^32 := by
    change region.start + region.size < 2^32 at hb
    omega
  have hin (i : Nat) (hi : i < length) : region.Contains (address + BitVec.ofNat 64 i).toNat := by
    rw [toNat_add_ofNat _ _ (by omega)]
    exact ⟨by omega, by omega⟩
  exact ⟨memReadable_of_allocated ha hlow hstart hend,
    fun i hi hp ↦ hav _ (hin i hi) (.inr hp),
    fun i hi hp ↦ hav _ (hin i hi) (.inl hp)⟩

theorem UpdatePre.contextWritable_of_agrees [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdatePre kind boundary message input s) {changes : List Component}
    (ha : AgreesExcept changes s t) (i n : Nat) (hi : i + n ≤ 88) :
    MemoryRoutines.WritableRange t
      (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + i)) n := by
  have hh := h.stackHigh
  change (stackPtr s).toNat + kind.contextOffset + 88 < 2^32 at hh
  have he : (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + i)).toNat =
      (stackPtr s).toNat + kind.contextOffset + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show kind.contextOffset + i < 2^64 by omega),
      Nat.mod_eq_of_lt (show (stackPtr s).toNat + (kind.contextOffset + i) < 2^64 by omega),
      Nat.add_assoc]
  apply writableRange_of_region h.contextBounded (allocated_of_agrees ha h.contextAllocated)
    h.contextAvoids
  · change (kind.context s).toNat ≤ _
    rw [he, h.context_toNat]
    omega
  · change _ ≤ (kind.context s).toNat + 88
    rw [he, h.context_toNat]
    omega

theorem UpdatePre.scratchWritable_of_agrees [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdatePre kind boundary message input s) {changes : List Component}
    (ha : AgreesExcept changes s t) (distance n : Nat) (hd : distance ≤ 320) (hn : n ≤ distance) :
    MemoryRoutines.WritableRange t (stackPtr s - BitVec.ofNat 64 distance) n := by
  have hl := h.stackLow
  have he : (stackPtr s - BitVec.ofNat 64 distance).toNat = (stackPtr s).toNat - distance := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show distance < 2^64 by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show distance < 2^64 by omega)]
      omega
  apply writableRange_of_region h.scratchBounded (allocated_of_agrees ha h.scratchAllocated)
    h.scratchAvoids
  · change (stackPtr s).toNat - 320 ≤ _
    rw [he]
    omega
  · change _ ≤ (stackPtr s).toNat - 320 + 320
    rw [he]
    omega

theorem UpdatePre.callSlotWritable_of_agrees [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdatePre kind boundary message input s) {changes : List Component}
    (ha : AgreesExcept changes s t) : Md5.Proofs.Memory.MemWritable t (pushAddr s) 8 := by
  have hw := h.scratchWritable_of_agrees ha 8 8 (by decide) (by decide)
  exact ⟨hw.readable.low, hw.readable.mem, hw.tables⟩

theorem contains_add_of_range {region : MemoryRegion} {address : BitVec 64} {length : Nat}
    (hb : region.Bounded) (hstart : region.start ≤ address.toNat)
    (hend : address.toNat + length ≤ region.start + region.size)
    (i : Nat) (hi : i < length) : region.Contains (address + BitVec.ofNat 64 i).toNat := by
  have hh : region.start + region.size < 2^32 := hb
  rw [toNat_add_ofNat _ _ (by omega)]
  exact ⟨by omega, by omega⟩

theorem rangeApart_of_regions {a b : MemoryRegion} {p q : BitVec 64} {m n : Nat}
    (ha : a.Bounded) (hb : b.Bounded) (hd : a.Disjoint b)
    (hp : a.start ≤ p.toNat) (hpend : p.toNat + m ≤ a.start + a.size)
    (hq : b.start ≤ q.toNat) (hqend : q.toNat + n ≤ b.start + b.size) :
    RangeApart p m q n := by
  intro i hi j hj he
  exact hd _ (contains_add_of_range ha hp hpend i hi)
    (he ▸ contains_add_of_range hb hq hqend j hj)

theorem rangeApart_ordered {p q : BitVec 64} {n : Nat} (h : RangeApart p n q n) :
    p.toNat + n ≤ q.toNat ∨ q.toNat + n ≤ p.toNat := by
  by_cases hpq : p.toNat ≤ q.toNat
  · left
    apply Nat.le_of_not_gt
    intro hn
    apply h (q.toNat - p.toNat) (by omega) 0 (by omega)
    change p + BitVec.ofNat 64 (q.toNat - p.toNat) = q + 0#64
    rw [BitVec.add_zero]
    calc
      p + BitVec.ofNat 64 (q.toNat - p.toNat) =
          BitVec.ofNat 64 (p.toNat + (q.toNat - p.toNat)) := by
        simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = q := by rw [Nat.add_sub_of_le hpq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · right
    apply Nat.le_of_not_gt
    intro hn
    apply h 0 (by omega) (p.toNat - q.toNat) (by omega)
    change p + 0#64 = q + BitVec.ofNat 64 (p.toNat - q.toNat)
    rw [BitVec.add_zero]
    symm
    calc
      q + BitVec.ofNat 64 (p.toNat - q.toNat) =
          BitVec.ofNat 64 (q.toNat + (p.toNat - q.toNat)) := by
        simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = p := by rw [Nat.add_sub_of_le (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Md5.Proofs.Buffered
