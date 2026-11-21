import Sha1.Proofs.Buffered.DigestPrepare.Contracts
import Sha1.Proofs.Buffered.Finalize.Geometry
import Sha1.Proofs.MemoryRoutines.Contracts

namespace Sha1.Proofs.Buffered.DigestPrepare

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem allocated_of_agrees {s t : RamState} {changes : List Component} {region : MemoryRegion}
    (h : AgreesExcept changes s t) (ha : region.Allocated s.external) :
    region.Allocated t.external := by
  intro address hx
  exact Option.isSome_iff_exists.mp (h.grow address (Option.isSome_iff_exists.mpr (ha address hx)))

theorem memReadable_of_allocated {s : RamState} {region : MemoryRegion}
    {address : BitVec 64} {length : Nat} (h : region.Allocated s.external)
    (hlow : address.toNat + length ≤ 2^32)
    (hstart : region.start ≤ address.toNat)
    (hend : address.toNat + length ≤ region.start + region.size) :
    MemReadable s address length := by
  refine ⟨hlow, fun i hi ↦ ?_⟩
  have hc : region.Contains (address + BitVec.ofNat 64 i).toNat := by
    rw [toNat_add_ofNat _ _ (by omega)]
    exact ⟨by omega, by omega⟩
  exact Option.isSome_iff_exists.mpr (h _ hc)

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

theorem contains_of_mem_covers {region : MemoryRegion} (hBounded : region.Bounded)
    {address : BitVec 64}
    (hCovers : Component.Covers (.mem (BitVec.ofNat 64 region.start) region.size) address) :
    region.Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hCovers
  have hb : region.start + region.size < 2^32 := hBounded
  rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega, by omega⟩

theorem stack_bounds {initial : RamState} (hs : Stack.Valid initial Digest.minStackBytes) :
    656 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 ∧
      (stackPtr initial).toNat % 16 = 8 := by
  obtain ⟨hb, -, hn, ha⟩ := hs
  have hn' : 656 ≤ (stackPtr initial).toNat := hn
  change (stackPtr initial).toNat - 656 +
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 656)) < 2^32 at hb
  change ((stackPtr initial).toNat) % 16 = 8 at ha
  refine ⟨hn', by omega, ha⟩

theorem stack_region_contains {initial : RamState} (hs : Stack.Valid initial Digest.minStackBytes) {address : Nat}
    (hl : (stackPtr initial).toNat - 656 ≤ address) (hh : address < (stackPtr initial).toNat + 8) :
    (Stack.region initial Digest.minStackBytes).Contains address := by
  have hb := stack_bounds hs
  change (stackPtr initial).toNat - 656 ≤ address ∧
    address < (stackPtr initial).toNat - 656 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 656))
  omega

variable [bindings : Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {input : ByteArray}

theorem Frame.stackNat (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) :
    (stackPtr s).toNat = (stackPtr initial).toNat - 312 := by
  have hb := stack_bounds hs
  rw [h.stack, BitVec.toNat_sub_of_le]
  · rfl
  · change 312 ≤ (stackPtr initial).toNat
    omega

theorem Frame.address (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) {offset : Nat} (ho : offset ≤ 320) :
    (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
  have hb := stack_bounds hs
  have hn := h.stackNat hs
  exact toNat_add_ofNat _ _ (by omega)

theorem Frame.stackSubset (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) {address : Nat}
    (ha : (Finalize.Kind.digestCopy.stackRegion s).Contains address) :
    (Stack.region initial Digest.minStackBytes).Contains address := by
  change (stackPtr s).toNat - Finalize.Kind.frameBytes ≤ address ∧
    address < (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118) at ha
  rw [h.stackNat hs] at ha
  have hb := stack_bounds hs
  have hfb := Finalize.Kind.frameBytes_eq
  exact stack_region_contains hs (by omega) (by omega)

theorem Frame.storage (h : Frame initial boundary s)
    (hCall : Digest.ValidCall bindings initial input) :
    Finalize.Storage .digestCopy s := by
  have hs := hCall.stackAvailable
  have hb := stack_bounds hs
  have hn := h.stackNat hs
  have hfb := Finalize.Kind.frameBytes_eq
  refine ⟨by omega, ?_, by omega, ?_, ?_⟩
  · change (stackPtr s).toNat + 0x118 < 2^32
    omega
  · intro address ha
    exact Option.isSome_iff_exists.mp (h.agrees.grow address
      (Option.isSome_iff_exists.mpr (hs.2.1 address (h.stackSubset hs ha))))
  · intro address ha
    exact (hCall.separation.2 _ (by simp)).2 address (h.stackSubset hs ha)

theorem Frame.bounded (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) :
    (Finalize.Kind.digestCopy.stackRegion s).Bounded := by
  have hb := stack_bounds hs
  have hn := h.stackNat hs
  have hfb := Finalize.Kind.frameBytes_eq
  change (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118) < userAddressLimit
  change _ < 2^32
  omega

theorem Frame.writable (h : Frame initial boundary s)
    (hCall : Digest.ValidCall bindings initial input) {changes : List Component}
    (ha : AgreesExcept changes s t) (offset length : Nat) (ho : offset + length ≤ 0x118) :
    MemoryRoutines.WritableRange t (stackPtr s + BitVec.ofNat 64 offset) length := by
  have hst := h.storage hCall
  have hs := hCall.stackAvailable
  apply writableRange_of_region (h.bounded hs) (allocated_of_agrees ha hst.stackAllocated)
    hst.stackAvoids
  · rw [h.address hs (by omega)]
    change (stackPtr s).toNat - Finalize.Kind.frameBytes ≤ _
    omega
  · rw [h.address hs (by omega)]
    change _ ≤ (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118)
    have := hst.stackLow
    omega

theorem Frame.scratchWritable (h : Frame initial boundary s)
    (hCall : Digest.ValidCall bindings initial input) {changes : List Component}
    (ha : AgreesExcept changes s t) (distance length : Nat)
    (hd : distance ≤ Finalize.Kind.frameBytes)
    (hl : length ≤ distance) :
    MemoryRoutines.WritableRange t (stackPtr s - BitVec.ofNat 64 distance) length := by
  have hst := h.storage hCall
  have hs := hCall.stackAvailable
  have hlow := hst.stackLow
  have hn : (stackPtr s - BitVec.ofNat 64 distance).toNat =
      (stackPtr s).toNat - distance := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  apply writableRange_of_region (h.bounded hs) (allocated_of_agrees ha hst.stackAllocated)
    hst.stackAvoids
  · rw [hn]
    change (stackPtr s).toNat - Finalize.Kind.frameBytes ≤ _
    omega
  · rw [hn]
    change _ ≤ (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118)
    omega

set_option maxRecDepth 4096 in
theorem Frame.preserve (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) {changes : List Component}
    (ha : AgreesExcept changes s t) (ht : ReadyToStep t)
    (hc : CodeIn Extracted.programImage t)
    (hreg : ∀ c ∈ changes, c.isMem = false → c ∈ digestPreparationChanges initial)
    (hmem : ∀ c ∈ changes, ∀ address, c.Covers address →
      (Finalize.Kind.digestCopy.stackRegion s).Contains address.toNat)
    (hrsp : stackPtr t = stackPtr s) (hrbx : t.regValue .rbx = s.regValue .rbx)
    (hr14 : (Operand.reg 14 : Operand 64).read t = (Operand.reg 14 : Operand 64).read s) :
    Frame initial boundary t := by
  have hb := stack_bounds hs
  have hn := h.stackNat hs
  have hsave (offset : Nat) (hl : 0x118 ≤ offset) (hh : offset + 8 ≤ 320) :
      (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
    rw [hrsp]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
    apply ha.byte
    intro c hc hcov
    have hx := hmem c hc _ hcov
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by omega)] at hx
    change (stackPtr s).toNat - Finalize.Kind.frameBytes ≤ _ ∧
      _ < (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118) at hx
    have hfb := Finalize.Kind.frameBytes_eq
    omega
  have hag : AgreesExcept (digestPreparationChanges initial) s t := by
    apply ha.widen hreg
    intro address c hc hcov
    have hx := h.stackSubset hs (hmem c hc address hcov)
    refine ⟨.mem (BitVec.ofNat 64 (Stack.region initial Digest.minStackBytes).start)
      (Stack.region initial Digest.minStackBytes).size, by simp [digestPreparationChanges],
      address.toNat - (Stack.region initial Digest.minStackBytes).start, ?_, ?_⟩
    · exact Nat.sub_lt_left_of_lt_add hx.1 hx.2
    · rw [← BitVec.ofNat_add, Nat.add_sub_of_le hx.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨ht, hc, hag.directionFlagClear (by simp [digestPreparationChanges]) h.df,
    h.boundaryOutside, hrsp.trans h.stack, ?_, hrbx.trans h.output,
    (hsave 280 (by decide) (by decide)).trans h.savedRbx,
    (hsave 288 (by decide) (by decide)).trans h.savedR12,
    (hsave 296 (by decide) (by decide)).trans h.savedR14,
    (hsave 304 (by decide) (by decide)).trans h.savedR15,
    (hsave 312 (by decide) (by decide)).trans h.returnSlot,
    (h.agrees.trans hag).mono (by simp)⟩
  rw [hr14, h.statePointer, hrsp]

theorem Frame.finish (h : Frame initial boundary s)
    (hCall : Digest.ValidCall bindings initial input) (hStride : UnitStringStride bindings)
    (hRip : s.RIP = 0x1000da) (hAbsorbed : Absorbed (stackPtr s + 0xb8) input s)
    (hSize : input.size < 2^64) : DigestPrepared initial boundary input s :=
  ⟨h, ⟨h.storage hCall, h.ready, h.code, hStride, h.df, hRip, h.boundaryOutside, hAbsorbed,
    hSize⟩⟩

end Sha1.Proofs.Buffered.DigestPrepare
