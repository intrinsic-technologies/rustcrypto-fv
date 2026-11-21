import Md5.Proofs.Buffered.DigestPrepare.Contracts
import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {input : ByteArray}

theorem Frame.finish (h : Frame initial boundary s) (hStride : UnitStringStride bindings)
    (hRip : s.RIP = 0x1000cf) (hAbsorbed : Absorbed (Finalize.Kind.digest.context s) input s)
    (hSize : input.size < 2^64) : DigestPrepared initial boundary input s :=
  ⟨⟨⟨h.stackLow, h.stackHigh, h.stackAligned, h.stackAllocated, h.stackAvoids⟩,
    h.ready, h.code, hStride, h.df, hRip, h.boundaryOutside, hAbsorbed, hSize,
    fun _ ↦ h.statePointer⟩, h.stack, h.output, h.savedRbx, h.savedR12, h.savedR14,
    h.savedR15, h.returnSlot, h.agrees⟩

theorem Frame.stackNat (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) :
    (stackPtr s).toNat = (stackPtr initial).toNat - 296 := by
  rw [h.stack, BitVec.toNat_sub_of_le]
  · rfl
  · have hn : 616 ≤ (stackPtr initial).toNat := hs.2.2.1
    change 296 ≤ (stackPtr initial).toNat
    omega

theorem Frame.address (h : Frame initial boundary s) {offset : Nat} (ho : offset ≤ 264) :
    (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
  have hh : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
  exact toNat_add_ofNat _ _ (by omega)

theorem Frame.bounded (h : Frame initial boundary s) :
    (Finalize.Kind.digest.stackRegion s).Bounded := by
  have hl := h.stackLow
  have hh := h.stackHigh
  change (stackPtr s).toNat - 320 + (320 + 264) < userAddressLimit
  omega

theorem Frame.writable (h : Frame initial boundary s) {changes : List Component}
    (ha : AgreesExcept changes s t) (offset length : Nat) (ho : offset + length ≤ 264) :
    MemoryRoutines.WritableRange t (stackPtr s + BitVec.ofNat 64 offset) length := by
  apply writableRange_of_region h.bounded (allocated_of_agrees ha h.stackAllocated) h.stackAvoids
  · rw [h.address (by omega)]
    change (stackPtr s).toNat - 320 ≤ _
    omega
  · rw [h.address (by omega)]
    change _ ≤ (stackPtr s).toNat - 320 + (320 + 264)
    have := h.stackLow
    omega

theorem Frame.scratchWritable (h : Frame initial boundary s) {changes : List Component}
    (ha : AgreesExcept changes s t) (distance length : Nat) (hd : distance ≤ 320)
    (hl : length ≤ distance) :
    MemoryRoutines.WritableRange t (stackPtr s - BitVec.ofNat 64 distance) length := by
  have hlow := h.stackLow
  have hn : (stackPtr s - BitVec.ofNat 64 distance).toNat =
      (stackPtr s).toNat - distance := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  apply writableRange_of_region h.bounded (allocated_of_agrees ha h.stackAllocated) h.stackAvoids
  · rw [hn]
    change (stackPtr s).toNat - 320 ≤ _
    omega
  · rw [hn]
    change _ ≤ (stackPtr s).toNat - 320 + (320 + 264)
    omega

set_option maxRecDepth 2048 in
theorem Frame.stackSubset (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) {address : Nat}
    (ha : (Finalize.Kind.digest.stackRegion s).Contains address) :
    (Stack.region initial Digest.minStackBytes).Contains address := by
  change (stackPtr s).toNat - 320 ≤ address ∧
    address < (stackPtr s).toNat - 320 + (320 + 264) at ha
  rw [h.stackNat hs] at ha
  have hl : 616 ≤ (stackPtr initial).toNat := hs.2.2.1
  change (stackPtr initial).toNat - 616 ≤ address ∧
    address < (stackPtr initial).toNat - 616 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 616))
  omega

set_option maxRecDepth 4096 in
theorem Frame.preserve (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) {changes : List Component}
    (ha : AgreesExcept changes s t) (ht : ReadyToStep t)
    (hc : CodeIn Extracted.programImage t)
    (hreg : ∀ c ∈ changes, c.isMem = false → c ∈ digestPreparationChanges initial)
    (hmem : ∀ c ∈ changes, ∀ address, c.Covers address →
      (Finalize.Kind.digest.stackRegion s).Contains address.toNat)
    (hrsp : stackPtr t = stackPtr s) (hrbx : t.regValue .rbx = s.regValue .rbx)
    (hr14 : (Operand.reg 14 : Operand 64).read t = (Operand.reg 14 : Operand 64).read s) :
    Frame initial boundary t := by
  have hsave (offset : Nat) (hl : 264 ≤ offset) (hh : offset + 8 ≤ 304) :
      (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
    rw [hrsp]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
    apply ha.byte
    intro c hc hcov
    have hx := hmem c hc _ hcov
    have hb : (stackPtr initial).toNat - 616 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 616)) < 2^32 := hs.1
    have hn := h.stackNat hs
    have hlow : 616 ≤ (stackPtr initial).toNat := hs.2.2.1
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by omega)] at hx
    change (stackPtr s).toNat - 320 ≤ _ ∧
      _ < (stackPtr s).toNat - 320 + (320 + 264) at hx
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
    h.boundaryOutside,
    hrsp.trans h.stack, hrsp ▸ h.stackLow, hrsp ▸ h.stackHigh, hrsp ▸ h.stackAligned,
    ?_, ?_, ?_, hrbx.trans h.output,
    (hsave 264 (by decide) (by decide)).trans h.savedRbx,
    (hsave 272 (by decide) (by decide)).trans h.savedR12,
    (hsave 280 (by decide) (by decide)).trans h.savedR14,
    (hsave 288 (by decide) (by decide)).trans h.savedR15,
    (hsave 296 (by decide) (by decide)).trans h.returnSlot,
    (h.agrees.trans hag).mono (by simp)⟩
  · change (⟨(stackPtr t).toNat - 320, 584⟩ : MemoryRegion).Allocated t.external
    rw [hrsp]
    exact allocated_of_agrees ha h.stackAllocated
  · change (⟨(stackPtr t).toNat - 320, 584⟩ : MemoryRegion).Avoids _
    rw [hrsp]
    exact h.stackAvoids
  · rw [hr14, h.statePointer, hrsp]

end Md5.Proofs.Buffered.DigestPrepare
