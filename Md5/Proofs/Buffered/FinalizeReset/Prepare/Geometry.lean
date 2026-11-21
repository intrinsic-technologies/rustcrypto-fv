import Md5.Proofs.Buffered.FinalizeReset.Prepare.Model
import Md5.Proofs.Buffered.FinalizeReset.Frame
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Buffered.FinalizeReset.Normalize
import Md5.Proofs.Buffered.FinalizeReset.Arithmetic
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Buffered.Stack
import Md5.Proofs.Buffered.Update.Rodata

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem position_eq {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre boundary message s variant) :
    position s = BitVec.ofNat 64 (message.size % 64) := by
  have hsize := variant.stackBytes_bounds
  change (((.reg 0 : Operand 64).read s).setWidth 8).setWidth 64 = _
  rw [h.position, BitVec.setWidth_ofNat_of_le (by decide)]
  exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)

theorem copy_rsp {variant : Variant} {s t : RamState} (h : (copyEffect s variant).Holds s t) :
    stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4) (by
  simp [copyEffect, Effect.components, Write.component, Operand.component])

theorem copy_output {variant : Variant} {s t : RamState} (hs : Storage s variant) (h : (copyEffect s variant).Holds s t) :
    outputAddress t = outputAddress s := by
  have hsize := variant.stackBytes_bounds
  unfold outputAddress
  rw [copy_rsp h]
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s + 0xb8 + BitVec.ofNat 64 i]?).getD 0 = _
  congr 1
  apply h.agrees.byte
  intro c hc hcovers
  simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcovers.elim
  all_goals obtain ⟨j, hj, he⟩ := hcovers
  all_goals have hn := congrArg BitVec.toNat he
  all_goals have hh : (stackPtr s).toNat + variant.stackBytes < 2^32 := hs.stackHigh
  · change (((stackPtr s).toNat + 184) % 2^64 + i % 2^64) % 2^64 =
      (((stackPtr s).toNat + 240) % 2^64 + j % 2^64) % 2^64 at hn
    omega
  · change (((stackPtr s).toNat + 184) % 2^64 + i % 2^64) % 2^64 =
      (((stackPtr s).toNat + 232) % 2^64 + j % 2^64) % 2^64 at hn
    omega

theorem copy_storage {variant : Variant} {s t : RamState} (hs : Storage s variant) (h : (copyEffect s variant).Holds s t) :
    Storage t variant := hs.of_agrees h.agrees (copy_rsp h) (copy_output hs h)

theorem stackRange {variant : Variant} {s : RamState} (hs : Storage s variant) (offset len : Nat)
    (he : offset + len ≤ variant.stackBytes) :
    MemoryRoutines.WritableRange s (stackPtr s + BitVec.ofNat 64 offset) len := by
  have hsize := variant.stackBytes_bounds
  have hw := Export.stackWritable hs offset len he
  refine ⟨hw.readable, hw.tables, ?_⟩
  intro i hi hp
  exact hs.stackAvoids _ (Export.stack_cover hs he ⟨i, hi, rfl⟩) (.inl hp)

theorem pushAddress_toNat {variant : Variant} {s : RamState} (hs : Storage s variant) :
    (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
  have hsize := variant.stackBytes_bounds
  rw [pushAddr, BitVec.toNat_sub_of_le]
  · rfl
  · change 8 ≤ (stackPtr s).toNat
    have := hs.stackLow
    omega

theorem pushCover {variant : Variant} {s : RamState} (hs : Storage s variant) {address : BitVec 64}
    (hc : Component.Covers (.mem (pushAddr s) 8) address) :
    (stackRegion s variant).Contains address.toNat := by
  have hsize := variant.stackBytes_bounds
  obtain ⟨i, hi, rfl⟩ := hc
  have hh : (stackPtr s).toNat + variant.stackBytes < 2^32 := hs.stackHigh
  have hl := hs.stackLow
  rw [toNat_add_ofNat _ _ (by rw [pushAddress_toNat hs]; omega), pushAddress_toNat hs]
  change (stackPtr s).toNat - 320 ≤ _ ∧ _ < (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
  omega

theorem pushRange {variant : Variant} {s : RamState} (hs : Storage s variant) :
    MemoryRoutines.WritableRange s (pushAddr s) 8 := by
  have hsize := variant.stackBytes_bounds
  have hw : Memory.MemWritable s (pushAddr s) 8 := by
    apply Memory.MemWritable.of_region (Export.stackBounded hs) hs.stackAllocated
      (fun a ha hp ↦ hs.stackAvoids a ha (.inr hp))
    · rw [pushAddress_toNat hs]
      change (stackPtr s).toNat - 320 ≤ (stackPtr s).toNat - 8
      omega
    · rw [pushAddress_toNat hs]
      change _ ≤ (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
      have := hs.stackLow
      omega
  refine ⟨hw.readable, hw.tables, ?_⟩
  intro i hi hp
  exact hs.stackAvoids _ (pushCover hs ⟨i, hi, rfl⟩) (.inl hp)

theorem setup_memset_pre {variant : Variant} {s t : RamState} {n : Nat} (hs : Storage s variant)
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (hdf : DirectionFlagClear s.RFLAGS) (he : (setupEffect s variant).Holds s t) :
    MemsetSitePre (variant.address 0x1007e6) t := by
  have hsize := variant.stackBytes_bounds
  have hsp : stackPtr t = stackPtr s := he.agrees.read (n := 64) (r := 4) (by
    simp [setupEffect, Effect.components, Write.component, Operand.component])
  have hdi : rdi.read t = stackPtr s + BitVec.ofNat 64 (n + 9) := by
    rw [he.writes.2.2.1, hp]
    change stackPtr s + BitVec.ofNat 64 n + BitVec.ofNat 64 9 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hdx : MemoryRoutines.rdx.read t = BitVec.ofNat 64 (63 - n) := by
    rw [he.writes.2.2.2.2, hp, remainingBytes n hn]
  have hlen : (MemoryRoutines.rdx.read t).toNat = 63 - n := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpush : pushAddr t = pushAddr s := by simp only [pushAddr, hsp]
  have hslot := (pushRange hs).of_agrees he.agrees
  refine ⟨(he.agrees.directionFlagClear (by simp [setupEffect, Effect.components]) ⟨hdf⟩).df,
    ?_, ?_, ?_, ?_, by cases variant <;> decide,
    Or.inl (by cases variant <;> decide)⟩
  · rw [hdi, hlen]
    exact (stackRange hs (n + 9) (63 - n) (by omega)).of_agrees he.agrees
  · rw [hpush]; exact hslot.readable
  · rw [hpush]; exact hslot.code
  · rw [hdi, hlen, hpush]
    apply RangeApart.of_toNat
    · rw [Export.stackAddress_toNat hs _ (by omega)]
      have hh : (stackPtr s).toNat + variant.stackBytes < 2^32 := hs.stackHigh
      omega
    · rw [pushAddress_toNat hs]
      have hh : (stackPtr s).toNat + variant.stackBytes < 2^32 := hs.stackHigh
      omega
    · rw [Export.stackAddress_toNat hs _ (by omega), pushAddress_toNat hs]
      have := hs.stackLow
      omega


end Md5.Proofs.Buffered.FinalizeReset.Prepare
