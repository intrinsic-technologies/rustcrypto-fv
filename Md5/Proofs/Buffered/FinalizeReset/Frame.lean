import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Buffered.Stores.Program

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem agrees_rsp {s t : RamState} (h : AgreesExcept (changes s) s t) :
    stackPtr t = stackPtr s := h.read (n := 64) (r := 4) (by simp [changes])

theorem agrees_saved_byte {variant : Variant} {s t : RamState} (hs : Storage s variant)
    (h : AgreesExcept (changes s) s t) (offset : Nat)
    (hlo : 160 ≤ offset) (hhi : offset < 232) :
    t.external[stackPtr s + BitVec.ofNat 64 offset]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset]? := by
  have hsize := variant.stackBytes_bounds
  have hspLow := hs.stackLow
  have hspHigh : (stackPtr s).toNat + variant.stackBytes < 2^32 := hs.stackHigh
  apply h.byte
  intro c hc hcover
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · obtain ⟨i, hi, he⟩ := hcover
    have hn := congrArg BitVec.toNat he
    have hsub : (stackPtr s - 320).toNat = (stackPtr s).toNat - 320 :=
      BitVec.toNat_sub_of_le hs.stackLow
    rw [Export.stackAddress_toNat hs offset (by omega)] at hn
    simp only [BitVec.toNat_add, hsub, BitVec.toNat_ofNat] at hn
    omega
  · obtain ⟨i, hi, he⟩ := hcover
    have hn := congrArg BitVec.toNat he
    rw [Export.stackAddress_toNat hs offset (by omega)] at hn
    change (stackPtr s).toNat + offset =
      (((stackPtr s).toNat + 8) % 2^64 + i % 2^64) % 2^64 at hn
    omega
  · obtain ⟨i, hi, he⟩ := hcover
    have hn := congrArg BitVec.toNat he
    rw [Export.stackAddress_toNat hs offset (by omega)] at hn
    change (stackPtr s).toNat + offset =
      (((stackPtr s).toNat + 232) % 2^64 + i % 2^64) % 2^64 at hn
    omega
  · obtain ⟨i, hi, he⟩ := hcover
    have hn := congrArg BitVec.toNat he
    rw [Export.stackAddress_toNat hs offset (by omega)] at hn
    change (stackPtr s).toNat + offset =
      (((stackPtr s).toNat + 296) % 2^64 + i % 2^64) % 2^64 at hn
    omega
  · exact hs.outputStack _ (Export.output_cover hs (offset := 0) (len := 16)
      (by decide) (by simpa using hcover))
      (Export.stackContains hs offset (by omega))

theorem agrees_saved_read {variant : Variant} {s t : RamState} (hs : Storage s variant)
    (h : AgreesExcept (changes s) s t) (offset n : Nat)
    (hlo : 160 ≤ offset) (hhi : offset + n / 8 ≤ 232) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand n).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand n).read s := by
  have hsize := variant.stackBytes_bounds
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, agrees_saved_byte hs h _ (by omega) (by omega)]
  rfl

theorem agrees_outputAddress {variant : Variant} {s t : RamState} (hs : Storage s variant)
    (h : AgreesExcept (changes s) s t) : outputAddress t = outputAddress s := by
  have hsize := variant.stackBytes_bounds
  unfold outputAddress
  rw [agrees_rsp h]
  exact agrees_saved_read hs h 184 64 (by decide) (by decide)

theorem Storage.of_agrees {variant : Variant} {s t : RamState} {cs : List Component} (hs : Storage s variant)
    (ha : AgreesExcept cs s t) (hsp : stackPtr t = stackPtr s)
    (hout : outputAddress t = outputAddress s) : Storage t variant := by
  have hsize := variant.stackBytes_bounds
  have hstack : FinalizeReset.stackRegion t variant = FinalizeReset.stackRegion s variant :=
    congrArg (fun rsp : BitVec 64 ↦ (⟨rsp.toNat - 320, (320 + variant.stackBytes)⟩ : MemoryRegion)) hsp
  have houtput : outputRegion t = outputRegion s := congrArg (fun a : BitVec 64 ↦
    (⟨a.toNat, 16⟩ : MemoryRegion)) hout
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp]; exact hs.stackLow
  · rw [hsp]; exact hs.stackHigh
  · rw [hsp]; exact hs.stackAligned
  · rw [hstack]
    intro a haS
    exact Option.isSome_iff_exists.mp (ha.grow a
      (Option.isSome_iff_exists.mpr (hs.stackAllocated a haS)))
  · rw [hstack]; exact hs.stackAvoids
  · rw [houtput]; exact hs.outputBounded
  · rw [houtput]
    intro a haS
    exact Option.isSome_iff_exists.mp (ha.grow a
      (Option.isSome_iff_exists.mpr (hs.outputAllocated a haS)))
  · rw [houtput]; exact hs.outputAvoids
  · rw [houtput, hstack]; exact hs.outputStack

theorem agrees_storage {variant : Variant} {s t : RamState} (hs : Storage s variant)
    (h : AgreesExcept (changes s) s t) : Storage t variant :=
  hs.of_agrees h (agrees_rsp h) (agrees_outputAddress hs h)

theorem changes_eq {s t : RamState}
    (hsp : stackPtr t = stackPtr s) (hout : outputAddress t = outputAddress s) :
    changes t = changes s := by
  simp only [changes, hsp, hout]

theorem agrees_trans {variant : Variant} {s u t : RamState} (hs : Storage s variant)
    (hu : AgreesExcept (changes s) s u) (ht : AgreesExcept (changes u) u t) :
    AgreesExcept (changes s) s t := by
  have hsize := variant.stackBytes_bounds
  rw [changes_eq (agrees_rsp hu) (agrees_outputAddress hs hu)] at ht
  exact (hu.trans ht).mono (by simp)

theorem Post.prepend {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s u t : RamState} {fuel : Nat} (h : Post boundary message u t variant)
    (hs : Storage s variant) (ha : Advances boundary fuel s u)
    (hf : AgreesExcept (changes s) s u) : Post boundary message s t variant := by
  have hsize := variant.stackBytes_bounds
  obtain ⟨n, hn⟩ := h.advances
  refine ⟨⟨fuel + n, ha.trans hn⟩, h.ready, h.code, h.rip, ?_, ?_, agrees_trans hs hf h.agrees⟩
  · simpa only [context, agrees_rsp hf] using h.absorbed
  · simpa only [outputRegion, agrees_outputAddress hs hf] using h.digest

end Md5.Proofs.Buffered.FinalizeReset
