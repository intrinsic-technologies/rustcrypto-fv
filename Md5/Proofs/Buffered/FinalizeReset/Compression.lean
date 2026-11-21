import Md5.Proofs.Buffered.FinalizeReset.CompressCall
import Md5.Proofs.Buffered.FinalizeReset.Frame

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem Storage.belowAddress {variant : Variant} {s : RamState} (h : Storage s variant) :
    (stackPtr s - 320).toNat = (stackPtr s).toNat - 320 := by
  have hstackSize := variant.stackBytes_bounds
  rw [BitVec.toNat_sub_of_le h.stackLow]
  rfl

theorem Storage.belowRange {variant : Variant} {s : RamState} (h : Storage s variant) :
    MemoryRoutines.WritableRange s (stackPtr s - 320) 320 := by
  have hstackSize := variant.stackBytes_bounds
  have hw : Memory.MemWritable s (stackPtr s - 320) 320 := by
    apply Memory.MemWritable.of_region (Export.stackBounded h) h.stackAllocated
      (fun a ha hp ↦ h.stackAvoids a ha (.inr hp))
    · rw [h.belowAddress]
      exact Nat.le_refl _
    · rw [h.belowAddress]
      change _ ≤ (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
      omega
  refine ⟨hw.readable, hw.tables, ?_⟩
  intro i hi hp
  apply h.stackAvoids _ ?_ (.inl hp)
  have hh : (stackPtr s).toNat + variant.stackBytes < 2^32 := h.stackHigh
  simp only [BitVec.toNat_add, h.belowAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2^64),
    Nat.mod_eq_of_lt (by omega : (stackPtr s).toNat - 320 + i < 2^64)]
  change (stackPtr s).toNat - 320 ≤ (stackPtr s).toNat - 320 + i ∧
    (stackPtr s).toNat - 320 + i < (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
  omega

namespace Compression

theorem pre {variant : Variant} {s : RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (h : Storage s variant) (hsize : input.size = 64)
    (hdi : s.regValue .rdi = stackPtr s + 0xe8)
    (hsi : s.regValue .rsi = stackPtr s + 0x60)
    (hdx : s.regValue .rdx = 1)
    (hi : (⟨(stackPtr s + 0x60).toNat, 64⟩ : MemoryRegion).HasBytes s.external input)
    (hb : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes s.external
      ⟨buffer.toBytes.toArray⟩) : CompressCall.Pre buffer input s := by
  have hstackSize := variant.stackBytes_bounds
  have hlow := h.stackLow
  have hhigh : (stackPtr s).toNat + variant.stackBytes < 2^32 := h.stackHigh
  have h96 : (stackPtr s + 0x60).toNat = (stackPtr s).toNat + 96 :=
    Export.stackAddress_toNat h 96 (by cases variant <;> decide)
  have h232 : (stackPtr s + 0xe8).toNat = (stackPtr s).toNat + 232 :=
    Export.stackAddress_toNat h 232 (by cases variant <;> decide)
  have hiRegion : Compress.inputRegion s input =
      ⟨(stackPtr s).toNat + 96, 64⟩ := by
    unfold Compress.inputRegion registerRegion
    rw [hsi, hsize, h96]
  have hbRegion : Compress.outputRegion s = ⟨(stackPtr s).toNat + 232, 16⟩ := by
    unfold Compress.outputRegion registerRegion
    rw [hdi, h232]
  refine ⟨?_, ?_, h.stackLow, by change (stackPtr s).toNat < 2^32; omega,
    h.stackAligned, h.belowRange, ?_, ?_, ?_, ?_⟩
  · change (Compress.inputRegion s input).Bounded ∧
      (Compress.inputRegion s input).HasLength (64 * (s.regValue .rdx).toNat) ∧ _
    rw [hiRegion, hdx]
    refine ⟨by change (stackPtr s).toNat + 96 + 64 < 2^32; omega, rfl, ?_⟩
    rwa [h96] at hi
  · change (Compress.outputRegion s).Bounded ∧ _
    rw [hbRegion]
    refine ⟨by change (stackPtr s).toNat + 232 + 16 < 2^32; omega, ?_⟩
    rwa [h232] at hb
  · rw [hiRegion]
    intro address hin hs
    change (stackPtr s).toNat + 96 ≤ address ∧ address < (stackPtr s).toNat + 96 + 64 at hin
    change (stackPtr s).toNat - 320 ≤ address ∧ address < (stackPtr s).toNat - 320 + 320 at hs
    omega
  · rw [hbRegion]
    intro address hin hs
    change (stackPtr s).toNat + 232 ≤ address ∧ address < (stackPtr s).toNat + 232 + 16 at hin
    change (stackPtr s).toNat - 320 ≤ address ∧ address < (stackPtr s).toNat - 320 + 320 at hs
    omega
  · rw [hiRegion, hbRegion]
    intro address hi hb
    change (stackPtr s).toNat + 96 ≤ address ∧ address < (stackPtr s).toNat + 96 + 64 at hi
    change (stackPtr s).toNat + 232 ≤ address ∧ address < (stackPtr s).toNat + 232 + 16 at hb
    omega
  · rw [hbRegion]
    intro address ha hp
    apply h.stackAvoids address ?_ hp
    change (stackPtr s).toNat + 232 ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat + 232 + 16 at ha
    change (stackPtr s).toNat - 320 ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
    omega

local macro "finalize_reset_compress" off:term "," pc:term "," retoff:term "," disp:term "," hp:term "," hr:term "," hc:term "," hout:term "," hip:term : tactic =>
  `(tactic| exact CompressCall.run_of_step
    (Buffered.Stack.call_rel32_effect_step $pc $disp (by decide +kernel)) $hr $hc
    (Block.program_text_slice $hc $off 5 (by decide +kernel)) ⟨$hip, ($hp).pushWritable⟩ $hp
    (by decide +kernel) (by decide) (Or.inl (by decide)) $hout
    (Block.text_address_ne_return $hout $retoff (by decide +kernel)))

theorem first {variant : Variant} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hp : CompressCall.Pre buffer input s) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hout : ¬ InProgram boundary.rip)
    (hip : s.RIP = (variant.address 0x10085e)) :
    ∃ t, CompressCall.Post boundary (variant.address 0x100863) buffer input s t := by
  cases variant with
  | saved => finalize_reset_compress 0x85e, 0x10085e, 0x863, 0x133d, hp, hr, hc, hout, hip
  | direct => finalize_reset_compress 0xf0e, 0x100f0e, 0xf13, 0xc8d, hp, hr, hc, hout, hip

theorem last {variant : Variant} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hp : CompressCall.Pre buffer input s) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hout : ¬ InProgram boundary.rip)
    (hip : s.RIP = (variant.address 0x100917)) :
    ∃ t, CompressCall.Post boundary (variant.address 0x10091c) buffer input s t := by
  cases variant with
  | saved => finalize_reset_compress 0x917, 0x100917, 0x91c, 0x1284, hp, hr, hc, hout, hip
  | direct => finalize_reset_compress 0xfc7, 0x100fc7, 0xfcc, 0xbd4, hp, hr, hc, hout, hip

theorem agrees {s t : RamState} (hdi : s.regValue .rdi = stackPtr s + 0xe8)
    (ha : AgreesExcept (CompressCall.changes s) s t) :
    AgreesExcept (FinalizeReset.changes s) s t := by
  apply ha.mono
  intro c hc
  simp only [CompressCall.changes, hdi, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [FinalizeReset.changes]

end Compression

end Md5.Proofs.Buffered.FinalizeReset
