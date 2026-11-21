import Md5.Proofs.Buffered.Update.Slices.Full.Prepare.Copy
import Md5.Proofs.Buffered.Update.Slices.Full.Prepare.Calls
import Md5.Proofs.Buffered.Update.Slices.Full.Prepare.Memory
import Md5.Proofs.Buffered.Update.Slices.Full.Machine.Branch

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

set_option maxRecDepth 4096 in
theorem filled_ready {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hp : Prepared variant boundary s u) (hfull : 64 - message.size % 64 ≤ input.size)
    (hpos : message.size % 64 ≠ 0) :
    ∃ v, BatchReady variant boundary input s (64 - message.size % 64)
      (Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (updateBlock message input))) (message.size / 64 + 1) v := by
  obtain ⟨f₁, a, hsa, hra, hca, hea⟩ := fill_ready h hp hfull hpos
  have hasp : stackPtr a = stackPtr s := hea.agrees.read (n := 64) (r := 4)
    (by simp [fillReadyEffect, Effect.components])
  have hadi : rdi.read a = (kind variant).context s + BitVec.ofNat 64 (message.size % 64) := by
    rw [hea.writes.2.2.2.2.1, position_eq h]
    rw [kind_context]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + 192 =
      stackPtr s + 192 + BitVec.ofNat 64 (message.size % 64)
    ac_rfl
  have hasi : rsi.read a = (Operand.reg 14 : Operand 64).read s := hea.writes.2.2.2.2.2
  have hadx : MemoryRoutines.rdx.read a = BitVec.ofNat 64 (64 - message.size % 64) :=
    hea.writes.2.1.trans (capacity_eq h)
  have hmem : a.external = s.external := hea.agrees.external
    (by simp [fillReadyEffect, Effect.components, Component.Covers])
  have hsaAg : AgreesExcept ((kind variant).changes s) s a := hea.agrees.mono (by
    intro c hc
    simp only [fillReadyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters])
  obtain ⟨b, hb⟩ := fill_copy_call h hea.agrees hasp hea.rip hra hca hadi hasi hadx hfull
    (by simp [fillReadyEffect, Effect.components])
  obtain ⟨hib, hbb, hcountb⟩ := filledBlock_of_copy h hb hmem hasp hadi (by simpa only [kind_inputRegister] using hasi) hadx hfull
  have hab := hb.toCallSiteResult.update_agrees h hasp hadi (by
    rw [hadx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 64 - message.size % 64 < 2^64 by omega)]
    omega)
  have hsb : AgreesExcept ((kind variant).changes s) s b := (hsaAg.trans hab).mono (by simp)
  have hbsp : stackPtr b = stackPtr s := hb.rsp.trans hasp
  obtain ⟨c, hbc, hrc, hcc, hec⟩ := fill_increment h hsb hbsp hb.rip hb.ready hb.code
  have hsc : AgreesExcept ((kind variant).changes s) s c :=
    (hsb.trans (fill_increment_agrees hbsp hec)).mono (by simp)
  have hcsp : stackPtr c = stackPtr s := hsc.read (n := 64) (r := 4)
    (by cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters])
  have hic : (⟨((kind variant).context s).toNat, 64⟩ : MemoryRegion).HasBytes
      c.external (updateBlock message input) := by
    have hh := fill_increment_preserves h hbsp hec (offset := 0)
      (bytes := updateBlock message input) (by rw [size_updateBlock message input hfull]; decide)
      (by simpa only [Nat.add_zero, size_updateBlock message input hfull] using hib)
    simpa only [Nat.add_zero, size_updateBlock message input hfull] using hh
  have hbcBytes : (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      c.external ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
    have hs : (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray).size = 16 := by
      simp only [ByteArray.size, Vector.size_toArray]
    have hh := fill_increment_preserves h hbsp hec (offset := 64)
      (bytes := ⟨(absorbedBuffer message).toBytes.toArray⟩) (by rw [hs]; decide)
      (by simpa only [hs] using hbb)
    simpa only [hs] using hh
  have hbase : stackPtr b + 272 = (kind variant).context s + 80 := by
    rw [hbsp]
    rw [kind_context]
    change stackPtr s + 272 = stackPtr s + 192 + 80
    rw [BitVec.add_assoc]
    rfl
  have hcountc : (Operand.mem ((kind variant).context s + 80) : Operand 64).read c =
      BitVec.ofNat 64 (message.size / 64 + 1) := by
    have hw := fill_increment_write hec
    rw [hbase, hcountb] at hw
    exact hw.trans (BitVec.ofNat_add ..).symm
  have hbytes : CodeIn (codeRange (pc variant 0x100397) partialCompressBytes) c :=
    by
      cases variant with
      | false => exact program_text_slice hcc 0x397 21 (by decide +kernel)
      | true => exact program_text_slice hcc 0x1947 21 (by decide +kernel)
  obtain ⟨f₃, d, hcd, hrd, _, hed⟩ :=
    partial_compress_prepare boundary h.boundaryOutside c hrc hbytes (by cases variant <;> exact hec.rip)
  have hnoMem : ∀ comp ∈ (partialCompressEffect variant c).components, ∀ x, ¬ comp.Covers x := by
    simp [partialCompressEffect, Effect.components, Component.Covers]
  have hcdMem : d.external = c.external := hed.agrees.external hnoMem
  have hdc : CodeIn Extracted.programImage d :=
    hed.codeIn (Effect.Avoids.of_noMem hnoMem _) hcc
  have hcdAg : AgreesExcept ((kind variant).changes s) c d := hed.agrees.mono (by
    simp [partialCompressEffect, Effect.components, UpdateKind.changes])
  have hsd : AgreesExcept ((kind variant).changes s) s d := (hsc.trans hcdAg).mono (by simp)
  have hdsp : stackPtr d = stackPtr s := hsd.read (n := 64) (r := 4)
    (by cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters])
  have hddi : d.regValue .rdi = (kind variant).context s + 64 := by
    have hw := hed.writes.2.1
    change d.regValue .rdi = stackPtr c + 256 at hw
    rw [hw, hcsp]
    rw [kind_context]
    change stackPtr s + 256 = stackPtr s + 192 + 64
    rw [BitVec.add_assoc]
    rfl
  have hdsi : d.regValue .rsi = (kind variant).context s := by
    change (Operand.reg 6 : Operand 64).read d = (kind variant).context s
    simpa only [kind_context] using hed.writes.2.2.trans (congrArg (fun x ↦ x + 192) hcsp)
  have hddx : d.regValue .rdx = 1 := hed.writes.1
  obtain ⟨e, he⟩ := compress_filled_context h hsd hdsp hed.rip hrd hdc hddi hdsi hddx
    hfull (hcdMem ▸ hic) (hcdMem ▸ hbcBytes)
  have hse : AgreesExcept ((kind variant).changes s) s e :=
    (hsd.trans (he.update_agrees h hdsp hddi)).mono (by simp)
  have hesp : stackPtr e = stackPtr s := he.rsp.trans hdsp
  have hbe : (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      e.external ⟨(Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (updateBlock message input))).toBytes.toArray⟩ := by
    rw [← h.compressionOutputRegion hddi]
    exact he.output
  have hcounte : (Operand.mem ((kind variant).context s + 80) : Operand 64).read e =
      BitVec.ofNat 64 (message.size / 64 + 1) := by
    rw [he.update_counter h hdsp hddi]
    change memLoad d.external _ 64 = _
    rw [hcdMem]
    exact hcountc
  obtain ⟨f, hef, hrf, hcf, heclear⟩ := fill_clear h hse hesp he.rip he.ready he.code
  obtain ⟨hbf, hcountf⟩ := fill_clear_preserves h hesp heclear hbe
  have hsf : AgreesExcept ((kind variant).changes s) s f :=
    (hse.trans (fill_clear_agrees hesp heclear)).mono (by simp)
  have hpath := (((hb.agrees.trans hec.agrees).trans hed.agrees).trans he.agrees).trans
    heclear.agrees
  have hf3 : (Operand.reg 3 : Operand 64).read f =
      (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 (64 - message.size % 64) := by
    rw [hpath.read (by
      simp only [fillIncrementEffect_components, fillClearEffect_components]
      simp [callSiteChanges, partialCompressEffect, Effect.components,
        FinalizeReset.CompressCall.changes])]
    exact hea.writes.2.2.2.1.trans (by rw [capacity_eq h])
  have hf5 : (Operand.reg 5 : Operand 64).read f =
      BitVec.ofNat 64 (input.size - (64 - message.size % 64)) := by
    rw [hpath.read (by
      simp only [fillIncrementEffect_components, fillClearEffect_components]
      simp [callSiteChanges, partialCompressEffect, Effect.components,
        FinalizeReset.CompressCall.changes]), hea.writes.2.2.1, capacity_eq h]
    have hs : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 input.size := by simpa only [kind_sizeRegister] using h.inputSize
    rw [hs]
    exact BitVec.ofNat_sub_ofNat_of_le input.size (64 - message.size % 64)
      (by have := inputSize_lt h; omega) hfull
  obtain ⟨f₅, t, hft, hrt, hct, het⟩ :=
    remainder_count_branch (variant := variant) boundary h.boundaryOutside f hrf hcf (by cases variant <;> exact heclear.rip)
  have htMem : t.external = f.external := het.agrees.external (by
    simp [remainderBranchEffect, remainderCountEffect, Effect.components, Component.Covers])
  have hremLt : input.size - (64 - message.size % 64) < 2^64 := by
    have := inputSize_lt h
    omega
  have hcountLt : (input.size - (64 - message.size % 64)) / 64 < 2^64 := by omega
  have hshift : (Operand.reg 5 : Operand 64).read f >>> 6 =
      BitVec.ofNat 64 ((input.size - (64 - message.size % 64)) / 64) := by
    rw [hf5]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hremLt, Nat.mod_eq_of_lt hcountLt]
  have hzero : (Operand.reg 5 : Operand 64).read f >>> 6 = 0 ↔
      (input.size - (64 - message.size % 64)) / 64 = 0 := by
    rw [hshift]
    constructor
    · intro hz
      have hn := congrArg BitVec.toNat hz
      change ((input.size - (64 - message.size % 64)) / 64) % 2^64 = 0 at hn
      rw [Nat.mod_eq_of_lt hcountLt] at hn
      exact hn
    · intro hz
      rw [hz]
      rfl
  obtain ⟨f₂, habAdv⟩ := hb.advances
  obtain ⟨f₄, hde⟩ := he.advances
  refine ⟨t, ⟨⟨f₁ + f₂ + 1 + f₃ + f₄ + 1 + f₅,
    (((((hsa.trans habAdv).trans hbc).trans hcd).trans hde).trans hef).trans hft⟩,
    hrt, hct, ?_, ?_, hfull, (by simpa only [kind_inputRegister] using het.writes.1.trans hf3), ?_, het.writes.2.trans hshift, ?_, ?_⟩⟩
  · simpa only [remainderBranchEffect, hzero, kind_tailEntry, kind_batchEntry] using het.rip
  · apply (hsf.trans het.agrees).mono
    intro comp hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hc
    · simp only [remainderBranchEffect, remainderCountEffect, Effect.components, List.map_cons,
        List.map_nil, Write.component_reg, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters]
  · simpa only [kind_batchSizeRegister] using (het.agrees.read (n := 64) (r := 5) (by
      simp [remainderBranchEffect, remainderCountEffect, Effect.components])).trans hf5
  · rw [htMem]
    exact hbf
  · change memLoad t.external _ 64 = _
    rw [htMem]
    exact hcountf.trans hcounte

end Md5.Proofs.Buffered.Update.Slices
