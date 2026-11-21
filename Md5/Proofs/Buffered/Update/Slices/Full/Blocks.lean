import Md5.Proofs.Buffered.Update.Slices.Full.Counter
import Md5.Proofs.Buffered.Update.Slices.Full.Blocks.Prepare
import Md5.Proofs.Buffered.Update.Slices.Full.Blocks.Call
import Md5.Proofs.Buffered.Update.Preservation.Compression

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

set_option maxRecDepth 4096 in
theorem blocks {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre (kind variant) boundary message input s)
    (hp : BatchReady variant boundary input s offset buffer count u) :
    ∃ t, BlocksDone variant boundary input s offset buffer count t := by
  by_cases hz : (input.size - offset) / 64 = 0
  · refine ⟨u, hp.advances, hp.ready, hp.code, ?_, hp.agrees, hp.offsetBound,
      hp.pointer, hp.size, ?_, ?_⟩
    · simpa only [hz, ite_true] using hp.rip
    · rw [fullBytes_of_size_lt _ (by simp only [ByteArray.size_extract, Nat.min_self]; omega)]
      change (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
        u.external ⟨(Standards.RFC.MD5.processBlocks buffer #[]).toBytes.toArray⟩
      rw [Md5.Proofs.RFC1321.processBlocks_empty]
      exact hp.bufferBytes
    · simpa only [hz, Nat.add_zero] using hp.counter
  · have hsp : stackPtr u = stackPtr s := hp.agrees.read (n := 64) (r := 4)
      (by cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters])
    have hpc : u.RIP = (pc variant 0x1003c5) := by simpa only [hz, ite_false, kind_batchEntry] using hp.rip
    obtain ⟨v, hav, hrv, hcv, he⟩ := counter_add h hp.agrees hsp hpc hp.ready hp.code
    have hac := counter_add_agrees hsp he
    have hsv : AgreesExcept ((kind variant).changes s) s v :=
      (hp.agrees.trans hac).mono (by simp)
    have hvsp : stackPtr v = stackPtr s := hsv.read (n := 64) (r := 4)
      (by cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters])
    have hv14 : (Operand.reg 14 : Operand 64).read v =
        (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 offset := by
      rw [he.agrees.read (by rw [counterAddEffect_components]; simp)]
      simpa only [kind_inputRegister] using hp.pointer
    have hv5 : (Operand.reg 5 : Operand 64).read v = BitVec.ofNat 64 (input.size - offset) := by
      rw [he.agrees.read (by rw [counterAddEffect_components]; simp)]
      simpa only [kind_batchSizeRegister] using hp.size
    have hv2 : (Operand.reg 2 : Operand 64).read v =
        BitVec.ofNat 64 ((input.size - offset) / 64) := by
      rw [he.agrees.read (by rw [counterAddEffect_components]; simp)]
      exact hp.blockCount
    have hbv := counter_add_buffer h hsp he hp.bufferBytes
    have hbase : stackPtr u + 272 = (kind variant).context s + 80 := by
      rw [hsp]
      rw [kind_context]
      change stackPtr s + 272 = stackPtr s + 192 + 80
      rw [BitVec.add_assoc]
      rfl
    have hcountv : (Operand.mem ((kind variant).context s + 80) : Operand 64).read v =
        BitVec.ofNat 64 (count + (input.size - offset) / 64) := by
      have hw := counter_add_write he
      rw [hbase, hp.counter, hp.blockCount, ← BitVec.ofNat_add] at hw
      exact hw
    have hbytes : CodeIn (codeRange (pc variant 0x1003cd) fullCompressBytes) v :=
      by
        cases variant with
        | false => exact program_text_slice hcv 0x3cd 11 (by decide +kernel)
        | true => exact program_text_slice hcv 0x197d 11 (by decide +kernel)
    obtain ⟨prepareFuel, w, hvw, hrw, _, hw⟩ := full_compress_prepare boundary h.boundaryOutside
      v hrv hbytes (by cases variant <;> exact he.rip)
    have hnoMem : ∀ c ∈ (fullCompressEffect variant v).components, ∀ x, ¬ c.Covers x := by
      simp [fullCompressEffect, Effect.components, Component.Covers]
    have hcw : CodeIn Extracted.programImage w := hw.codeIn (Effect.Avoids.of_noMem hnoMem _) hcv
    have hmemory : w.external = v.external := hw.agrees.external hnoMem
    have hprep : AgreesExcept ((kind variant).changes s) v w := hw.agrees.mono (by
      simp [fullCompressEffect, Effect.components, UpdateKind.changes])
    have hsw : AgreesExcept ((kind variant).changes s) s w :=
      (hsv.trans hprep).mono (by simp)
    have hwsp : stackPtr w = stackPtr s := hsw.read (n := 64) (r := 4)
      (by cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters])
    have hwdi : w.regValue .rdi = (kind variant).context s + 64 := by
      have hx := hw.writes.1
      change w.regValue .rdi = stackPtr v + 256 at hx
      rw [hx, hvsp]
      rw [kind_context]
      change stackPtr s + 256 = stackPtr s + 192 + 64
      rw [BitVec.add_assoc]
      rfl
    have hwsi : w.regValue .rsi = (Operand.reg 14 : Operand 64).read s +
        BitVec.ofNat 64 offset := hw.writes.2.trans hv14
    have hw2 : w.regValue .rdx = BitVec.ofNat 64 ((input.size - offset) / 64) :=
      (hw.agrees.read (n := 64) (r := 2) (by simp [fullCompressEffect, Effect.components])).trans hv2
    have hbw : (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
        w.external ⟨buffer.toBytes.toArray⟩ := hmemory ▸ hbv
    have hcountw : (Operand.mem ((kind variant).context s + 80) : Operand 64).read w =
        BitVec.ofNat 64 (count + (input.size - offset) / 64) := by
      change memLoad w.external _ 64 = _
      rw [hmemory]
      exact hcountv
    obtain ⟨t, ht⟩ := compress_full_input h hsw hwsp hw.rip hrw hcw hwdi offset hp.offsetBound
      hwsi hw2 hbw
    have hct := ht.update_agrees h hwsp hwdi
    obtain ⟨oldFuel, hau⟩ := hp.advances
    obtain ⟨callFuel, hwt⟩ := ht.advances
    refine ⟨t, ⟨oldFuel + 1 + prepareFuel + callFuel, ((hau.trans hav).trans hvw).trans hwt⟩,
      ht.ready, ht.code, (by simpa only [kind_tailEntry] using ht.rip), (hsw.trans hct).mono (by simp), hp.offsetBound, ?_, ?_, ?_, ?_⟩
    · simpa only [kind_inputRegister] using ((ht.agrees.read (n := 64) (r := 14) (by
        simp [FinalizeReset.CompressCall.changes])).trans
        (hw.agrees.read (n := 64) (r := 14) (by simp [fullCompressEffect, Effect.components]))).trans hv14
    · simpa only [kind_batchSizeRegister] using ((ht.agrees.read (n := 64) (r := 5) (by
        simp [FinalizeReset.CompressCall.changes])).trans
        (hw.agrees.read (n := 64) (r := 5) (by simp [fullCompressEffect, Effect.components]))).trans hv5
    · rw [← h.compressionOutputRegion hwdi]
      exact ht.output
    · exact (ht.update_counter h hwsp hwdi).trans hcountw

end Md5.Proofs.Buffered.Update.Slices
