import Md5.Proofs.Buffered.Update.ResetSecond.Counter
import Md5.Proofs.Buffered.Update.Store
import Md5.Proofs.Buffered.Update.ResetSecond.Calls
import Md5.Proofs.Buffered.Update.Batch
import Md5.Proofs.Buffered.Update.Compression
import Md5.Proofs.Buffered.Update.Preservation
import Md5.Proofs.Buffered.Update.Preservation.Compression

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem blocks_done [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hu : UpdateBatchReady kind boundary input s offset buffer count u) :
    ∃ t, UpdateBlocksDone kind boundary input s offset buffer count t := by
  by_cases hz : (input.size - offset) / 64 = 0
  · exact ⟨u, hu.noBlocks hz⟩
  have hrip : u.RIP = (pc kind 0x100a35) := by
    have hpc : pc kind 0x100a35 = kind.batchEntry := by
      rcases hkind with rfl | rfl | rfl <;> decide +kernel
    rw [hpc]
    simpa only [hz, ite_false] using hu.rip
  have hsp : stackPtr u = stackPtr s := hu.agrees.read (n := 64) (r := 4) (by
    rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
  have hw : MemoryRoutines.WritableRange u (kind.context u + 80) 8 := by
    simpa [UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc, ← BitVec.ofNat_add, hsp] using
      h.contextWritable_of_agrees hu.agrees 80 8 (by decide)
  have hpre := h.contextStorePre hu.agrees hsp hrip 13 80 8 (by decide) (by
    intro j hj
    rcases hkind with rfl | rfl | rfl
    · have ht := text_address_in_program (0xa35 + j) (by
        have hn : 0xa42 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht
    · have ht := text_address_in_program (0x10c5 + j) (by
        have hn : 0x10d2 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht
    · have ht := text_address_in_program (0x15a3 + j) (by
        have hn : 0x15b0 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht)
  have hbytes : CodeIn (codeRange (pc kind 0x100a35) (addPrepareBytes kind)) u := by
    rcases hkind with rfl | rfl | rfl
    · exact program_text_slice hu.code 0xa35 13 (by decide +kernel)
    · exact program_text_slice hu.code 0x10c5 13 (by decide +kernel)
    · exact program_text_slice hu.code 0x15a3 13 (by decide +kernel)
  obtain ⟨fv, v, hav, hrv, _, he⟩ := add_prepare hkind boundary h.boundaryOutside
    u hu.ready hbytes (by
      simpa [UpdateKind.context, BitVec.add_assoc, ← BitVec.ofNat_add] using hpre)
  have hcv : CodeIn Extracted.programImage v := by
    apply CodeIn.of_agreesExcept he.agrees _ hu.code
    intro x hx c hm hcover
    simp only [addPrepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, heq⟩ := hcover
    exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
  have haddr : kind.context u + 80 = kind.context s + 80 := by
    simp only [UpdateKind.context, hsp]
  have hm : ∀ c ∈ (addPrepareEffect kind u).components, ∀ address, c.Covers address →
      (Component.mem (kind.context s + 80) 8).Covers address := by
    intro c hcm address hcover
    simp only [addPrepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    simpa only [haddr] using hcover
  have hag : AgreesExcept (kind.changes s) u v := by
    apply he.agrees.widen
    · intro c hc hn
      simp only [addPrepareEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals rcases hkind with rfl | rfl | rfl <;> simp_all [UpdateKind.changes, UpdateKind.workRegisters, Component.isMem]
    · intro address c hc hcover
      obtain ⟨i, hi, heq⟩ := hm c hc address hcover
      refine ⟨.mem (kind.context s) 88,
        by simp [UpdateKind.changes], 80 + i, by omega, ?_⟩
      rw [heq, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
  have hagv : AgreesExcept (kind.changes s) s v :=
    (hu.agrees.trans hag).mono (by simp)
  have hvsp : stackPtr v = stackPtr s := hagv.read (n := 64) (r := 4) (by
    rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
  have hdi : v.regValue .rdi = kind.context s + 64 := by
    change (Operand.reg 7 : Operand 64).read v = _
    rw [he.writes.2.1]
    simp only [UpdateKind.context, hsp]
  have hsi : v.regValue .rsi = (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset := by
    rcases hkind with rfl | rfl | rfl
    · exact (he.agrees.read (n := 64) (r := 6) (by simp [addPrepareEffect, Effect.components])).trans hu.pointer
    · exact (he.agrees.read (n := 64) (r := 6) (by simp [addPrepareEffect, Effect.components])).trans hu.pointer
    · exact he.writes.2.2.trans hu.pointer
  have hdx : v.regValue .rdx = BitVec.ofNat 64 ((input.size - offset) / 64) :=
    (he.agrees.read (n := 64) (r := 2) (by rcases hkind with rfl | rfl | rfl <;> simp [addPrepareEffect, Effect.components])).trans hu.blockCount
  have hbv : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      v.external ⟨buffer.toBytes.toArray⟩ := by
    have hs : (⟨buffer.toBytes.toArray⟩ : ByteArray).size = 16 := by
      simp only [ByteArray.size, Vector.size_toArray]
    have hb := h.bytes_before_counter_of_agrees he.agrees hm (offset := 64)
      (bytes := ⟨buffer.toBytes.toArray⟩) (by rw [hs]; decide)
      (by simpa only [hs] using hu.bufferBytes)
    simpa only [hs] using hb
  have hcounter : (Operand.mem (kind.context s + 80) : Operand 64).read v =
      BitVec.ofNat 64 (count + (input.size - offset) / 64) := by
    have hx := he.writes.1
    change (Operand.mem (kind.context u + 80) : Operand 64).read v =
      (Operand.mem (kind.context u + 80) : Operand 64).read u + (Operand.reg 2 : Operand 64).read u at hx
    rw [haddr, hu.counter, hu.blockCount, ← BitVec.ofNat_add] at hx
    exact hx
  have hcp := h.compressionPre_fullInput hagv hvsp hdi offset hu.offsetBound hsi hdx hbv
  obtain ⟨w, hc⟩ := compress_call (by rcases hkind with rfl | rfl | rfl <;> simp [addPrepareEffect, pc]) h.boundaryOutside hrv hcv he.rip hcp
  have hwb : CodeIn (codeRange (pc kind 0x100a47) (sourceRestoreBytes kind)) w := by
    rcases hkind with rfl | rfl | rfl
    · exact program_text_slice hc.code 0xa47 3 (by decide +kernel)
    · exact program_text_slice hc.code 0x10d7 3 (by decide +kernel)
    · exact program_text_slice hc.code 0x15b5 0 (by decide +kernel)
  obtain ⟨ft, t, hat, hrt, _, het⟩ := source_restore hkind boundary h.boundaryOutside w hc.ready hwb (by rcases hkind with rfl | rfl | rfl <;> exact hc.rip)
  have hnomem : ∀ c ∈ (sourceRestoreEffect kind w).components, ∀ address, ¬ c.Covers address := by
    simp [sourceRestoreEffect, UpdateKind.inputRegister, Effect.components, Component.Covers]
  have htmem : t.external = w.external := het.agrees.external hnomem
  have htag : AgreesExcept (kind.changes s) w t := het.agrees.mono (by
    rcases hkind with rfl | rfl | rfl <;> simp [sourceRestoreEffect, UpdateKind.inputRegister, Effect.components, UpdateKind.changes, UpdateKind.workRegisters])
  have hcallag := hc.update_agrees h hvsp hdi
  have hsize : (Operand.reg kind.batchSizeRegister : Operand 64).read t = BitVec.ofNat 64 (input.size - offset) := by
    rcases hkind with rfl | rfl | rfl
    all_goals exact ((het.agrees.read (by simp [sourceRestoreEffect, UpdateKind.inputRegister, UpdateKind.batchSizeRegister, Effect.components])).trans
      ((hc.agrees.read (by simp [FinalizeReset.CompressCall.changes, UpdateKind.batchSizeRegister])).trans
        (he.agrees.read (by simp [addPrepareEffect, UpdateKind.batchSizeRegister, Effect.components])))).trans hu.size
  have hpointer : (Operand.reg kind.inputRegister : Operand 64).read t =
      (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset := by
    rcases hkind with rfl | rfl | rfl
    · exact (het.writes.trans ((hc.agrees.read (n := 64) (r := 12) (by
        simp [FinalizeReset.CompressCall.changes])).trans he.writes.2.2)).trans hu.pointer
    · exact (het.writes.trans ((hc.agrees.read (n := 64) (r := 12) (by
        simp [FinalizeReset.CompressCall.changes])).trans he.writes.2.2)).trans hu.pointer
    · exact (het.writes.trans ((hc.agrees.read (n := 64) (r := 3) (by
        simp [FinalizeReset.CompressCall.changes])).trans
        (he.agrees.read (by simp [addPrepareEffect, Effect.components])))).trans hu.pointer
  obtain ⟨fu, hau⟩ := hu.advances
  obtain ⟨fc, hac⟩ := hc.advances
  refine ⟨t, ⟨⟨fu + fv + fc + ft, ((hau.trans hav).trans hac).trans hat⟩, hrt,
    het.agrees.codeIn hnomem hc.code, (by rcases hkind with rfl | rfl | rfl <;> exact het.rip),
    ((hagv.trans hcallag).trans htag).mono (by simp), hu.offsetBound, hpointer, hsize, ?_, ?_⟩⟩
  · rw [htmem, ← h.compressionOutputRegion hdi]
    exact hc.output
  · change memLoad t.external _ 64 = _
    rw [htmem]
    exact (hc.update_counter h hvsp hdi).trans hcounter

end Md5.Proofs.Buffered.ResetSecond
