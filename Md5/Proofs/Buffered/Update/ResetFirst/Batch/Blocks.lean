import Md5.Proofs.Buffered.Update.ResetFirst.Batch.Prepare
import Md5.Proofs.Buffered.Update.ResetFirst.BatchContracts
import Md5.Proofs.Buffered.Update.ResetFirst.Calls
import Md5.Proofs.Buffered.Update.Compression
import Md5.Proofs.Buffered.Update.Preservation
import Md5.Proofs.Buffered.Update.Preservation.Compression

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem batchPrepareEffect_components_of_kind (kind : UpdateKind) (u : RamState) :
    (batchPrepareEffect_of_kind kind u).components =
      [.mem (stackPtr u + stackOffset kind 88) 8, .reg 7, .reg 6, .flags, .rip] := by
  simp [batchPrepareEffect_of_kind, Effect.components]

theorem batchPrepareEffect_update_agrees_of_kind {kind : UpdateKind} (hk : KindSupported kind) {s u v : RamState}
    (hsp : stackPtr u = stackPtr s) (he : (batchPrepareEffect_of_kind kind u).Holds u v) :
    AgreesExcept (kind.changes s) u v := by
  apply he.agrees.widen
  · intro c hc hm
    rw [batchPrepareEffect_components_of_kind] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals rcases hk with rfl | rfl | rfl <;> simp_all [Component.isMem, UpdateKind.changes]
  · intro address c hc hcover
    rw [batchPrepareEffect_components_of_kind] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    refine ⟨.mem (kind.context s) 88, by simp [UpdateKind.changes], ?_⟩
    obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨80 + i, by omega, ?_⟩
    rw [hsp, BitVec.ofNat_add]
    rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    all_goals rw [← BitVec.add_assoc]; rfl

set_option maxRecDepth 4096 in
theorem batch_blocks_run_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre kind boundary message input s)
    (hb : UpdateBatchReady kind boundary input s offset buffer count u) :
    ∃ t, UpdateBlocksDone kind boundary input s offset buffer count t := by
  by_cases hz : (input.size - offset) / 64 = 0
  · refine ⟨u, hb.advances, hb.ready, hb.code, ?_, hb.agrees, hb.offsetBound,
      hb.pointer, hb.size, ?_, ?_⟩
    · simpa only [hz, ite_true] using hb.rip
    · rw [fullBytes_of_size_lt _ (by simp only [ByteArray.size_extract, Nat.min_self]; omega),
        show Standards.RFC.MD5.wordsOfBytes ByteArray.empty = #[] from rfl,
        Md5.Proofs.RFC1321.processBlocks_empty]
      exact hb.bufferBytes
    · simpa only [hz, Nat.add_zero] using hb.counter
  · have hsp : stackPtr u = stackPtr s := hb.agrees.read (n := 64) (r := 4)
      (by rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
    have hpc : u.RIP = (pc kind 0x72e) := by
      have hx := hb.rip
      rw [ite_eq_right hz] at hx
      rcases hk with rfl | rfl | rfl <;> exact hx
    have hw : MemoryRoutines.WritableRange u (stackPtr u + stackOffset kind 88) 8 := by
      rw [hsp]
      rcases hk with rfl | rfl | rfl <;> exact h.contextWritable_of_agrees hb.agrees 80 8 (by decide)
    have hbytes : CodeIn (codeRange (pc kind 0x72e) (batchPrepareBytes_of_kind kind)) u :=
      by
        rcases hk with rfl | rfl | rfl
        · exact program_text_slice hb.code 0x72e 13 (by decide +kernel)
        · exact program_text_slice hb.code 0xdde 13 (by decide +kernel)
        · exact program_text_slice hb.code 0x1467 13 (by decide +kernel)
    have hap : RangeApart (stackPtr u + stackOffset kind 88) 8 (pc kind 0x72e) 13 := by
      intro i hi j hj heq
      apply hw.code i hi
      rw [heq]
      rcases hk with rfl | rfl | rfl
      · have ht := text_address_in_program (0x72e + j) (by
          have hn : 0x73b ≤ Extracted.textBytes.size := by decide +kernel
          omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
      · have ht := text_address_in_program (0xdde + j) (by
          have hn : 0xdeb ≤ Extracted.textBytes.size := by decide +kernel
          omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
      · have ht := text_address_in_program (0x1467 + j) (by
          have hn : 0x1474 ≤ Extracted.textBytes.size := by decide +kernel
          omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
    obtain ⟨prepareFuel, w, hauw, hrw, _, he⟩ := batch_prepare_of_kind hk boundary h.boundaryOutside
      u hb.ready hbytes ⟨hpc, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, hap⟩
    have hcw : CodeIn Extracted.programImage w := by
      apply CodeIn.of_agreesExcept he.agrees _ hb.code
      intro x hx c hc hcover
      rw [batchPrepareEffect_components_of_kind] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      obtain ⟨i, hi, heq⟩ := hcover
      exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
    have hsw : AgreesExcept (kind.changes s) s w :=
      (hb.agrees.trans (batchPrepareEffect_update_agrees_of_kind hk hsp he)).mono (by simp)
    have hwsp : stackPtr w = stackPtr s := hsw.read (n := 64) (r := 4)
      (by rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters])
    have hdi : w.regValue .rdi = kind.context s + 64 := by
      change (.reg 7 : Operand 64).read w = _
      rw [he.writes.2.1, hsp]
      rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    have hsi : w.regValue .rsi = (Operand.reg kind.inputRegister : Operand 64).read s +
        BitVec.ofNat 64 offset := he.writes.2.2.trans hb.pointer
    have hdx : w.regValue .rdx = BitVec.ofNat 64 ((input.size - offset) / 64) :=
      (he.agrees.read (n := 64) (r := 2) (by rw [batchPrepareEffect_components_of_kind]; simp)).trans
        hb.blockCount
    have hbase : stackPtr u + stackOffset kind 88 = kind.context s + 80 := by
      rw [hsp]
      rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    have hmem : ∀ c ∈ (batchPrepareEffect_of_kind kind u).components, ∀ address, c.Covers address →
        (Component.mem (kind.context s + 80) 8).Covers address := by
      intro c hc address hcover
      rw [batchPrepareEffect_components_of_kind] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      simpa only [hbase] using hcover
    have hbw : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
        w.external ⟨buffer.toBytes.toArray⟩ := by
      have hs : (⟨buffer.toBytes.toArray⟩ : ByteArray).size = 16 := by
        simp only [ByteArray.size, Vector.size_toArray]
      have hh := h.bytes_before_counter_of_agrees he.agrees hmem (offset := 64)
        (bytes := ⟨buffer.toBytes.toArray⟩) (by rw [hs]; decide)
        (by simpa only [hs] using hb.bufferBytes)
      simpa only [hs] using hh
    have hcount : (Operand.mem (kind.context s + 80) : Operand 64).read w =
        BitVec.ofNat 64 (count + (input.size - offset) / 64) := by
      have hh := he.writes.1
      change (Operand.mem (stackPtr u + stackOffset kind 88) : Operand 64).read w =
        (Operand.mem (stackPtr u + stackOffset kind 88) : Operand 64).read u +
          (Operand.reg 2 : Operand 64).read u at hh
      rw [hbase, hb.counter, hb.blockCount, ← BitVec.ofNat_add] at hh
      exact hh
    have hpre := h.compressionPre_fullInput hsw hwsp hdi offset hb.offsetBound hsi hdx hbw
    obtain ⟨t, ht⟩ := compress_call_of_kind hk (Or.inr rfl) h.boundaryOutside hrw hcw he.rip hpre
    have hag := ht.update_agrees h hwsp hdi
    obtain ⟨oldFuel, hau⟩ := hb.advances
    obtain ⟨callFuel, hwt⟩ := ht.advances
    refine ⟨t, ⟨oldFuel + prepareFuel + callFuel, (hau.trans hauw).trans hwt⟩,
      ht.ready, ht.code, (by rcases hk with rfl | rfl | rfl <;> exact ht.rip), (hsw.trans hag).mono (by simp), hb.offsetBound, ?_, ?_, ?_, ?_⟩
    · exact ((ht.agrees.read (n := 64) (r := kind.inputRegister) (by
        rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.inputRegister, FinalizeReset.CompressCall.changes])).trans
        (he.agrees.read (n := 64) (r := kind.inputRegister) (by rw [batchPrepareEffect_components_of_kind]; rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.inputRegister]))).trans
        hb.pointer
    · exact ((ht.agrees.read (n := 64) (r := kind.batchSizeRegister) (by
        rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.batchSizeRegister, FinalizeReset.CompressCall.changes])).trans
        (he.agrees.read (n := 64) (r := kind.batchSizeRegister) (by rw [batchPrepareEffect_components_of_kind]; rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.batchSizeRegister]))).trans
        hb.size
    · rw [← h.compressionOutputRegion hdi]
      exact ht.output
    · exact (ht.update_counter h hwsp hdi).trans hcount

theorem batchPrepareEffect_components (u : RamState) :
    (batchPrepareEffect u).components =
      [.mem (stackPtr u + 88) 8, .reg 7, .reg 6, .flags, .rip] := by
  exact batchPrepareEffect_components_of_kind (kind := .resetFirst) u

theorem batchPrepareEffect_update_agrees {s u v : RamState}
    (hsp : stackPtr u = stackPtr s) (he : (batchPrepareEffect u).Holds u v) :
    AgreesExcept (UpdateKind.resetFirst.changes s) u v := by
  exact batchPrepareEffect_update_agrees_of_kind (kind := .resetFirst) (Or.inl rfl) hsp he

theorem batch_blocks_run [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre .resetFirst boundary message input s)
    (hb : BatchReady boundary input s offset buffer count u) :
    ∃ t, UpdateBlocksDone .resetFirst boundary input s offset buffer count t := by
  exact batch_blocks_run_of_kind (kind := .resetFirst) (Or.inl rfl) h hb

end Md5.Proofs.Buffered.ResetFirst
