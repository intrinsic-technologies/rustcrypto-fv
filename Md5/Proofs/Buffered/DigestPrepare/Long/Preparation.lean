import Md5.Proofs.Buffered.DigestPrepare.Long.Preparation.Register
import Md5.Proofs.Buffered.DigestPrepare.Branch
import Md5.Proofs.Buffered.DigestPrepare.Copy
import Md5.Proofs.Buffered.Update.ResetFirst.Arithmetic
import Md5.Proofs.Buffered.Stores.Program

namespace Md5.Proofs.Buffered.DigestPrepare.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

set_option maxRecDepth 2048 in
theorem prepare_compression [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hCall : Digest.ValidCall bindings initial input)
    (h : Initialized initial (returnBoundary initial) input s) (hLong : 64 ≤ input.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Prepared initial input t := by
  obtain ⟨u, hbranch, hu, hcu, hurip, hau⟩ := entry_branch h.ready h.code h.boundaryOutside
    h.rip (input_size_bounded hCall) h.inputSize
  have hrip : u.RIP = 0x100088 := by simpa only [ite_eq_left hLong] using hurip
  have hargs : CodeIn (codeRange 0x100088 argumentsBytes) u :=
    program_text_slice hcu 0x88 27 (by decide +kernel)
  obtain ⟨n, v, harg, hv, _, he⟩ := arguments_prepare (returnBoundary initial)
    h.boundaryOutside u hu hargs hrip
  have hcv := he.agrees.codeIn
    (by simp [argumentsEffect, Effect.components, Component.Covers]) hcu
  have hav : AgreesExcept [.reg 2, .reg 12, .reg 15, .flags, .rip] s v := by
    apply (hau.trans he.agrees).mono
    simp [argumentsEffect, Effect.components]
  have hvsp : stackPtr v = stackPtr s := hav.read (n := 64) (r := 4) (by simp)
  have hw := h.toFrame.writable hav 256 8 (by decide)
  have hwv : MemoryRoutines.WritableRange v (stackPtr v + 256) 8 := by
    rw [hvsp]
    exact hw
  have hstore := Stores.mov_m64_r64_effect_step 0x1000a3 0x48
    (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 256))
    (by decide) (by decide) (by decide)
  change StepEffect (Memory.StorePre 0x1000a3 8 (fun w ↦ stackPtr w + 256) 8)
    (codeRange 0x1000a3 [0x48, 0x89, 0x94, 0x24, 0, 1, 0, 0])
    (storeEffect 0x1000a3 8 (fun w ↦ stackPtr w + 256)
      (fun w ↦ (Operand.reg 2 : Operand 64).read w)) at hstore
  have hstorePre : Memory.StorePre 0x1000a3 8 (fun w ↦ stackPtr w + 256) 8 v :=
    ⟨he.rip, ⟨hwv.readable.low, hwv.readable.mem, hwv.tables⟩,
      Stores.rangeApart_text hwv.code (by decide +kernel : 0xa3 + 8 ≤ Extracted.textBytes.size)⟩
  have hstoreBytes : CodeIn (codeRange 0x1000a3 [0x48, 0x89, 0x94, 0x24, 0, 1, 0, 0]) v :=
    program_text_slice hcv 0xa3 8 (by decide +kernel)
  obtain ⟨w, hst, hwready, hstE⟩ := hstore.advances hv hstoreBytes hstorePre
    (text_address_ne_return h.boundaryOutside 0xab (by decide +kernel))
  have hcw := hstE.codeIn (Stores.store_avoids_program rfl (by simpa using hwv.code)) hcv
  have hmovBytes : CodeIn (codeRange 0x1000ab [0x4c, 0x89, 0xf7]) w :=
    program_text_slice hcw 0xab 3 (by decide +kernel)
  obtain ⟨t, hmov, ht, hmovE⟩ := (mov_r64_r64_effect_step 0x1000ab 0x4c 0xf7
    (by unfold RexWPrefix; decide) (by decide)).advances hwready hmovBytes hstE.rip
      (text_address_ne_return h.boundaryOutside 0xae (by decide +kernel))
  have hmovAg : AgreesExcept [.reg 7, .rip] w t := hmovE.agrees
  have hct := hmovAg.codeIn (by simp [Component.Covers]) hcw
  have hat : AgreesExcept [.reg 2, .reg 12, .reg 15, .reg 7, .flags, .rip,
      .mem (stackPtr s + 256) 8] s t := by
    have ha := (hav.trans hstE.agrees).trans hmovAg
    simp only [storeEffect_components, hvsp] at ha
    exact ha.mono (by simp)
  have htsp : stackPtr t = stackPtr s := hat.read (n := 64) (r := 4) (by simp)
  have hframe : Frame initial (returnBoundary initial) t := by
    apply h.toFrame.preserve hCall.stackAvailable hat ht hct
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem, digestPreparationChanges]
    · intro c hc a hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcov.elim
      obtain ⟨i, hi, rfl⟩ := hcov
      change (Finalize.Kind.digest.stackRegion s).Contains
        (stackPtr s + BitVec.ofNat 64 256 + BitVec.ofNat 64 i).toNat
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.toFrame.address (by omega)]
      have := h.stackLow
      change (stackPtr s).toNat - 320 ≤ _ ∧ _ < (stackPtr s).toNat - 320 + 584
      omega
    · exact htsp
    · exact hat.read (n := 64) (r := 3) (by simp)
    · exact hat.read (n := 64) (r := 14) (by simp)
  have h15 : (Operand.reg 15 : Operand 64).read u = BitVec.ofNat 64 input.size :=
    (hau.read (n := 64) (r := 15) (by simp)).trans h.inputSize
  have hsize : input.size < 2^32 := by
    have hb : (initial.regValue .rdi).toNat + input.size < 2^32 := hCall.inputInMemory.2.1
    omega
  have h15nat : ((Operand.reg 15 : Operand 64).read u).toNat = input.size := by
    rw [h15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hquot : (Operand.reg 2 : Operand 64).read v = BitVec.ofNat 64 (input.size / 64) := by
    apply he.writes.1.trans
    change ((Operand.reg 15 : Operand 64).read u >>> 6) = BitVec.ofNat 64 (input.size / 64)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, h15nat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hfull : 0x7fffffffffffffc0 &&& (Operand.reg 15 : Operand 64).read u =
      BitVec.ofNat 64 (input.size / 64 * 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.and_comm, ResetFirst.fullBlockMask_toNat _ (by rw [h15nat]; omega), h15nat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest : (((Operand.reg 15 : Operand 32).read u &&& 63).setWidth 64) =
      BitVec.ofNat 64 (input.size % 64) := by
    apply BitVec.eq_of_toNat_eq
    change (((u.GPR[gprIndex 15]).setWidth 32 &&& 63).setWidth 64).toNat = _
    rw [ResetFirst.tailMask_toNat]
    change ((Operand.reg 15 : Operand 64).read u).toNat % 64 = _
    rw [h15nat, BitVec.toNat_ofNat]
    omega
  have hafter : AgreesExcept [.reg 7, .rip, .mem (stackPtr v + 256) 8] v t := by
    have ha := hstE.agrees.trans hmovAg
    simp only [storeEffect_components] at ha
    exact ha.mono (by simp)
  refine ⟨2 + n + 1 + 1, t, ((hbranch.trans harg).trans hst).trans hmov,
    ⟨⟨hframe, ?_, ?_, ?_, ?_⟩, hmovE.rip, ?_, ?_, ?_⟩⟩
  · have hbuffer := h.absorbed.buffer
    rw [absorbedBuffer_empty] at hbuffer
    have hcontext : (Finalize.Kind.digest.context s).toNat = (stackPtr s).toNat + 176 :=
      h.toFrame.address (by decide)
    rw [hcontext, Nat.add_assoc] at hbuffer
    rw [htsp]
    refine ⟨hbuffer.1, fun i ↦ ?_⟩
    apply Eq.trans _ (hbuffer.2 i)
    apply hat.byte
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    obtain ⟨j, hj, heq⟩ := hcov
    have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    have hn := congrArg BitVec.toNat heq
    change (BitVec.ofNat 64 ((stackPtr s).toNat + 240 + i.val)).toNat =
      (stackPtr s + BitVec.ofNat 64 256 + BitVec.ofNat 64 j).toNat at hn
    have hh : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.toFrame.address (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    omega
  · rw [htsp, ← hvsp]
    have hm := hmovAg.external (by simp [Component.Covers])
    change memLoad t.external (stackPtr v + 256) 64 = _
    rw [hm]
    exact hstE.writes.trans hquot
  · rw [hafter.read (n := 64) (r := 12) (by simp), he.writes.2.1, hfull]
    have hsi : (Operand.reg 6 : Operand 64).read u = initial.regValue .rdi :=
      (hau.read (n := 64) (r := 6) (by simp)).trans h.inputPointer
    rw [hsi, BitVec.add_comm]
  · exact (hafter.read (n := 64) (r := 15) (by simp)).trans (he.writes.2.2.trans hrest)
  · exact (hat.read (n := 64) (r := 6) (by simp)).trans h.inputPointer
  · have hm : (Operand.reg 7 : Operand 64).read t = (Operand.reg 14 : Operand 64).read w :=
      hmovE.writes
    have h14 : (Operand.reg 14 : Operand 64).read w = (Operand.reg 14 : Operand 64).read s :=
      (hstE.agrees.read (n := 64) (r := 14) (by simp)).trans
        (hav.read (n := 64) (r := 14) (by simp))
    rw [hm, h14, h.statePointer, htsp]
  · exact (hafter.read (n := 64) (r := 2) (by simp)).trans hquot

end Md5.Proofs.Buffered.DigestPrepare.Long
