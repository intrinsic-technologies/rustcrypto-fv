import Sha1.Proofs.Buffered.DigestPrepare.Long.Preparation.Register
import Sha1.Proofs.Buffered.DigestPrepare.Long.Preparation.Arithmetic
import Sha1.Proofs.Buffered.DigestPrepare.Branch
import Sha1.Proofs.Buffered.DigestPrepare.Position
import Sha1.Proofs.Common.Instructions.MovStore.Triple

namespace Sha1.Proofs.Buffered.DigestPrepare.Long

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine Sha1.Proofs.Common.Instructions
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

set_option maxRecDepth 2048 in
theorem prepare_compression [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hCall : Digest.ValidCall bindings initial input)
    (h : Initialized initial (returnBoundary initial) input s) (hLong : 64 ≤ input.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Prepared initial input t := by
  have hs := hCall.stackAvailable
  have hst := h.toFrame.storage hCall
  have hinBound : (initial.regValue .rdi).toNat + input.size < 2^32 := hCall.inputInMemory.2.1
  have hsize64 : input.size < 2^64 := by omega
  obtain ⟨u, hbranch, hu, hcu, hurip, hau⟩ := entry_branch h.ready h.code h.boundaryOutside
    h.rip hsize64 h.inputSize
  have hrip : u.RIP = 0x100093 := by simpa only [hLong, ite_true] using hurip
  have hargs : CodeIn (codeRange 0x100093 argumentsBytes) u :=
    program_text_slice hcu 0x93 27 (by decide +kernel)
  obtain ⟨n, v, harg, hv, _, he⟩ := arguments_prepare (returnBoundary initial)
    h.boundaryOutside u hu hargs hrip
  have hcv := he.agrees.codeIn
    (by simp [argumentsEffect, Effect.components, Component.Covers]) hcu
  have hav : AgreesExcept [.reg 2, .reg 12, .reg 15, .flags, .rip] s v := by
    apply (hau.trans he.agrees).mono
    simp [argumentsEffect, Effect.components]
  have hvsp : stackPtr v = stackPtr s := hav.read (n := 64) (r := 4) (by simp)
  have hw := h.toFrame.writable hCall hav 0xf8 8 (by decide)
  have hwv : MemoryRoutines.WritableRange v (stackPtr v + 0xf8) 8 := by
    rw [hvsp]
    exact hw
  have hstore := MovStore.mov_m64_r64_effect_step 0x1000ae 0x48
    (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 0xf8))
    (by decide) (by decide) (by decide)
  change StepEffect (StorePre.StorePre 0x1000ae 8 (fun w ↦ stackPtr w + 0xf8) 8)
    (codeRange 0x1000ae [0x48, 0x89, 0x94, 0x24, 0xf8, 0, 0, 0])
    (storeEffect 0x1000ae 8 (fun w ↦ stackPtr w + 0xf8)
      (fun w ↦ (Operand.reg 2 : Operand 64).read w)) at hstore
  have hstorePre : StorePre.StorePre 0x1000ae 8 (fun w ↦ stackPtr w + 0xf8) 8 v :=
    ⟨he.rip, ⟨hwv.readable.low, hwv.readable.mem, hwv.tables⟩,
      rangeApart_text hwv.code
        (by decide +kernel : 0xae + 8 ≤ Extracted.textBytes.size)⟩
  have hstoreBytes : CodeIn (codeRange 0x1000ae [0x48, 0x89, 0x94, 0x24, 0xf8, 0, 0, 0]) v :=
    program_text_slice hcv 0xae 8 (by decide +kernel)
  obtain ⟨w, hstw, hwready, hstE⟩ := hstore.advances hv hstoreBytes hstorePre
    (text_address_ne_return h.boundaryOutside 0xb6 (by decide +kernel))
  have hcw := hstE.codeIn (store_avoids_program rfl (by simpa using hwv.code)) hcv
  have hmovBytes : CodeIn (codeRange 0x1000b6 [0x4c, 0x89, 0xf7]) w :=
    program_text_slice hcw 0xb6 3 (by decide +kernel)
  obtain ⟨t, hmov, ht, hmovE⟩ := (mov_r64_r64_effect_step 0x1000b6 0x4c 0xf7
    (by unfold RexWPrefix; decide) (by decide)).advances hwready hmovBytes hstE.rip
      (text_address_ne_return h.boundaryOutside 0xb9 (by decide +kernel))
  have hmovAg : AgreesExcept [.reg 7, .rip] w t := hmovE.agrees
  have hct := hmovAg.codeIn (by simp [Component.Covers]) hcw
  have hat : AgreesExcept [.reg 2, .reg 12, .reg 15, .reg 7, .flags, .rip,
      .mem (stackPtr s + 0xf8) 8] s t := by
    have ha := (hav.trans hstE.agrees).trans hmovAg
    simp only [storeEffect_components, hvsp] at ha
    exact ha.mono (by simp)
  have htsp : stackPtr t = stackPtr s := hat.read (n := 64) (r := 4) (by simp)
  have hlow := hst.stackLow
  have hhigh : (stackPtr s).toNat + 0x118 < 2^32 := hst.stackHigh
  have hframe : Frame initial (returnBoundary initial) t := by
    apply h.toFrame.preserve hs hat ht hct
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem, digestPreparationChanges]
    · intro c hc a hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcov.elim
      obtain ⟨i, hi, rfl⟩ := hcov
      change (Finalize.Kind.digestCopy.stackRegion s).Contains
        (stackPtr s + BitVec.ofNat 64 0xf8 + BitVec.ofNat 64 i).toNat
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.toFrame.address hs (by omega)]
      change (stackPtr s).toNat - Finalize.Kind.frameBytes ≤ _ ∧ _ < (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118)
      omega
    · exact htsp
    · exact hat.read (n := 64) (r := 3) (by simp)
    · exact hat.read (n := 64) (r := 14) (by simp)
  have h15 : (Operand.reg 15 : Operand 64).read u = BitVec.ofNat 64 input.size :=
    (hau.read (n := 64) (r := 15) (by simp)).trans h.inputSize
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
    rw [BitVec.and_comm, fullBlockMask_toNat _ (by rw [h15nat]; omega), h15nat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest : (((Operand.reg 15 : Operand 32).read u &&& 63).setWidth 64) =
      BitVec.ofNat 64 (input.size % 64) := by
    apply BitVec.eq_of_toNat_eq
    change (((u.GPR[gprIndex 15]).setWidth 32 &&& 63).setWidth 64).toNat = _
    rw [tailMask_toNat]
    change ((Operand.reg 15 : Operand 64).read u).toNat % 64 = _
    rw [h15nat, BitVec.toNat_ofNat]
    omega
  have hafter : AgreesExcept [.reg 7, .rip, .mem (stackPtr v + 0xf8) 8] v t := by
    have ha := hstE.agrees.trans hmovAg
    simp only [storeEffect_components] at ha
    exact ha.mono (by simp)
  refine ⟨2 + n + 1 + 1, t, ((hbranch.trans harg).trans hstw).trans hmov,
    ⟨⟨hframe, ?_, ?_, ?_, ?_⟩, hmovE.rip, ?_, ?_, ?_⟩⟩
  · have hhash := h.absorbed.state
    rw [absorbedStateBytes, absorbedHash_empty] at hhash
    have hcontext : (stackPtr s + 0xb8 + 72).toNat = (stackPtr s).toNat + 0x100 := by
      change (stackPtr s + BitVec.ofNat 64 0xb8 + BitVec.ofNat 64 72).toNat = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.toFrame.address hs (by decide)]
    rw [hcontext] at hhash
    rw [htsp]
    refine ⟨hhash.1, fun i ↦ ?_⟩
    apply Eq.trans _ (hhash.2 i)
    apply hat.byte
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    obtain ⟨j, hj, heq⟩ := hcov
    have hi : i.val < 20 := by
      have := i.isLt
      simp only [Wrapper.Hash.Serialize.stateBytes_size] at this
      exact this
    have hn := congrArg BitVec.toNat heq
    change (BitVec.ofNat 64 ((stackPtr s).toNat + 0x100 + i.val)).toNat =
      (stackPtr s + BitVec.ofNat 64 0xf8 + BitVec.ofNat 64 j).toNat at hn
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.toFrame.address hs (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    omega
  · rw [htsp, ← hvsp]
    have hm := hmovAg.external (by simp [Component.Covers])
    change memLoad t.external (stackPtr v + 0xf8) 64 = _
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

end Sha1.Proofs.Buffered.DigestPrepare.Long
