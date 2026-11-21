import Sha1.Proofs.Buffered.DigestPrepare.Long.Preservation
import Sha1.Proofs.Buffered.DigestPrepare.Position
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.MemoryRoutines.Register.Compose

namespace Sha1.Proofs.Buffered.DigestPrepare.Long

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

def copyBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xb8, 0, 0, 0, 0x4c, 0x89, 0xe6, 0x4c, 0x89, 0xfa]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x1000d4
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 184⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 15 : Operand 64).read s⟩] }

theorem copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1000c6)
      (codeRange 0x1000c6 copyBytes) copyEffect := by
  unfold copyBytes
  md5_run_begin lea_r64_effect_step 0x1000c6 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d32 184)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xce (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x1000ce 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000c6) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd1 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x1000d1 0x4c 0xfa
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000c6) 11 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd4 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [copyEffect]
  · x86_norm [copyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect]

structure CopyReady [Bindings] (initial : RamState) (input : ByteArray) (s : RamState) : Prop
    extends State initial input (absorbedHash input) s where
  rip : s.RIP = 0x1000d4
  destination : rdi.read s = stackPtr s + 184
  source : rsi.read s = initial.regValue .rdi + BitVec.ofNat 64 (input.size / 64 * 64)
  length : MemoryRoutines.rdx.read s = BitVec.ofNat 64 (input.size % 64)
  position : (Operand.mem (stackPtr s + 0xf7) : Operand 8).read s =
    BitVec.ofNat 8 (input.size % 64)

set_option maxRecDepth 2048 in
theorem copy_ready [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hCall : Digest.ValidCall bindings initial input) (h : Compressed initial input s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ CopyReady initial input t := by
  have hs := hCall.stackAvailable
  obtain ⟨u, ha, hu, hcu, he⟩ := position_store hCall h.toFrame (Or.inr rfl) h.rip
  have huf := h.toFrame.after_position_store hCall hu hcu he
  have husp : stackPtr u = stackPtr s :=
    he.agrees.read (n := 64) (r := 4) (by simp [positionStore])
  have hb : CodeIn (codeRange 0x1000c6 copyBytes) u :=
    program_text_slice hcu 0xc6 14 (by decide +kernel)
  obtain ⟨n, t, hat, ht, _, het⟩ := copy_prepare (returnBoundary initial)
    h.boundaryOutside u hu hb he.rip
  have hct := het.agrees.codeIn (by simp [copyEffect, Effect.components, Component.Covers]) hcu
  have htsp : stackPtr t = stackPtr u := het.agrees.read (n := 64) (r := 4)
    (by simp [copyEffect, Effect.components])
  have htf : Frame initial (returnBoundary initial) t := by
    apply huf.preserve hs het.agrees ht hct
    · simp [copyEffect, Effect.components, digestPreparationChanges]
    · simp [copyEffect, Effect.components, Component.Covers]
    · exact htsp
    · exact het.agrees.read (n := 64) (r := 3) (by simp [copyEffect, Effect.components])
    · exact het.agrees.read (n := 64) (r := 14) (by simp [copyEffect, Effect.components])
  have hag : AgreesExcept (shortChanges s (input.size % 64)) s t := by
    have ha := he.agrees.trans het.agrees
    simp only [positionStore, storeEffect_components] at ha
    apply ha.mono
    simp [copyEffect, Effect.components, shortChanges]
  refine ⟨1 + n, t, ha.trans hat,
    ⟨h.toState.preserve hs (Nat.mod_lt _ (by decide)) hag htf, het.rip, ?_, ?_, ?_, ?_⟩⟩
  · rw [het.writes.1, htsp]
  · exact het.writes.2.1.trans
      ((he.agrees.read (n := 64) (r := 12) (by simp [positionStore])).trans h.tailPointer)
  · exact het.writes.2.2.trans
      ((he.agrees.read (n := 64) (r := 15) (by simp [positionStore])).trans h.tailSize)
  · rw [htsp]
    have hm := het.agrees.external (by simp [copyEffect, Effect.components, Component.Covers])
    change memLoad t.external (stackPtr u + 0xf7) 8 = _
    rw [hm, husp]
    apply he.writes.trans
    have hh := congrArg (fun x : BitVec 64 ↦ x.setWidth 8) h.tailSize
    change (s.GPR[gprIndex 15]).setWidth 8 = _
    simpa only [Operand.read_reg64, BitVec.setWidth_ofNat_of_le (v := 8) (w := 64)
      (by decide)] using hh

set_option maxRecDepth 2048 in
theorem copy_tail [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input)
    (h : CopyReady initial input s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      DigestPrepared initial (returnBoundary initial) input t := by
  have hs := hCall.stackAvailable
  have hmod : input.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have hb := h.toFrame.inputBytes hCall
  have hp : MemcpySitePre (0x1000d4 + 6) s :=
    memcpy_site_pre hCall h.toFrame (by omega) (by omega) hb h.destination
      h.source h.length (by decide) (by decide)
  have hw := h.toFrame.scratchWritable hCall (AgreesExcept.refl [] s) 8 8 (by decide) (by decide)
  obtain ⟨t, hr⟩ := digest_memcpy_call hStride h.ready h.code h.boundaryOutside h.rip
    (Or.inr rfl) hp ⟨hw.readable.low, hw.readable.mem, hw.tables⟩
  have hlen : (MemoryRoutines.rdx.read s).toNat = input.size % 64 := by
    rw [h.length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htf := h.toFrame.after_memcpy hCall hr h.destination (by rw [hlen]; omega)
  have hag : AgreesExcept (shortChanges s (input.size % 64)) s t := by
    have ha := hr.agrees
    rw [callSiteChanges, h.destination, hlen] at ha
    exact ha.mono (by simp [shortChanges])
  have htstate := h.toState.preserve hs hmod hag htf
  have hposition := (position_after_memcpy hCall h.toFrame hr h.destination
    (by rw [hlen]; exact hmod)).trans h.position
  have hin : (initial.regValue .rdi).toNat + input.size < 2^32 := hCall.inputInMemory.2.1
  have htail : (⟨(stackPtr t).toNat + 184, (tailBytes input).size⟩ : MemoryRegion).HasBytes
      t.external (tailBytes input) := by
    have hsrc : (rsi.read s).toNat =
        (initial.regValue .rdi).toNat + 64 * (input.size / 64) := by
      rw [h.source, toNat_add_ofNat _ _ (by omega)]
      omega
    have hsbytes : (⟨(rsi.read s).toNat, (tailBytes input).size⟩ : MemoryRegion).HasBytes
        s.external (tailBytes input) := by
      rw [hsrc]
      exact hasBytes_extract hb (64 * (input.size / 64)) input.size
    have hout := memcpy_hasBytes hr (hlen.trans (size_tailBytes input).symm) hsbytes
    have hd : (rdi.read s).toNat = (stackPtr s).toNat + 184 := by
      rw [h.destination]
      exact h.toFrame.address hs (by decide)
    rw [hd] at hout
    rw [hr.rsp]
    exact hout
  have habs : Absorbed (stackPtr t + 0xb8) input t := by
    have hctx : (stackPtr t + 0xb8).toNat = (stackPtr t).toNat + 184 :=
      htf.address hs (by decide)
    have hstate : (stackPtr t + 0xb8 + 72).toNat = (stackPtr t).toNat + 0x100 := by
      change (stackPtr t + BitVec.ofNat 64 0xb8 + BitVec.ofNat 64 72).toNat = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, htf.address hs (by decide)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstate]
      exact htstate.hash
    · rw [hctx]
      exact htail
    · rw [size_tailBytes]
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hposition
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using htstate.blocks
  obtain ⟨fuel, ha⟩ := hr.advances
  exact ⟨fuel, t, ha, htf.finish hCall hStride hr.rip habs (input_size_bounded hCall)⟩

theorem finish_compressed [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input)
    (h : Compressed initial input s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      DigestPrepared initial (returnBoundary initial) input t := by
  obtain ⟨n, u, ha, hu⟩ := copy_ready hCall h
  obtain ⟨m, t, hb, ht⟩ := copy_tail hStride hCall hu
  exact ⟨n + m, t, ha.trans hb, ht⟩

end Sha1.Proofs.Buffered.DigestPrepare.Long
