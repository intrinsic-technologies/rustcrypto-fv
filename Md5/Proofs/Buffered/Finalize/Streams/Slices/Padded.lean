import Md5.Proofs.Buffered.Finalize.Streams.Slices.Prefix
import Md5.Proofs.Buffered.Finalize.Streams.Slices.PaddingBytes
import Md5.Proofs.Buffered.Finalize.Streams.Slices.PaddingFrame
import Md5.Proofs.Buffered.Finalize.Streams.Preserve

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

structure Padded [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) (update : Bool := false) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = (BitVec.ofNat 64 (relocated update 0x100483))
  storage : Storage (streamKind update) t
  padded : (⟨(stackPtr t + 16).toNat, 64⟩ : MemoryRegion).HasBytes t.external (firstBlock message)
  result : (⟨(stackPtr t).toNat, 16⟩ : MemoryRegion).HasBytes t.external
    ⟨(absorbedBuffer message).toBytes.toArray⟩
  blocks : (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64)
  position : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64)
  remaining : (Operand.reg 3 : Operand 64).read t = BitVec.ofNat 64 (63 - message.size % 64)
  df : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  rsp : stackPtr t = stackPtr s
  agrees : AgreesExcept ((streamKind update).changes s) s t

theorem pad {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre (streamKind update) boundary message s) : ∃ t, Padded (update := update) boundary message s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    obtain ⟨u, hu⟩ := prepare_state (update := update) h
    have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
    have hbound : ((.reg 15 : Operand 64).read u).toNat < 64 := by
      rw [hu.position, BitVec.toNat_ofNat]
      omega
    obtain ⟨setupFuel, v, hsetup, hv, hcv, he⟩ := padding_run (update := update) hu.ready hu.code hu.storage
      h.boundaryOutside hu.rip hbound
    have hsv := hu.storage.of_agrees he.agrees (padding_rsp he)
    obtain ⟨t, ht⟩ := memset_run (update := update) h.stride hu.storage hu.position hn hu.df.df he hv hcv h.boundaryOutside
    have hp := padding_bytes_pre (update := update) hu.storage hu.position hu.absorbed he
    have hsp : stackPtr t = stackPtr u := ht.rsp.trans (padding_rsp he)
    have hDst : rdi.read v = stackPtr v + BitVec.ofNat 64 (message.size % 64 + 17) := by
      rw [hp.destination, padding_rsp he]
      change stackPtr u + BitVec.ofNat 64 16 + BitVec.ofNat 64 (message.size % 64 + 1) = _
      rw [add_ofNat_add_ofNat]
      congr 2
      omega
    have hf := memset_firstBlock_bytes ht hp
    have hb0 : Bytes u.external (stackPtr u) 16
        (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, ByteArray.size, Vector.size_toArray]
        using bytes_of_hasBytes hu.result
    have hb1 := padding_preserves_bytes he hb0 (by
      rw [hu.position]
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using
        RangeApart.offsets (stackPtr u) (a := 0) (len := 16)
          (b := message.size % 64 + 16) (count := 1)
          (by decide) (by omega) (Or.inl (by omega)))
    have hb2 := call_preserves_bytes ht.toCallSiteResult hb1 (by
      rw [hDst, padding_rsp he, hp.length]
      simpa using RangeApart.offsets (stackPtr u) (a := 0) (len := 16)
        (b := message.size % 64 + 17) (count := 63 - message.size % 64)
        (by decide) (by omega) (Or.inl (by omega))) (by
      have hh := hsv.stackApartPush (offset := 0) (len := 16) (by decide)
      rw [padding_rsp he] at hh
      simpa using hh)
    have hag1 := padding_agrees hu.position hn he
    have hag2 := call_agrees (update := update) ht.toCallSiteResult hDst (by rw [hp.length]; omega)
    have hchangesU : (streamKind update).changes u = (streamKind update).changes s := by
      simp only [update, streamKind, Bool.false_eq_true, ↓reduceIte, Kind.changes, Kind.localChanges, hu.rsp]
    have hchangesV : (streamKind update).changes v = (streamKind update).changes s := by
      simp only [update, streamKind, Bool.false_eq_true, ↓reduceIte, Kind.changes, Kind.localChanges, padding_rsp he, hu.rsp]
    rw [hchangesU] at hag1
    rw [hchangesV] at hag2
    have hag : AgreesExcept ((streamKind update).changes s) s t :=
      ((hu.agrees.trans hag1).trans hag2).mono (by
        intro c hc
        simpa only [List.mem_append, or_self] using hc)
    obtain ⟨prefixFuel, hprefix⟩ := hu.advances
    obtain ⟨callFuel, hcall⟩ := ht.advances
    refine ⟨t, ⟨⟨prefixFuel + setupFuel + callFuel, (hprefix.trans hsetup).trans hcall⟩,
      ht.ready, ht.code, ht.rip, hsv.of_agrees ht.agrees ht.rsp, ?_, ?_, ?_, ?_, ?_,
      hag.directionFlagClear (by simp [update, streamKind, Kind.changes, Kind.workRegisters, Kind.localChanges]) h.df,
      hsp.trans hu.rsp, hag⟩⟩
    · rw [hsp]
      have hb : Bytes t.external (stackPtr u + 16) (firstBlock message).size
          (fun i ↦ (firstBlock message)[i]!) := by simpa only [size_firstBlock] using hf
      simpa only [size_firstBlock] using hasBytes_of_bytes hb
    · rw [hsp]
      have hb : Bytes t.external (stackPtr u)
          (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray).size
          (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
        simpa only [ByteArray.size, Vector.size_toArray] using hb2
      simpa only [ByteArray.size, Vector.size_toArray] using hasBytes_of_bytes hb
    · rw [ht.agrees.read (n := 64) (r := 14) (by simp [callSiteChanges]),
        he.agrees.read (n := 64) (r := 14) (by simp [paddingEffect, Effect.components])]
      exact hu.blocks
    · rw [ht.agrees.read (n := 64) (r := 15) (by simp [callSiteChanges]),
        he.agrees.read (n := 64) (r := 15) (by simp [paddingEffect, Effect.components])]
      exact hu.position
    · rw [ht.agrees.read (n := 64) (r := 3) (by simp [callSiteChanges]), he.writes.1,
        hu.position, FinalizeReset.remainingBytes _ hn]

end Md5.Proofs.Buffered.Finalize.Streams.Slices
