import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Contracts
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.PaddingBytes
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.PaddingFrame
import Md5.Proofs.Buffered.Finalize.Streams.Preserve

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem complete {variant : Variant} [bindings : Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {u : RamState} (hu : Prefix message u variant) (hstride : UnitStringStride bindings)
    (hout : ¬ InProgram boundary.rip) :
    ∃ t, Transition boundary u t variant ∧ Prepared message t variant := by
  cases variant with
  | original =>
      have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
      have hbound : ((.reg 15 : Operand 64).read u).toNat < 64 := by
        rw [hu.position, BitVec.toNat_ofNat]
        omega
      obtain ⟨setupFuel, v, hsetup, hv, hcv, he⟩ := (padding_run (variant := .original)) hu.ready hu.code hu.toStorage
        hout hu.rip hbound
      have hsv := hu.toStorage.of_agrees he.agrees ((padding_rsp (variant := .original)) he)
      obtain ⟨t, ht⟩ := (memset_run (variant := .original)) hstride hu.toStorage hu.position hn hu.df he hv hcv hout
      have hp := (padding_bytes_pre (variant := .original)) hu.toStorage hu.position hu.absorbed he
      have hsp : stackPtr t = stackPtr u := ht.rsp.trans ((padding_rsp (variant := .original)) he)
      have hDst : rdi.read v = stackPtr v + 96 + BitVec.ofNat 64 (message.size % 64 + 1) := by
        simp only [hp.destination, Variant.tailOffset, (padding_rsp (variant := .original)) he]
        rfl
      have hf := memset_firstBlock_bytes ht hp
      have hb0 : Bytes u.external (stackPtr u + 216) 16
          (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
        have haddr : BitVec.ofNat 64 ((stackPtr u).toNat + 216) = stackPtr u + 216 := by
          rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rfl
        simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, haddr, ByteArray.size, Vector.size_toArray] using bytes_of_hasBytes hu.buffer
      have hb1 := (padding_preserves_bytes (variant := .original)) he hb0 (by
        rw [hu.position]
        simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.add_assoc] using
          RangeApart.offsets (stackPtr u) (a := 216) (len := 16)
            (b := message.size % 64 + 96) (count := 1)
            (by decide) (by omega) (Or.inr (by omega)))
      have hb2 := call_preserves_bytes ht.toCallSiteResult hb1 (by
        rw [hDst, (padding_rsp (variant := .original)) he, hp.length]
        change RangeApart (stackPtr u + BitVec.ofNat 64 216) 16
          (stackPtr u + BitVec.ofNat 64 96 + BitVec.ofNat 64 (message.size % 64 + 1)) _
        rw [add_ofNat_add_ofNat]
        exact RangeApart.offsets (stackPtr u) (a := 216) (len := 16)
          (b := 96 + (message.size % 64 + 1)) (count := 63 - message.size % 64)
          (by decide) (by omega) (Or.inr (by omega))) (by
        have hh := hsv.stackApartPush (offset := 216) (len := 16) (by decide)
        rw [(padding_rsp (variant := .original)) he] at hh
        exact hh)
      have hag1 := (padding_agrees (variant := .original)) hu.position hn he
      have hag2 := (call_agrees (variant := .original)) ht.toCallSiteResult hDst (by rw [hp.length]; omega)
      have hchangesV : Kind.resetSecond.changes v = Kind.resetSecond.changes u := by
        simp only [Kind.changes, Kind.localChanges, (padding_rsp (variant := .original)) he]
      simp only [Variant.toKind] at hag2
      rw [hchangesV] at hag2
      have hag : AgreesExcept (Kind.resetSecond.changes u) u t :=
        (hag1.trans hag2).mono (by
          intro c hc
          simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, List.mem_append, or_self] using hc)
      obtain ⟨callFuel, hcall⟩ := ht.advances
      refine ⟨t, ⟨⟨setupFuel + callFuel, hsetup.trans hcall⟩, hag⟩,
        ⟨hsv.of_agrees ht.agrees ht.rsp, ht.ready, ht.code, ht.rip, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hsp]
        exact hf
      · rw [hsp]
        have hb : Bytes t.external (stackPtr u + 216)
            (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray).size
            (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
          simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, ByteArray.size, Vector.size_toArray] using hb2
        have haddr : (stackPtr u + 216).toNat = (stackPtr u).toNat + 216 :=
          hu.toStorage.stackAddress (offset := 216) (by decide)
        simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, haddr, ByteArray.size, Vector.size_toArray] using hasBytes_of_bytes hb
      · rw [ht.agrees.read (n := 64) (r := 14) (by simp [callSiteChanges]),
          he.agrees.read (n := 64) (r := 14) (by simp [Variant.tailOffset, paddingEffect, Effect.components])]
        exact hu.blocks
      · rw [ht.agrees.read (n := 64) (r := 15) (by simp [callSiteChanges]),
          he.agrees.read (n := 64) (r := 15) (by simp [Variant.tailOffset, paddingEffect, Effect.components])]
        exact hu.position
      · rw [ht.agrees.read (n := 64) (r := 3) (by simp [callSiteChanges]), he.writes.1,
          hu.position, FinalizeReset.remainingBytes _ hn]
  | finalize =>
      have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
      have hbound : ((.reg 15 : Operand 64).read u).toNat < 64 := by
        rw [hu.position, BitVec.toNat_ofNat]
        omega
      obtain ⟨setupFuel, v, hsetup, hv, hcv, he⟩ := (padding_run (variant := .finalize)) hu.ready hu.code hu.toStorage
        hout hu.rip hbound
      have hsv := hu.toStorage.of_agrees he.agrees ((padding_rsp (variant := .finalize)) he)
      obtain ⟨t, ht⟩ := (memset_run (variant := .finalize)) hstride hu.toStorage hu.position hn hu.df he hv hcv hout
      have hp := (padding_bytes_pre (variant := .finalize)) hu.toStorage hu.position hu.absorbed he
      have hsp : stackPtr t = stackPtr u := ht.rsp.trans ((padding_rsp (variant := .finalize)) he)
      have hDst : rdi.read v = stackPtr v + 96 + BitVec.ofNat 64 (message.size % 64 + 1) := by
        simp only [hp.destination, Variant.tailOffset, (padding_rsp (variant := .finalize)) he]
        rfl
      have hf := memset_firstBlock_bytes ht hp
      have hb0 : Bytes u.external (stackPtr u + 216) 16
          (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
        have haddr : BitVec.ofNat 64 ((stackPtr u).toNat + 216) = stackPtr u + 216 := by
          rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rfl
        simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, haddr, ByteArray.size, Vector.size_toArray] using bytes_of_hasBytes hu.buffer
      have hb1 := (padding_preserves_bytes (variant := .finalize)) he hb0 (by
        rw [hu.position]
        simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.add_assoc] using
          RangeApart.offsets (stackPtr u) (a := 216) (len := 16)
            (b := message.size % 64 + 96) (count := 1)
            (by decide) (by omega) (Or.inr (by omega)))
      have hb2 := call_preserves_bytes ht.toCallSiteResult hb1 (by
        rw [hDst, (padding_rsp (variant := .finalize)) he, hp.length]
        change RangeApart (stackPtr u + BitVec.ofNat 64 216) 16
          (stackPtr u + BitVec.ofNat 64 96 + BitVec.ofNat 64 (message.size % 64 + 1)) _
        rw [add_ofNat_add_ofNat]
        exact RangeApart.offsets (stackPtr u) (a := 216) (len := 16)
          (b := 96 + (message.size % 64 + 1)) (count := 63 - message.size % 64)
          (by decide) (by omega) (Or.inr (by omega))) (by
        have hh := hsv.stackApartPush (offset := 216) (len := 16) (by decide)
        rw [(padding_rsp (variant := .finalize)) he] at hh
        exact hh)
      have hag1 := (padding_agrees (variant := .finalize)) hu.position hn he
      have hag2 := (call_agrees (variant := .finalize)) ht.toCallSiteResult hDst (by rw [hp.length]; omega)
      have hchangesV : Kind.finalizeResetSecond.changes v = Kind.finalizeResetSecond.changes u := by
        simp only [Kind.changes, Kind.localChanges, (padding_rsp (variant := .finalize)) he]
      simp only [Variant.toKind] at hag2
      rw [hchangesV] at hag2
      have hag : AgreesExcept (Kind.finalizeResetSecond.changes u) u t :=
        (hag1.trans hag2).mono (by
          intro c hc
          simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, List.mem_append, or_self] using hc)
      obtain ⟨callFuel, hcall⟩ := ht.advances
      refine ⟨t, ⟨⟨setupFuel + callFuel, hsetup.trans hcall⟩, hag⟩,
        ⟨hsv.of_agrees ht.agrees ht.rsp, ht.ready, ht.code, ht.rip, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hsp]
        exact hf
      · rw [hsp]
        have hb : Bytes t.external (stackPtr u + 216)
            (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray).size
            (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
          simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, ByteArray.size, Vector.size_toArray] using hb2
        have haddr : (stackPtr u + 216).toNat = (stackPtr u).toNat + 216 :=
          hu.toStorage.stackAddress (offset := 216) (by decide)
        simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, haddr, ByteArray.size, Vector.size_toArray] using hasBytes_of_bytes hb
      · rw [ht.agrees.read (n := 64) (r := 14) (by simp [callSiteChanges]),
          he.agrees.read (n := 64) (r := 14) (by simp [Variant.tailOffset, paddingEffect, Effect.components])]
        exact hu.blocks
      · rw [ht.agrees.read (n := 64) (r := 15) (by simp [callSiteChanges]),
          he.agrees.read (n := 64) (r := 15) (by simp [Variant.tailOffset, paddingEffect, Effect.components])]
        exact hu.position
      · rw [ht.agrees.read (n := 64) (r := 3) (by simp [callSiteChanges]), he.writes.1,
          hu.position, FinalizeReset.remainingBytes _ hn]
  | discard =>
      have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
      have hbound : ((.reg 15 : Operand 64).read u).toNat < 64 := by
        rw [hu.position, BitVec.toNat_ofNat]
        omega
      obtain ⟨setupFuel, v, hsetup, hv, hcv, he⟩ := (padding_run (variant := .discard)) hu.ready hu.code hu.toStorage
        hout hu.rip hbound
      have hsv := hu.toStorage.of_agrees he.agrees ((padding_rsp (variant := .discard)) he)
      obtain ⟨t, ht⟩ := (memset_run (variant := .discard)) hstride hu.toStorage hu.position hn hu.df he hv hcv hout
      have hp := (padding_bytes_pre (variant := .discard)) hu.toStorage hu.position hu.absorbed he
      have hsp : stackPtr t = stackPtr u := ht.rsp.trans ((padding_rsp (variant := .discard)) he)
      have hDst : rdi.read v = stackPtr v + 136 + BitVec.ofNat 64 (message.size % 64 + 1) := by
        simp only [hp.destination, Variant.tailOffset, (padding_rsp (variant := .discard)) he]
        rfl
      have hf := memset_firstBlock_bytes ht hp
      have hb0 : Bytes u.external (stackPtr u + 120) 16
          (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
        have haddr : BitVec.ofNat 64 ((stackPtr u).toNat + 120) = stackPtr u + 120 := by
          rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rfl
        simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, haddr, ByteArray.size, Vector.size_toArray] using bytes_of_hasBytes hu.buffer
      have hb1 := (padding_preserves_bytes (variant := .discard)) he hb0 (by
        rw [hu.position]
        simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.add_assoc] using
          RangeApart.offsets (stackPtr u) (a := 120) (len := 16)
            (b := message.size % 64 + 136) (count := 1)
            (by decide) (by omega) (Or.inl (by omega)))
      have hb2 := call_preserves_bytes ht.toCallSiteResult hb1 (by
        rw [hDst, (padding_rsp (variant := .discard)) he, hp.length]
        change RangeApart (stackPtr u + BitVec.ofNat 64 120) 16
          (stackPtr u + BitVec.ofNat 64 136 + BitVec.ofNat 64 (message.size % 64 + 1)) _
        rw [add_ofNat_add_ofNat]
        exact RangeApart.offsets (stackPtr u) (a := 120) (len := 16)
          (b := 136 + (message.size % 64 + 1)) (count := 63 - message.size % 64)
          (by decide) (by omega) (Or.inl (by omega))) (by
        have hh := hsv.stackApartPush (offset := 120) (len := 16) (by decide)
        rw [(padding_rsp (variant := .discard)) he] at hh
        exact hh)
      have hag1 := (padding_agrees (variant := .discard)) hu.position hn he
      have hag2 := (call_agrees (variant := .discard)) ht.toCallSiteResult hDst (by rw [hp.length]; omega)
      have hchangesV : Kind.resetDiscardSecond.changes v = Kind.resetDiscardSecond.changes u := by
        simp only [Kind.changes, Kind.localChanges, (padding_rsp (variant := .discard)) he]
      simp only [Variant.toKind] at hag2
      rw [hchangesV] at hag2
      have hag : AgreesExcept (Kind.resetDiscardSecond.changes u) u t :=
        (hag1.trans hag2).mono (by
          intro c hc
          simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, List.mem_append, or_self] using hc)
      obtain ⟨callFuel, hcall⟩ := ht.advances
      refine ⟨t, ⟨⟨setupFuel + callFuel, hsetup.trans hcall⟩, hag⟩,
        ⟨hsv.of_agrees ht.agrees ht.rsp, ht.ready, ht.code, ht.rip, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hsp]
        exact hf
      · rw [hsp]
        have hb : Bytes t.external (stackPtr u + 120)
            (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray).size
            (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
          simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, ByteArray.size, Vector.size_toArray] using hb2
        have haddr : (stackPtr u + 120).toNat = (stackPtr u).toNat + 120 :=
          hu.toStorage.stackAddress (offset := 120) (by decide)
        simpa only [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, haddr, ByteArray.size, Vector.size_toArray] using hasBytes_of_bytes hb
      · rw [ht.agrees.read (n := 64) (r := 14) (by simp [callSiteChanges]),
          he.agrees.read (n := 64) (r := 14) (by simp [Variant.tailOffset, paddingEffect, Effect.components])]
        exact hu.blocks
      · rw [ht.agrees.read (n := 64) (r := 15) (by simp [callSiteChanges]),
          he.agrees.read (n := 64) (r := 15) (by simp [Variant.tailOffset, paddingEffect, Effect.components])]
        exact hu.position
      · rw [ht.agrees.read (n := 64) (r := 3) (by simp [callSiteChanges]), he.writes.1,
          hu.position, FinalizeReset.remainingBytes _ hn]

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
