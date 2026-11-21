import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Prefix.Execution
import Md5.Proofs.Buffered.Finalize.Copy
import Md5.Proofs.Buffered.FinalizeReset.Export.Bytes

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_preserves_context {variant : Variant} {s t : RamState} {message : ByteArray}
    (h : (prepareEffect s variant).Holds s t)
    (ha : Absorbed (stackPtr s + BitVec.ofNat 64 variant.tailOffset) message s) : Absorbed (stackPtr t + BitVec.ofNat 64 variant.tailOffset) message t := by
  cases variant with
  | original =>
      have hsp : stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4)
        (by simp [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components])
      rw [hsp]
      apply absorbed_of_copy ha
      intro i hi
      apply h.agrees.byte
      intro c hc hcover
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      · obtain ⟨j, hj, he⟩ := hcover
        exact RangeApart.offsets (stackPtr s) (a := 96) (len := 88) (b := 224) (count := 8)
          (by decide) (by decide) (by decide) i hi j hj he
      · obtain ⟨j, hj, he⟩ := hcover
        exact RangeApart.offsets (stackPtr s) (a := 96) (len := 88) (b := 216) (count := 8)
          (by decide) (by decide) (by decide) i hi j hj (by simpa only [Variant.tailOffset] using he)
  | finalize =>
      have hsp : stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4)
        (by simp [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components])
      rw [hsp]
      apply absorbed_of_copy ha
      intro i hi
      apply h.agrees.byte
      intro c hc hcover
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      · obtain ⟨j, hj, he⟩ := hcover
        exact RangeApart.offsets (stackPtr s) (a := 96) (len := 88) (b := 224) (count := 8)
          (by decide) (by decide) (by decide) i hi j hj he
      · obtain ⟨j, hj, he⟩ := hcover
        exact RangeApart.offsets (stackPtr s) (a := 96) (len := 88) (b := 216) (count := 8)
          (by decide) (by decide) (by decide) i hi j hj (by simpa only [Variant.tailOffset] using he)
  | discard =>
      have hsp : stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4)
        (by simp [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components])
      rw [hsp]
      apply absorbed_of_copy ha
      intro i hi
      apply h.agrees.byte
      intro c hc hcover
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      · obtain ⟨j, hj, he⟩ := hcover
        exact RangeApart.offsets (stackPtr s) (a := 136) (len := 88) (b := 128) (count := 8)
          (by decide) (by decide) (by decide) i hi j hj he
      · obtain ⟨j, hj, he⟩ := hcover
        exact RangeApart.offsets (stackPtr s) (a := 136) (len := 88) (b := 120) (count := 8)
          (by decide) (by decide) (by decide) i hi j hj (by simpa only [Variant.tailOffset] using he)

theorem prepare_result {variant : Variant} {s t : RamState} {message : ByteArray}
    (hs : Storage variant.toKind s) (h : (prepareEffect s variant).Holds s t)
    (ha : Absorbed (stackPtr s + BitVec.ofNat 64 variant.toKind.contextOffset) message s) :
    (⟨(stackPtr s).toNat + variant.resultOffset, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
  cases variant with
  | original =>
      have hb : (⟨(stackPtr s + BitVec.ofNat 64 72).toNat, 16⟩ : MemoryRegion).HasBytes s.external
          ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
        have he : (stackPtr s + BitVec.ofNat 64 8).toNat + 64 = (stackPtr s + BitVec.ofNat 64 72).toNat := by
          change (stackPtr s + BitVec.ofNat 64 8).toNat + 64 =
            (stackPtr s + BitVec.ofNat 64 72).toNat
          rw [hs.stackAddress (offset := 8) (by decide),
            hs.stackAddress (offset := 72) (by decide)]
        simpa only [Variant.toKind, Kind.contextOffset, he] using ha.buffer
      have hw := h.writes
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Write.AllHold] at hw
      simp only [Variant.resultOffset]
      rw [← hs.stackAddress (offset := 216) (by decide)]
      refine FinalizeReset.Export.hasBytes_of_halves (base := stackPtr s + BitVec.ofNat 64 216)
        (hi := (Operand.mem (stackPtr s + BitVec.ofNat 64 80) : Operand 64).read s)
        (bytes := (absorbedBuffer message).toBytes) ?_ hw.2.2.2.2.2 ?_ ?_ ?_
      · intro i hi
        apply h.agrees.grow
        have hm := (hs.stackWritable 216 16 (by decide)).bytes i hi
        exact hm
      · simpa [BitVec.add_assoc] using hw.2.2.2.2.1
      · intro i
        simpa using FinalizeReset.Export.digest_half hb 0 (by decide) i
      · intro i
        simpa [BitVec.add_assoc] using FinalizeReset.Export.digest_half hb 8 (by decide) i
  | finalize =>
      have hb : (⟨(stackPtr s + BitVec.ofNat 64 72).toNat, 16⟩ : MemoryRegion).HasBytes s.external
          ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
        have he : (stackPtr s + BitVec.ofNat 64 8).toNat + 64 = (stackPtr s + BitVec.ofNat 64 72).toNat := by
          change (stackPtr s + BitVec.ofNat 64 8).toNat + 64 =
            (stackPtr s + BitVec.ofNat 64 72).toNat
          rw [hs.stackAddress (offset := 8) (by decide),
            hs.stackAddress (offset := 72) (by decide)]
        simpa only [Variant.toKind, Kind.contextOffset, he] using ha.buffer
      have hw := h.writes
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Write.AllHold] at hw
      simp only [Variant.resultOffset]
      rw [← hs.stackAddress (offset := 216) (by decide)]
      refine FinalizeReset.Export.hasBytes_of_halves (base := stackPtr s + BitVec.ofNat 64 216)
        (hi := (Operand.mem (stackPtr s + BitVec.ofNat 64 80) : Operand 64).read s)
        (bytes := (absorbedBuffer message).toBytes) ?_ hw.2.2.2.2.2 ?_ ?_ ?_
      · intro i hi
        apply h.agrees.grow
        have hm := (hs.stackWritable 216 16 (by decide)).bytes i hi
        exact hm
      · simpa [BitVec.add_assoc] using hw.2.2.2.2.1
      · intro i
        simpa using FinalizeReset.Export.digest_half hb 0 (by decide) i
      · intro i
        simpa [BitVec.add_assoc] using FinalizeReset.Export.digest_half hb 8 (by decide) i
  | discard =>
      have hb : (⟨(stackPtr s + BitVec.ofNat 64 96).toNat, 16⟩ : MemoryRegion).HasBytes s.external
          ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
        have he : (stackPtr s + BitVec.ofNat 64 32).toNat + 64 = (stackPtr s + BitVec.ofNat 64 96).toNat := by
          change (stackPtr s + BitVec.ofNat 64 32).toNat + 64 =
            (stackPtr s + BitVec.ofNat 64 96).toNat
          rw [hs.stackAddress (offset := 32) (by decide),
            hs.stackAddress (offset := 96) (by decide)]
        simpa only [Variant.toKind, Kind.contextOffset, he] using ha.buffer
      have hw := h.writes
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Write.AllHold] at hw
      simp only [Variant.resultOffset]
      rw [← hs.stackAddress (offset := 120) (by decide)]
      refine FinalizeReset.Export.hasBytes_of_halves (base := stackPtr s + BitVec.ofNat 64 120)
        (hi := (Operand.mem (stackPtr s + BitVec.ofNat 64 104) : Operand 64).read s)
        (bytes := (absorbedBuffer message).toBytes) ?_ hw.2.2.2.2.2 ?_ ?_ ?_
      · intro i hi
        apply h.agrees.grow
        have hm := (hs.stackWritable 120 16 (by decide)).bytes i hi
        exact hm
      · simpa [BitVec.add_assoc] using hw.2.2.2.2.1
      · intro i
        simpa using FinalizeReset.Export.digest_half hb 0 (by decide) i
      · intro i
        simpa [BitVec.add_assoc] using FinalizeReset.Export.digest_half hb 8 (by decide) i

theorem prepare_length {variant : Variant} {s t : RamState} {message : ByteArray}
    (h : (prepareEffect s variant).Holds s t)
    (ha : Absorbed (stackPtr s + BitVec.ofNat 64 variant.tailOffset) message s) :
    (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64) ∧
    (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64) := by
  cases variant with
  | original =>
      have hw := h.writes
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Write.AllHold] at hw
      constructor
      · exact hw.1.trans (by simpa [Variant.tailOffset, BitVec.add_assoc] using ha.blocks)
      · rw [hw.2.1]
        have hp : (Operand.mem (stackPtr s + BitVec.ofNat 64 159) : Operand 8).read s =
            BitVec.ofNat 8 (message.size % 64) := by
          simpa [Variant.tailOffset, BitVec.add_assoc] using ha.position
        rw [hp]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega
  | finalize =>
      have hw := h.writes
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Write.AllHold] at hw
      constructor
      · exact hw.1.trans (by simpa [Variant.tailOffset, BitVec.add_assoc] using ha.blocks)
      · rw [hw.2.1]
        have hp : (Operand.mem (stackPtr s + BitVec.ofNat 64 159) : Operand 8).read s =
            BitVec.ofNat 8 (message.size % 64) := by
          simpa [Variant.tailOffset, BitVec.add_assoc] using ha.position
        rw [hp]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega
  | discard =>
      have hw := h.writes
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Write.AllHold] at hw
      constructor
      · exact hw.1.trans (by simpa [Variant.tailOffset, BitVec.add_assoc] using ha.blocks)
      · rw [hw.2.1]
        have hp : (Operand.mem (stackPtr s + BitVec.ofNat 64 199) : Operand 8).read s =
            BitVec.ofNat 8 (message.size % 64) := by
          simpa [Variant.tailOffset, BitVec.add_assoc] using ha.position
        rw [hp]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega


end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
