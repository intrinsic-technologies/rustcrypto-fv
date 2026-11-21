import Md5.Proofs.Buffered.Finalize.Digest.Padding.Contracts
import Md5.Proofs.Buffered.Finalize.Streams.PaddedBytes
import Md5.Proofs.Buffered.Finalize.Streams.Preserve
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.Finalize.Digest.Padding

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem effect_preserves_bytes {s t : RamState} {base : BitVec 64}
    {len : Nat} {bytes : Nat → UInt8} (he : (effect s).Holds s t)
    (hb : Bytes s.external base len bytes)
    (ha : RangeApart base len (stackPtr s + (.reg 12 : Operand 64).read s + 24) 1) :
    Bytes t.external base len bytes := by
  apply hb.of_agreesExcept he.agrees
  intro i hi c hc hcover
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨j, hj, hh⟩ := hcover
  exact ha i hi j hj hh

theorem effect_marker {s t : RamState} {n : Nat} (hs : Storage .digest s)
    (hp : (.reg 12 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (he : (effect s).Holds s t) :
    t.external[stackPtr s + 24 + BitVec.ofNat 64 n]? = some 128 := by
  have hw := hs.stackWritable (n + 24) 1 (by change _ ≤ 264; omega)
  have hm : ∀ i < 8 / 8,
      (t.external[stackPtr s + BitVec.ofNat 64 (n + 24) + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    exact he.agrees.grow _ (hw.bytes i hi)
  have hb := Bytes.of_memLoad (n := 8) hm
  have hread : memLoad t.external (stackPtr s + BitVec.ofNat 64 (n + 24)) 8 =
      (128 : BitVec 8) := by
    have hh := he.writes.1
    change (.mem (stackPtr s + (.reg 12 : Operand 64).read s + 24) : Operand 8).read t = 128 at hh
    rw [hp] at hh
    simpa [Operand.read, BitVec.ofNat_add, BitVec.add_assoc] using hh
  rw [hread] at hb
  have hh := hb 0 (by decide)
  have hadd : stackPtr s + 24 + BitVec.ofNat 64 n =
      stackPtr s + BitVec.ofNat 64 (n + 24) := by
    change stackPtr s + BitVec.ofNat 64 24 + BitVec.ofNat 64 n = _
    rw [add_ofNat_add_ofNat, Nat.add_comm 24 n]
  rw [hadd]
  simpa [storedByte] using hh

theorem effect_padding_bytes [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Input boundary message s) (he : (effect s).Holds s t) :
    Streams.PaddingBytesPre message (stackPtr s + 24) t := by
  have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have hsp := effect_rsp he
  refine ⟨?_, effect_marker h.toStorage h.positionEq hn he, ?_, ?_, ?_, ?_⟩
  · apply effect_preserves_bytes he
    · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, size_tailBytes]
        using bytes_of_hasBytes h.tail
    · rw [h.positionEq]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        RangeApart.offsets (stackPtr s) (a := 24) (len := message.size % 64)
          (b := message.size % 64 + 24) (count := 1)
          (by omega) (by omega) (Or.inl (by omega))
  · rw [he.writes.2.1, h.positionEq]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 25 =
      stackPtr s + BitVec.ofNat 64 24 + BitVec.ofNat 64 (message.size % 64 + 1)
    rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat]
    congr 2
    omega
  · rw [he.writes.2.2.2, h.remainingEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [he.writes.2.2.1]
    rfl
  · have hh := (h.toStorage.of_agrees he.agrees hsp).stackApartPush (offset := 24)
      (len := message.size % 64 + 1) (by change _ ≤ 264; omega)
    rw [hsp] at hh
    exact hh

theorem effect_agrees {s t : RamState} {n : Nat}
    (hp : (.reg 12 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (he : (effect s).Holds s t) : AgreesExcept (Kind.digest.changes s) s t := by
  apply he.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro address c hc hcover
    refine ⟨.mem (stackPtr s + 8) 168, by simp [Kind.changes, Kind.localChanges], ?_⟩
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    apply FinalizeReset.Export.covers_shift (offset := n + 16) (len := 1) _ (by omega)
    rw [hp] at hcover
    have hadd : stackPtr s + BitVec.ofNat 64 n + 24 =
        (stackPtr s + 8) + BitVec.ofNat 64 (n + 16) := by
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      rw [← BitVec.add_assoc (8 : BitVec 64), BitVec.add_comm (8 : BitVec 64)]
      simp only [BitVec.add_assoc]
      rfl
    rwa [← hadd]

theorem call_agrees [Bindings] {boundary : ReturnBoundary} {ret : BitVec 64}
    {s t : RamState} {offset : Nat} (h : CallSiteResult boundary ret s t)
    (hdst : rdi.read s = stackPtr s + BitVec.ofNat 64 (8 + offset))
    (hlen : offset + (MemoryRoutines.rdx.read s).toNat ≤ 168) :
    AgreesExcept (Kind.digest.changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro address c hc hcover
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    · refine ⟨.mem (stackPtr s + 8) 168, by simp [Kind.changes, Kind.localChanges], ?_⟩
      rw [hdst, BitVec.ofNat_add, ← BitVec.add_assoc] at hcover
      exact FinalizeReset.Export.covers_shift hcover hlen
    · refine ⟨.mem (stackPtr s - 320) 320, by simp [Kind.changes], ?_⟩
      have hpush : pushAddr s = stackPtr s - 320 + BitVec.ofNat 64 312 := by
        simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [hpush] at hcover
      exact FinalizeReset.Export.covers_shift hcover (by decide)

theorem pad [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {message : ByteArray} {s : RamState}
    (h : Input boundary message s) : ∃ t, Result boundary message s t := by
  obtain ⟨setupFuel, u, hsetup, hu, hcu, he⟩ := run h.ready h.code h.boundaryOutside h.toRunPre
  have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have hspu := effect_rsp he
  have hsu := h.toStorage.of_agrees he.agrees hspu
  have hp := effect_padding_bytes h he
  have hDst : rdi.read u = stackPtr u + BitVec.ofNat 64 (message.size % 64 + 25) := by
    rw [hp.destination, hspu]
    change stackPtr s + BitVec.ofNat 64 24 + BitVec.ofNat 64 (message.size % 64 + 1) = _
    rw [add_ofNat_add_ofNat]
    congr 2
    omega
  have hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 (63 - message.size % 64) :=
    he.writes.2.2.2.trans h.remainingEq
  obtain ⟨t, ht⟩ := memset hstride hu hcu h.boundaryOutside hsu he.rip
    (he.agrees.directionFlagClear (by simp [effect, Effect.components]) ⟨h.df⟩).df hn hDst hdx
  have hsp := ht.rsp.trans hspu
  have hf := Streams.memset_firstBlock_bytes ht hp
  have hb0 : Bytes s.external (stackPtr s + 8) 16
      (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, ByteArray.size, Vector.size_toArray]
      using bytes_of_hasBytes h.buffer
  have hb1 := effect_preserves_bytes he hb0 (by
    rw [h.positionEq]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
      RangeApart.offsets (stackPtr s) (a := 8) (len := 16)
        (b := message.size % 64 + 24) (count := 1)
        (by decide) (by omega) (Or.inl (by omega)))
  have hb2 := Streams.call_preserves_bytes ht.toCallSiteResult hb1 (by
    rw [hDst, hspu, hp.length]
    exact RangeApart.offsets (stackPtr s) (a := 8) (len := 16)
      (b := message.size % 64 + 25) (count := 63 - message.size % 64)
      (by decide) (by omega) (Or.inl (by omega))) (by
    have hh := hsu.stackApartPush (offset := 8) (len := 16) (by decide)
    rw [hspu] at hh
    exact hh)
  have hag1 := effect_agrees h.positionEq hn he
  have hag2 := call_agrees ht.toCallSiteResult (offset := message.size % 64 + 17) (by
    rw [hDst]
    congr 2
    omega) (by rw [hp.length]; omega)
  have hchanges : Kind.digest.changes u = Kind.digest.changes s := by
    simp only [Kind.changes, Kind.localChanges, hspu]
  rw [hchanges] at hag2
  have hag : AgreesExcept (Kind.digest.changes s) s t := (hag1.trans hag2).mono (by
    intro c hc
    simpa only [List.mem_append, or_self] using hc)
  obtain ⟨callFuel, hcall⟩ := ht.advances
  refine ⟨t, ⟨⟨setupFuel + callFuel, hsetup.trans hcall⟩, ht.ready, ht.code, ht.rip,
    hsu.of_agrees ht.agrees ht.rsp, hsp, ?_, ?_, ?_, ?_, ?_, hag⟩⟩
  · rw [ht.agrees.read (n := 64) (r := 12) (by simp [callSiteChanges]),
      he.agrees.read (n := 64) (r := 12) (by simp [effect, Effect.components])]
    exact h.positionEq
  · rw [ht.agrees.read (n := 64) (r := 14) (by simp [callSiteChanges]),
      he.agrees.read (n := 64) (r := 14) (by simp [effect, Effect.components])]
    exact h.remainingEq
  · rw [ht.agrees.read (n := 64) (r := 15) (by simp [callSiteChanges]),
      he.agrees.read (n := 64) (r := 15) (by simp [effect, Effect.components])]
    exact h.blocksEq
  · rw [hsp]
    exact hf
  · rw [hsp]
    have hb : Bytes t.external (stackPtr s + 8)
        (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray).size
        (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) := by
      simpa only [ByteArray.size, Vector.size_toArray] using hb2
    simpa only [ByteArray.size, Vector.size_toArray] using Finalize.hasBytes_of_bytes hb

end Md5.Proofs.Buffered.Finalize.Digest.Padding
