import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.PaddingRun
import Md5.Proofs.Buffered.Finalize.Streams.PaddedBytes
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem padding_marker {variant : Variant} {s t : RamState} {n : Nat} (hs : Storage variant.toKind s)
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (he : (paddingEffect s variant).Holds s t) :
    t.external[stackPtr s + BitVec.ofNat 64 variant.tailOffset + BitVec.ofNat 64 n]? = some 128 := by
  cases variant with
  | original =>
      have hw := hs.stackWritable (n + 96) 1 (by change _ ≤ 296; omega)
      have hm : ∀ i < 8 / 8,
          (t.external[stackPtr s + BitVec.ofNat 64 (n + 96) + BitVec.ofNat 64 i]?).isSome := by
        intro i hi
        exact he.agrees.grow _ (hw.bytes i hi)
      have hb := Bytes.of_memLoad (n := 8) hm
      have hread : memLoad t.external (stackPtr s + BitVec.ofNat 64 (n + 96)) 8 = (128 : BitVec 8) := by
        have hh := he.writes.2.1
        change (.mem (stackPtr s + (.reg 15 : Operand 64).read s + 96) : Operand 8).read t = 128 at hh
        rw [hp] at hh
        simpa [Operand.read, BitVec.ofNat_add, BitVec.add_assoc] using hh
      rw [hread] at hb
      have hh := hb 0 (by decide)
      have hadd : stackPtr s + BitVec.ofNat 64 96 + BitVec.ofNat 64 n =
          stackPtr s + BitVec.ofNat 64 (n + 96) := by
        change stackPtr s + BitVec.ofNat 64 96 + BitVec.ofNat 64 n = _
        rw [add_ofNat_add_ofNat, Nat.add_comm 96 n]
      simp only [Variant.tailOffset]
      rw [hadd]
      simpa [storedByte] using hh
  | finalize =>
      have hw := hs.stackWritable (n + 96) 1 (by change _ ≤ 296; omega)
      have hm : ∀ i < 8 / 8,
          (t.external[stackPtr s + BitVec.ofNat 64 (n + 96) + BitVec.ofNat 64 i]?).isSome := by
        intro i hi
        exact he.agrees.grow _ (hw.bytes i hi)
      have hb := Bytes.of_memLoad (n := 8) hm
      have hread : memLoad t.external (stackPtr s + BitVec.ofNat 64 (n + 96)) 8 = (128 : BitVec 8) := by
        have hh := he.writes.2.1
        change (.mem (stackPtr s + (.reg 15 : Operand 64).read s + 96) : Operand 8).read t = 128 at hh
        rw [hp] at hh
        simpa [Operand.read, BitVec.ofNat_add, BitVec.add_assoc] using hh
      rw [hread] at hb
      have hh := hb 0 (by decide)
      have hadd : stackPtr s + BitVec.ofNat 64 96 + BitVec.ofNat 64 n =
          stackPtr s + BitVec.ofNat 64 (n + 96) := by
        change stackPtr s + BitVec.ofNat 64 96 + BitVec.ofNat 64 n = _
        rw [add_ofNat_add_ofNat, Nat.add_comm 96 n]
      simp only [Variant.tailOffset]
      rw [hadd]
      simpa [storedByte] using hh
  | discard =>
      have hw := hs.stackWritable (n + 136) 1 (by change _ ≤ 288; omega)
      have hm : ∀ i < 8 / 8,
          (t.external[stackPtr s + BitVec.ofNat 64 (n + 136) + BitVec.ofNat 64 i]?).isSome := by
        intro i hi
        exact he.agrees.grow _ (hw.bytes i hi)
      have hb := Bytes.of_memLoad (n := 8) hm
      have hread : memLoad t.external (stackPtr s + BitVec.ofNat 64 (n + 136)) 8 = (128 : BitVec 8) := by
        have hh := he.writes.2.1
        change (.mem (stackPtr s + (.reg 15 : Operand 64).read s + 136) : Operand 8).read t = 128 at hh
        rw [hp] at hh
        simpa [Operand.read, BitVec.ofNat_add, BitVec.add_assoc] using hh
      rw [hread] at hb
      have hh := hb 0 (by decide)
      have hadd : stackPtr s + BitVec.ofNat 64 136 + BitVec.ofNat 64 n =
          stackPtr s + BitVec.ofNat 64 (n + 136) := by
        change stackPtr s + BitVec.ofNat 64 136 + BitVec.ofNat 64 n = _
        rw [add_ofNat_add_ofNat, Nat.add_comm 136 n]
      simp only [Variant.tailOffset]
      rw [hadd]
      simpa [storedByte] using hh
theorem padding_tail {variant : Variant} {s t : RamState} {message : ByteArray}
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (ha : Absorbed (stackPtr s + BitVec.ofNat 64 variant.tailOffset) message s) (he : (paddingEffect s variant).Holds s t) :
    Bytes t.external (stackPtr s + BitVec.ofNat 64 variant.tailOffset) (message.size % 64)
      (fun i ↦ (tailBytes message)[i]!) := by
  cases variant with
  | original =>
      have ht : Bytes s.external (stackPtr s + BitVec.ofNat 64 96) (message.size % 64)
          (fun i ↦ (tailBytes message)[i]!) := by
        simpa only [Variant.tailOffset, BitVec.ofNat_toNat, BitVec.setWidth_eq, size_tailBytes]
          using bytes_of_hasBytes ha.tail
      intro i hi
      apply Eq.trans _ (ht i hi)
      apply he.agrees.byte
      intro c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      obtain ⟨j, hj, hh⟩ := hcover
      have hsep := RangeApart.offsets (stackPtr s) (a := 96) (len := message.size % 64)
        (b := message.size % 64 + 96) (count := 1) (by omega) (by omega) (Or.inl (by omega))
      apply hsep i hi j hj
      rw [hp] at hh
      simpa [Variant.tailOffset, BitVec.ofNat_add, BitVec.add_assoc] using hh
  | finalize =>
      have ht : Bytes s.external (stackPtr s + BitVec.ofNat 64 96) (message.size % 64)
          (fun i ↦ (tailBytes message)[i]!) := by
        simpa only [Variant.tailOffset, BitVec.ofNat_toNat, BitVec.setWidth_eq, size_tailBytes]
          using bytes_of_hasBytes ha.tail
      intro i hi
      apply Eq.trans _ (ht i hi)
      apply he.agrees.byte
      intro c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      obtain ⟨j, hj, hh⟩ := hcover
      have hsep := RangeApart.offsets (stackPtr s) (a := 96) (len := message.size % 64)
        (b := message.size % 64 + 96) (count := 1) (by omega) (by omega) (Or.inl (by omega))
      apply hsep i hi j hj
      rw [hp] at hh
      simpa [Variant.tailOffset, BitVec.ofNat_add, BitVec.add_assoc] using hh
  | discard =>
      have ht : Bytes s.external (stackPtr s + BitVec.ofNat 64 136) (message.size % 64)
          (fun i ↦ (tailBytes message)[i]!) := by
        simpa only [Variant.tailOffset, BitVec.ofNat_toNat, BitVec.setWidth_eq, size_tailBytes]
          using bytes_of_hasBytes ha.tail
      intro i hi
      apply Eq.trans _ (ht i hi)
      apply he.agrees.byte
      intro c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      obtain ⟨j, hj, hh⟩ := hcover
      have hsep := RangeApart.offsets (stackPtr s) (a := 136) (len := message.size % 64)
        (b := message.size % 64 + 136) (count := 1) (by omega) (by omega) (Or.inl (by omega))
      apply hsep i hi j hj
      rw [hp] at hh
      simpa [Variant.tailOffset, BitVec.ofNat_add, BitVec.add_assoc] using hh
theorem padding_bytes_pre {variant : Variant} {s t : RamState} {message : ByteArray}
    (hs : Storage variant.toKind s)
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (ha : Absorbed (stackPtr s + BitVec.ofNat 64 variant.tailOffset) message s) (he : (paddingEffect s variant).Holds s t) :
    PaddingBytesPre message (stackPtr s + BitVec.ofNat 64 variant.tailOffset) t := by
  cases variant with
  | original =>
      have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
      have hsp := (padding_rsp (variant := .original)) he
      refine ⟨(padding_tail (variant := .original)) hp ha he, (padding_marker (variant := .original)) hs hp hn he, ?_, ?_, ?_, ?_⟩
      · rw [he.writes.2.2.1, hp]
        change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 97 =
          stackPtr s + BitVec.ofNat 64 96 + BitVec.ofNat 64 (message.size % 64 + 1)
        rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat]
        congr 2
        omega
      · rw [he.writes.2.2.2.2, hp, FinalizeReset.remainingBytes _ hn,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · rw [he.writes.2.2.2.1]
        rfl
      · have hh := (hs.of_agrees he.agrees hsp).stackApartPush (offset := 96)
          (len := message.size % 64 + 1) (by change _ ≤ 296; omega)
        rw [hsp] at hh
        exact hh
  | finalize =>
      have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
      have hsp := (padding_rsp (variant := .finalize)) he
      refine ⟨(padding_tail (variant := .finalize)) hp ha he, (padding_marker (variant := .finalize)) hs hp hn he, ?_, ?_, ?_, ?_⟩
      · rw [he.writes.2.2.1, hp]
        change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 97 =
          stackPtr s + BitVec.ofNat 64 96 + BitVec.ofNat 64 (message.size % 64 + 1)
        rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat]
        congr 2
        omega
      · rw [he.writes.2.2.2.2, hp, FinalizeReset.remainingBytes _ hn,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · rw [he.writes.2.2.2.1]
        rfl
      · have hh := (hs.of_agrees he.agrees hsp).stackApartPush (offset := 96)
          (len := message.size % 64 + 1) (by change _ ≤ 296; omega)
        rw [hsp] at hh
        exact hh
  | discard =>
      have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
      have hsp := (padding_rsp (variant := .discard)) he
      refine ⟨(padding_tail (variant := .discard)) hp ha he, (padding_marker (variant := .discard)) hs hp hn he, ?_, ?_, ?_, ?_⟩
      · rw [he.writes.2.2.1, hp]
        change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 137 =
          stackPtr s + BitVec.ofNat 64 136 + BitVec.ofNat 64 (message.size % 64 + 1)
        rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat]
        congr 2
        omega
      · rw [he.writes.2.2.2.2, hp, FinalizeReset.remainingBytes _ hn,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · rw [he.writes.2.2.2.1]
        rfl
      · have hh := (hs.of_agrees he.agrees hsp).stackApartPush (offset := 136)
          (len := message.size % 64 + 1) (by change _ ≤ 288; omega)
        rw [hsp] at hh
        exact hh
theorem padding_preserves_bytes {variant : Variant} {s t : RamState} {base : BitVec 64}
    {len : Nat} {bytes : Nat → UInt8} (he : (paddingEffect s variant).Holds s t)
    (hb : Bytes s.external base len bytes)
    (ha : RangeApart base len (stackPtr s + (.reg 15 : Operand 64).read s + BitVec.ofNat 64 variant.tailOffset) 1) :
    Bytes t.external base len bytes := by
  cases variant with
  | original =>
      apply hb.of_agreesExcept he.agrees
      intro i hi c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      obtain ⟨j, hj, hh⟩ := hcover
      exact ha i hi j hj hh
  | finalize =>
      apply hb.of_agreesExcept he.agrees
      intro i hi c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      obtain ⟨j, hj, hh⟩ := hcover
      exact ha i hi j hj hh
  | discard =>
      apply hb.of_agreesExcept he.agrees
      intro i hi c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      obtain ⟨j, hj, hh⟩ := hcover
      exact ha i hi j hj hh

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
