import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Streams.Slices.PaddingRun
import Md5.Proofs.Buffered.Finalize.Streams.PaddedBytes
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem padding_marker {update : Bool} {s t : RamState} {n : Nat} (hs : Storage (streamKind update) s)
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (he : (paddingEffect (update := update) s).Holds s t) :
    t.external[stackPtr s + 16 + BitVec.ofNat 64 n]? = some 128 := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hw := hs.stackWritable (n + 16) 1 (by change _ ≤ 280; omega)
    have hm : ∀ i < 8 / 8,
        (t.external[stackPtr s + BitVec.ofNat 64 (n + 16) + BitVec.ofNat 64 i]?).isSome := by
      intro i hi
      exact he.agrees.grow _ (hw.bytes i hi)
    have hb := Bytes.of_memLoad (n := 8) hm
    have hread : memLoad t.external (stackPtr s + BitVec.ofNat 64 (n + 16)) 8 = (128 : BitVec 8) := by
      have hh := he.writes.2.1
      change (.mem (stackPtr s + (.reg 15 : Operand 64).read s + 16) : Operand 8).read t = 128 at hh
      rw [hp] at hh
      simpa [Operand.read, BitVec.ofNat_add, BitVec.add_assoc] using hh
    rw [hread] at hb
    have hh := hb 0 (by decide)
    have hadd : stackPtr s + 16 + BitVec.ofNat 64 n =
        stackPtr s + BitVec.ofNat 64 (n + 16) := by
      change stackPtr s + BitVec.ofNat 64 16 + BitVec.ofNat 64 n = _
      rw [add_ofNat_add_ofNat, Nat.add_comm 16 n]
    rw [hadd]
    simpa [storedByte] using hh

theorem padding_tail {update : Bool} {s t : RamState} {message : ByteArray}
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (ha : Absorbed (stackPtr s + 16) message s) (he : (paddingEffect (update := update) s).Holds s t) :
    Bytes t.external (stackPtr s + 16) (message.size % 64)
      (fun i ↦ (tailBytes message)[i]!) := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have ht : Bytes s.external (stackPtr s + 16) (message.size % 64)
        (fun i ↦ (tailBytes message)[i]!) := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, size_tailBytes] using bytes_of_hasBytes ha.tail
    intro i hi
    apply Eq.trans _ (ht i hi)
    apply he.agrees.byte
    intro c hc hcover
    simp only [paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨j, hj, hh⟩ := hcover
    have hsep := RangeApart.offsets (stackPtr s) (a := 16) (len := message.size % 64)
      (b := message.size % 64 + 16) (count := 1) (by omega) (by omega) (Or.inl (by omega))
    apply hsep i hi j hj
    rw [hp] at hh
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using hh

theorem padding_bytes_pre {update : Bool} {s t : RamState} {message : ByteArray}
    (hs : Storage (streamKind update) s)
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (ha : Absorbed (stackPtr s + 16) message s) (he : (paddingEffect (update := update) s).Holds s t) :
    PaddingBytesPre message (stackPtr s + 16) t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
    have hsp := padding_rsp he
    refine ⟨padding_tail hp ha he, padding_marker hs hp hn he, ?_, ?_, ?_, ?_⟩
    · rw [he.writes.2.2.1, hp]
      change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 17 =
        stackPtr s + BitVec.ofNat 64 16 + BitVec.ofNat 64 (message.size % 64 + 1)
      rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat]
      congr 2
      omega
    · rw [he.writes.2.2.2.2, hp, FinalizeReset.remainingBytes _ hn,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [he.writes.2.2.2.1]
      rfl
    · have hh := (hs.of_agrees he.agrees hsp).stackApartPush (offset := 16)
        (len := message.size % 64 + 1) (by change _ ≤ 280; omega)
      rw [hsp] at hh
      exact hh

theorem padding_preserves_bytes {update : Bool} {s t : RamState} {base : BitVec 64}
    {len : Nat} {bytes : Nat → UInt8} (he : (paddingEffect (update := update) s).Holds s t)
    (hb : Bytes s.external base len bytes)
    (ha : RangeApart base len (stackPtr s + (.reg 15 : Operand 64).read s + 16) 1) :
    Bytes t.external base len bytes := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    apply hb.of_agreesExcept he.agrees
    intro i hi c hc hcover
    simp only [paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨j, hj, hh⟩ := hcover
    exact ha i hi j hj hh

end Md5.Proofs.Buffered.Finalize.Streams.Slices
