import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Prepare
import Md5.Proofs.Buffered.Finalize.Copy
import Md5.Proofs.Buffered.FinalizeReset.Export.Bytes

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_preserves_context {update : Bool} {s t : RamState} {message : ByteArray}
    (h : (prepareEffect (update := update) s).Holds s t)
    (ha : Absorbed (stackPtr s + 16) message s) : Absorbed (stackPtr t + 16) message t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hsp : stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4)
      (by simp [prepareEffect, Effect.components])
    rw [hsp]
    apply absorbed_of_copy ha
    intro i hi
    apply h.agrees.byte
    intro c hc hcover
    simp only [prepareEffect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    · obtain ⟨j, hj, he⟩ := hcover
      exact RangeApart.offsets (stackPtr s) (a := 16) (len := 88) (b := 8) (count := 8)
        (by decide) (by decide) (by decide) i hi j hj he
    · obtain ⟨j, hj, he⟩ := hcover
      exact RangeApart.offsets (stackPtr s) (a := 16) (len := 88) (b := 0) (count := 8)
        (by decide) (by decide) (by decide) i hi j hj (by simpa using he)

theorem prepare_result {update : Bool} {s t : RamState} {message : ByteArray}
    (hs : Storage (streamKind update) s) (h : (prepareEffect (update := update) s).Holds s t)
    (ha : Absorbed (stackPtr s + 192) message s) :
    (⟨(stackPtr s).toNat, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hb : (⟨(stackPtr s + 256).toNat, 16⟩ : MemoryRegion).HasBytes s.external
        ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
      have he : (stackPtr s + 192).toNat + 64 = (stackPtr s + 256).toNat := by
        change (stackPtr s + BitVec.ofNat 64 192).toNat + 64 =
          (stackPtr s + BitVec.ofNat 64 256).toNat
        rw [hs.stackAddress (offset := 192) (by decide),
          hs.stackAddress (offset := 256) (by decide)]
      simpa only [he] using ha.buffer
    have hw := h.writes
    simp only [prepareEffect, Write.AllHold] at hw
    refine FinalizeReset.Export.hasBytes_of_halves (base := stackPtr s)
      (bytes := (absorbedBuffer message).toBytes) ?_ hw.2.2.2.2.2 hw.2.2.2.2.1 ?_ ?_
    · intro i hi
      apply h.agrees.grow
      have hm := (hs.stackWritable 0 16 (by decide)).bytes i hi
      simpa using hm
    · intro i
      simpa using FinalizeReset.Export.digest_half hb 0 (by decide) i
    · intro i
      simpa [BitVec.add_assoc] using FinalizeReset.Export.digest_half hb 8 (by decide) i

theorem prepare_length {update : Bool} {s t : RamState} {message : ByteArray}
    (h : (prepareEffect (update := update) s).Holds s t)
    (ha : Absorbed (stackPtr s + 16) message s) :
    (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64) ∧
    (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64) := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hw := h.writes
    simp only [prepareEffect, Write.AllHold] at hw
    constructor
    · exact hw.1.trans (by simpa [BitVec.add_assoc] using ha.blocks)
    · rw [hw.2.1]
      have hp : (Operand.mem (stackPtr s + 79) : Operand 8).read s =
          BitVec.ofNat 8 (message.size % 64) := by
        simpa [BitVec.add_assoc] using ha.position
      rw [hp]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega

end Md5.Proofs.Buffered.Finalize.Streams.Slices
