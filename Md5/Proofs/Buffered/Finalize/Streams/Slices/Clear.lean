import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Clear.Properties
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Transition
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace Clear

theorem buffer_bytes {update : Bool} {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (he : (Blocks.Clear.effect (update := update) s).Holds s t)
    (hb : (⟨(stackPtr s).toNat, 16⟩ : MemoryRegion).HasBytes s.external
      ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr t).toNat, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨buffer.toBytes.toArray⟩ := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    rw [Blocks.Clear.effect_rsp he]
    refine ⟨hb.1, ?_⟩
    intro i
    have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    have hApart : RangeApart (stackPtr s) 16 (stackPtr s + 16) 56 := by
      simpa using RangeApart.offsets (stackPtr s) (a := 0) (len := 16)
        (b := 16) (count := 56) (by decide) (by decide) (Or.inl (by decide))
    have heq : t.external[stackPtr s + BitVec.ofNat 64 i.val]? =
        s.external[stackPtr s + BitVec.ofNat 64 i.val]? := by
      apply (Blocks.Clear.effect_agrees he).byte
      intro c hc hcover
      simp only [Blocks.Clear.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hcover.elim
      · obtain ⟨j, hj, heq⟩ := hcover
        exact hApart i.val hi j hj heq
    have hb' := hb.2 i
    change s.external[BitVec.ofNat 64 ((stackPtr s).toNat + i.val)]? = _ at hb'
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb'
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using heq.trans hb'

theorem agrees {update : Bool} {s t : RamState} (he : (Blocks.Clear.effect (update := update) s).Holds s t) :
    AgreesExcept ((streamKind update).changes s) s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    apply (Blocks.Clear.effect_agrees he).widen
    · intro c hc hm
      simp only [Blocks.Clear.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      all_goals simp_all [streamKind, Component.isMem, Kind.changes]
    · intro address c hc hcover
      simp only [Blocks.Clear.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hcover.elim
      · exact ⟨.mem (stackPtr s) 168, by simp [streamKind, Kind.changes, Kind.localChanges],
          FinalizeReset.Export.covers_shift hcover (by decide)⟩

end Clear

end Md5.Proofs.Buffered.Finalize.Streams.Slices
