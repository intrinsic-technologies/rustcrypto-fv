import Md5.Proofs.Buffered.FinalizeReset.Clear
import Md5.Proofs.Buffered.FinalizeReset.Frame
import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.FinalizeReset.Clear

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem effect_frame {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) :
    AgreesExcept [.rip, .mem (stackPtr s + 8) 56] s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem]
  · intro address c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨.mem (stackPtr s + 8) 56, by simp, ?_⟩
    · exact Export.covers_shift (offset := 0) (by simpa using ha) (by cases variant <;> decide)
    · exact Export.covers_shift (offset := 8) (by simpa [BitVec.add_assoc] using ha) (by cases variant <;> decide)
    · exact Export.covers_shift (offset := 16) (by simpa [BitVec.add_assoc] using ha) (by cases variant <;> decide)
    · exact Export.covers_shift (offset := 24) (by simpa [BitVec.add_assoc] using ha) (by cases variant <;> decide)
    · exact Export.covers_shift (offset := 32) (by simpa [BitVec.add_assoc] using ha) (by cases variant <;> decide)
    · exact Export.covers_shift (offset := 40) (by simpa [BitVec.add_assoc] using ha) (by cases variant <;> decide)
    · exact Export.covers_shift (offset := 48) (by simpa [BitVec.add_assoc] using ha) (by cases variant <;> decide)

theorem effect_agrees {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) :
    AgreesExcept (changes s) s t := by
  apply (effect_frame h).widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp [changes]
    · cases hm
  · intro address c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.elim
    · refine ⟨.mem (stackPtr s + 8) 152, by simp [changes], ?_⟩
      obtain ⟨i, hi, he⟩ := ha
      exact ⟨i, by omega, he⟩

theorem effect_buffer {variant : Variant} {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : (effect s variant).Holds s t)
    (hb : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes
      t.external ⟨buffer.toBytes.toArray⟩ := by
  have hb' := Block.bytes_of_hasBytes hb
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb'
  have hx := hb'.of_agreesExcept (effect_frame h) (by
    intro i hi c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.elim
    · obtain ⟨j, hj, he⟩ := ha
      exact RangeApart.offsets (stackPtr s) (a := 8) (len := 56) (b := 232)
        (count := (⟨buffer.toBytes.toArray⟩ : ByteArray).size)
        (by cases variant <;> decide) (by simp [ByteArray.size]) (Or.inl (by cases variant <;> decide)) j hj i hi he.symm)
  simpa only [ByteArray.size, Vector.size_toArray] using Finalize.hasBytes_of_bytes hx

end Md5.Proofs.Buffered.FinalizeReset.Clear
