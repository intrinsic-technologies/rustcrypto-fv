import Md5.Proofs.Buffered.FinalizeReset.Length
import Md5.Proofs.Buffered.FinalizeReset.Frame
import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.FinalizeReset.Length

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem effect_agrees {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) :
    AgreesExcept (changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [changes, Component.isMem]
  · intro address c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨.mem (stackPtr s + 8) 152, by simp [changes], ?_⟩
    · exact Export.covers_shift (offset := 56) (by simpa [BitVec.add_assoc] using ha) (by cases variant <;> decide)
    · exact Export.covers_shift (offset := 144) (by simpa [BitVec.add_assoc] using ha) (by cases variant <;> decide)

theorem effect_preserves {variant : Variant} {s t : RamState} {base : BitVec 64} {len : Nat}
    {bytes : Nat → UInt8} (h : (effect s variant).Holds s t)
    (hb : Bytes s.external base len bytes)
    (ha : RangeApart (stackPtr s + 64) 8 base len)
    (hc : RangeApart (stackPtr s + 152) 8 base len) : Bytes t.external base len bytes := by
  apply hb.of_agreesExcept h.agrees
  intro i hi c hm hcov
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · obtain ⟨j, hj, he⟩ := hcov
    exact ha j hj i hi he.symm
  · obtain ⟨j, hj, he⟩ := hcov
    exact hc j hj i hi he.symm

theorem effect_prefix {variant : Variant} {s t : RamState} {bytes : Nat → UInt8}
    (h : (effect s variant).Holds s t) (hb : Bytes s.external (stackPtr s + 8) 56 bytes) :
    Bytes t.external (stackPtr s + 8) 56 bytes :=
  effect_preserves h hb
    (RangeApart.offsets (stackPtr s) (by cases variant <;> decide) (by cases variant <;> decide) (Or.inr (by cases variant <;> decide)))
    (RangeApart.offsets (stackPtr s) (by cases variant <;> decide) (by cases variant <;> decide) (Or.inr (by cases variant <;> decide)))

theorem effect_buffer {variant : Variant} {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : (effect s variant).Holds s t)
    (hb : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes
      t.external ⟨buffer.toBytes.toArray⟩ := by
  have hb' := Block.bytes_of_hasBytes hb
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb'
  simpa only [ByteArray.size, Vector.size_toArray] using
    Finalize.hasBytes_of_bytes (effect_preserves h hb'
    (RangeApart.offsets (stackPtr s) (by cases variant <;> decide)
      (by simp [ByteArray.size]) (Or.inl (by cases variant <;> decide)))
    (RangeApart.offsets (stackPtr s) (by cases variant <;> decide)
      (by simp [ByteArray.size]) (Or.inl (by cases variant <;> decide))))

theorem effect_lengths {variant : Variant} {s t : RamState} (hs : Storage s variant) (h : (effect s variant).Holds s t) :
    Bytes t.external (stackPtr s + 64) 8 (storedByte (value s)) ∧
      Bytes t.external (stackPtr s + 152) 8 (storedByte (value s)) := by
  exact ⟨Stores.bytes_of_read_eq
      (Stores.readable_of_agrees (Export.stackWritable hs 64 8 (by cases variant <;> decide)).readable h.agrees)
      h.writes.2.1,
    Stores.bytes_of_read_eq
      (Stores.readable_of_agrees (Export.stackWritable hs 152 8 (by cases variant <;> decide)).readable h.agrees)
      h.writes.2.2⟩

theorem effect_lastBlock {variant : Variant} {s t : RamState} {message : ByteArray}
    (hs : Storage s variant) (h : (effect s variant).Holds s t)
    (hp : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (hb : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64) <<< 9)
    (hprefix : Bytes s.external (stackPtr s + 8) 56
      (fun i ↦ if message.size % 64 < 56 then (Finalize.firstBlock message)[i]! else 0)) :
    (⟨(stackPtr s + 8).toNat, 64⟩ : MemoryRegion).HasBytes t.external (Finalize.lastBlock message) ∧
      Bytes t.external (stackPtr s + 152) 8
        (storedByte (BitVec.ofNat 64 (message.size * 8))) := by
  have hl := effect_lengths hs h
  rw [value_eq hp hb] at hl
  constructor
  · have hp' := effect_prefix h hprefix
    have hh := Finalize.lastBlock_bytes message hp' (by simpa [BitVec.add_assoc] using hl.1)
    have hout := Finalize.hasBytes_of_bytes (by
      rw [Finalize.size_lastBlock]
      exact hh)
    simpa only [Finalize.size_lastBlock] using hout
  · exact hl.2

end Md5.Proofs.Buffered.FinalizeReset.Length
