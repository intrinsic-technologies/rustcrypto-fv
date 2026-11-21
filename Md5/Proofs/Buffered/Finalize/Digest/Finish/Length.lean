import Md5.Proofs.Buffered.Finalize.Digest.Finish.Length.Execution
import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.Finalize.Digest.Finish.Length

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem value_eq {s : RamState} {message : ByteArray}
    (hp : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (hb : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)) :
    value s = BitVec.ofNat 64 (message.size * 8) := by
  have hp32 : (Operand.reg 12 : Operand 32).read s = BitVec.ofNat 32 (message.size % 64) := by
    change ((Operand.reg 12 : Operand 64).read s).setWidth 32 = _
    rw [hp, BitVec.setWidth_ofNat_of_le (by decide)]
  rw [value, hp32, hb, FinalizeReset.Length.shift_position _ (by omega)]
  exact FinalizeReset.bitLength message.size

theorem effect_avoids {s : RamState} (h : Storage .digest s) :
    (effect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (by decide : 80 + 8 ≤ Kind.digest.stackBytes) ha) (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (by decide : 168 + 8 ≤ Kind.digest.stackBytes) ha) (.inl ⟨x.2, hx⟩)

theorem run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage .digest s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = 0x1001df) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hBytes : CodeIn (codeRange 0x1001df bytes) s :=
    program_text_slice hCode 0x1df 24 (by decide +kernel)
  obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
    execution boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
  exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (effect_avoids hStorage) hCode, hEffect⟩


theorem effect_preserves {s t : RamState} {base : BitVec 64} {len : Nat}
    {bytes : Nat → UInt8} (h : (effect s).Holds s t)
    (hb : Bytes s.external base len bytes)
    (ha : RangeApart (stackPtr s + 80) 8 base len)
    (hc : RangeApart (stackPtr s + 168) 8 base len) : Bytes t.external base len bytes := by
  apply hb.of_agreesExcept h.agrees
  intro i hi c hm hcov
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · obtain ⟨j, hj, he⟩ := hcov
    exact ha j hj i hi he.symm
  · obtain ⟨j, hj, he⟩ := hcov
    exact hc j hj i hi he.symm

theorem effect_prefix {s t : RamState} {bytes : Nat → UInt8}
    (h : (effect s).Holds s t) (hb : Bytes s.external (stackPtr s + 24) 56 bytes) :
    Bytes t.external (stackPtr s + 24) 56 bytes :=
  effect_preserves h hb
    (RangeApart.offsets (stackPtr s) (by decide) (by decide) (Or.inr (by decide)))
    (RangeApart.offsets (stackPtr s) (by decide) (by decide) (Or.inr (by decide)))

theorem effect_buffer {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : (effect s).Holds s t)
    (hb : (⟨(stackPtr s + 8).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr s + 8).toNat, 16⟩ : MemoryRegion).HasBytes
      t.external ⟨buffer.toBytes.toArray⟩ := by
  have hb' := Block.bytes_of_hasBytes hb
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb'
  simpa only [ByteArray.size, Vector.size_toArray] using
    Finalize.hasBytes_of_bytes (effect_preserves h hb'
    (RangeApart.offsets (stackPtr s) (by decide)
      (by simp [ByteArray.size]) (Or.inr (by simp [ByteArray.size])))
    (RangeApart.offsets (stackPtr s) (by decide)
      (by simp [ByteArray.size]) (Or.inr (by simp [ByteArray.size]))))

theorem effect_lengths {s t : RamState} (hs : Storage .digest s) (h : (effect s).Holds s t) :
    Bytes t.external (stackPtr s + 80) 8 (storedByte (value s)) ∧
      Bytes t.external (stackPtr s + 168) 8 (storedByte (value s)) := by
  exact ⟨Stores.bytes_of_read_eq
      (Stores.readable_of_agrees (hs.stackWritable 80 8 (by decide)).readable h.agrees)
      h.writes.2.2.1,
    Stores.bytes_of_read_eq
      (Stores.readable_of_agrees (hs.stackWritable 168 8 (by decide)).readable h.agrees)
      h.writes.2.2.2⟩


theorem effect_rsp {s t : RamState} (h : (effect s).Holds s t) :
    stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4) (by
  simp [effect, Effect.components, Write.component, Operand.component])


theorem effect_agrees {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (Kind.digest.changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Kind.changes, Kind.workRegisters, Kind.localChanges, Component.isMem]
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨.mem (stackPtr s + 8) 168, by simp [Kind.changes, Kind.localChanges], ?_⟩
    · exact FinalizeReset.Export.covers_shift (offset := 72) (len := 8)
        (by simpa [BitVec.add_assoc] using ha) (by decide)
    · exact FinalizeReset.Export.covers_shift (offset := 160) (len := 8)
        (by simpa [BitVec.add_assoc] using ha) (by decide)

end Md5.Proofs.Buffered.Finalize.Digest.Finish.Length
