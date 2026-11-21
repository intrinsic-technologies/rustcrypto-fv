import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Machine
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Memory
import P256.Proofs.SHA256.LengthEncoding

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SHA256

theorem lower_memory {initial s : RamState} {offset : Nat}
    (rsp : stackPtr s = stackPtr initial - 1176) (bound : offset ≤ 48) :
    ∀ a, (Component.mem (rspOf s + BitVec.ofNat 64 offset) 8).Covers a →
      (Component.mem (stackPtr initial - 1176) 56).Covers a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨offset+i, by omega, ?_⟩
  change rspOf s = stackPtr initial - 1176 at rsp
  simp only [rsp, BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc,
    BitVec.reduceNeg, BitVec.ofNat_eq_ofNat]


theorem lower_frame {initial s t : RamState} {p : BitVec 64}
    (rsp : stackPtr s = stackPtr initial - 1176)
    (effect : (CopyWords.effect p s).Holds s t) :
    AgreesExcept [.reg 0,.reg 1,.mem (stackPtr initial - 1176) 56,.rip] s t := by
  apply agrees_of_footprint effect.agrees
  · intro c hc hm
    simp only [CopyWords.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals simp_all [Component.isMem]
  · intro c hc a ha
    simp only [CopyWords.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    · exact ⟨.mem (stackPtr initial - 1176) 56, by simp, lower_memory rsp (offset := 0) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 1176) 56, by simp, lower_memory rsp (offset := 8) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 1176) 56, by simp, lower_memory rsp (offset := 16) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 1176) 56, by simp, lower_memory rsp (offset := 24) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 1176) 56, by simp, lower_memory rsp (offset := 32) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 1176) 56, by simp, lower_memory rsp (offset := 40) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 1176) 56, by simp, lower_memory rsp (offset := 48) (by decide) a ha⟩

theorem lower_words {initial s t : RamState} {p : BitVec 64}
    (rsp : stackPtr s = stackPtr initial - 1176)
    (effect : (CopyWords.effect p s).Holds s t) :
    ∀ j < 7, memLoad t.external (stackPtr initial - 1176 + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (stackPtr initial - 1048 + BitVec.ofNat 64 (8*j)) 64 := by
  change rspOf s = stackPtr initial - 1176 at rsp
  have stores := effect.writes
  simp only [CopyWords.effect, Write.AllHold, Operand.read] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have word := stores.2.2.1
    change memLoad t.external (rspOf s + 0) 64 =
      memLoad s.external (rspOf s + 128) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.1
    change memLoad t.external (rspOf s + 8) 64 =
      memLoad s.external (rspOf s + 136) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.1
    change memLoad t.external (rspOf s + 16) 64 =
      memLoad s.external (rspOf s + 144) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.2.1
    change memLoad t.external (rspOf s + 24) 64 =
      memLoad s.external (rspOf s + 152) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.2.2.1
    change memLoad t.external (rspOf s + 32) 64 =
      memLoad s.external (rspOf s + 160) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.2.2.2.1
    change memLoad t.external (rspOf s + 40) 64 =
      memLoad s.external (rspOf s + 168) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.2.2.2.2
    change memLoad t.external (rspOf s + 48) 64 =
      memLoad s.external (rspOf s + 176) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word

theorem copy_lower [Bindings] (last : Bool)
    {initial s : RamState} {message chunk : ByteArray} {boundary : ReturnBoundary} {hash : Array UInt32}
    (pre : Message.Pre initial boundary message)
    (input : HashAt initial s boundary hash)
    (rip : s.RIP = if last then 0x10d864 else 0x10d78b)
    (bytes : (⟨(stackPtr initial - 1048).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk)
    (high : memLoad s.external (stackPtr initial - 1120) 64 =
      memLoad s.external (stackPtr initial - 992) 64) :
    ∃ t, HashAt initial t boundary hash ∧
      t.RIP = (if last then 0x10d8be else 0x10d7e5) ∧
      (⟨(stackPtr initial - 1176).toNat, 64⟩ : MemoryRegion).HasBytes t.external chunk ∧
      AgreesExcept [.reg 0,.reg 1,.mem (stackPtr initial - 1176) 56,.rip] s t := by
  let pc : Nat := if last then 0xd864 else 0xd78b
  have bound : pc + 90 ≤ 118431 := by cases last <;> decide
  have boundlt : pc + 90 < 118431 := by cases last <;> decide
  have next (i : Nat) (hi : i ≤ 90) :
      (Extracted.textAddress + BitVec.ofNat 64 pc) + BitVec.ofNat 64 i ≠
        boundary.rip := by
    apply boundary_ne_program pre.outerBoundary
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (pc+i) (by omega)
  have hp : CopyWords.Pre (Extracted.textAddress + BitVec.ofNat 64 pc) s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases last <;> exact rip
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_readable pre input.toFrameState (by decide) (by decide)
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_writable8 pre input.toFrameState (by decide) (by decide)
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_codeApart pre (by decide) (by decide) bound
  obtain ⟨_, t, run, ready, _, effect⟩ := CopyWords.run
    (Extracted.textAddress + BitVec.ofNat 64 pc) boundary next s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) pc CopyWords.bytes bound
      (by cases last <;> decide +kernel)) hp
  have frame := lower_frame input.rsp effect
  have writes : Writes initial [.reg 0,.reg 1,.mem (stackPtr initial - 1176) 56,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, he⟩ := ha
    exact .inr ⟨i, by omega, he⟩
  have state := preserve pre input run ready frame writes (by simp) (by simp)
  have top : memLoad t.external (stackPtr initial - 1120) 64 =
      memLoad s.external (stackPtr initial - 992) 64 := by
    rw [← high]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨j, hj, he⟩ := ha
    apply OffsetsApart.ne (c₁ := -1176) (len₁ := 56) (c₂ := -1120) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg] using he.symm
  have words : ∀ j < 8,
      memLoad t.external (stackPtr initial - 1176 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (stackPtr initial - 1048 + BitVec.ofNat 64 (8*j)) 64 := by
    intro j hj
    by_cases low : j < 7
    · exact lower_words input.rsp effect j low
    · have eq : j = 7 := by omega
      subst j
      simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
        BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using top
  have copied := HMAC.Key.Output.bytes_of_words (count := 8)
    (stack_readable pre input.toFrameState (offset := 1048) (len := 64) (by decide) (by decide))
    (stack_readable pre state.toFrameState (offset := 1176) (len := 64) (by decide) (by decide)) words
  refine ⟨t, state, ?_, ⟨bytes.1, ?_⟩, frame⟩
  · have h := effect.rip
    cases last <;> exact h
  · intro i
    have h := copied i.val (by have hsize : chunk.size = 64 := bytes.1; omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat] using h.trans (by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat] using bytes.2 i)

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks
