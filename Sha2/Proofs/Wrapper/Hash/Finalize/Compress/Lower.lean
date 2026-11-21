import Sha2.Proofs.Wrapper.Hash.Padding.CopyWords
import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Machine
import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Memory
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Compress

variable {v : Variant}

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem lower_memory {initial s : RamState} {offset : Nat}
    (rsp : stackPtr s = stackPtr initial - 344) (bound : offset ≤ 48) :
    ∀ a, (Component.mem (rspOf s + BitVec.ofNat 64 (104+offset)) 8).Covers a →
      (Component.mem (stackPtr initial - 240) 56).Covers a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨offset+i, by omega, ?_⟩
  change rspOf s = stackPtr initial - 344 at rsp
  simp only [rsp, BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc,
    BitVec.ofNat_eq_ofNat]
  rw [← BitVec.add_assoc (-344#64) (104#64)]
  rfl

theorem lower_frame {initial s t : RamState} {p : BitVec 64}
    (rsp : stackPtr s = stackPtr initial - 344)
    (effect : (Sha2.Proofs.Wrapper.Hash.Padding.CopyWords.effect p s).Holds s t) :
    AgreesExcept [.reg 0,.reg 1,.mem (stackPtr initial - 240) 56,.rip] s t := by
  apply Common.Encoding.Serialize.agrees_of_footprint effect.agrees
  · intro c hc hm
    simp only [Sha2.Proofs.Wrapper.Hash.Padding.CopyWords.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals simp_all [Component.isMem]
  · intro c hc a ha
    simp only [Sha2.Proofs.Wrapper.Hash.Padding.CopyWords.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    · exact ⟨.mem (stackPtr initial - 240) 56, by simp, lower_memory rsp (offset := 0) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 240) 56, by simp, lower_memory rsp (offset := 8) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 240) 56, by simp, lower_memory rsp (offset := 16) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 240) 56, by simp, lower_memory rsp (offset := 24) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 240) 56, by simp, lower_memory rsp (offset := 32) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 240) 56, by simp, lower_memory rsp (offset := 40) (by decide) a ha⟩
    · exact ⟨.mem (stackPtr initial - 240) 56, by simp, lower_memory rsp (offset := 48) (by decide) a ha⟩

theorem lower_words {initial s t : RamState} {p : BitVec 64}
    (rsp : stackPtr s = stackPtr initial - 344)
    (effect : (Sha2.Proofs.Wrapper.Hash.Padding.CopyWords.effect p s).Holds s t) :
    ∀ j < 7, memLoad t.external (stackPtr initial - 240 + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (stackPtr initial - 344 + BitVec.ofNat 64 (8*j)) 64 := by
  change rspOf s = stackPtr initial - 344 at rsp
  have stores := effect.writes
  simp only [Sha2.Proofs.Wrapper.Hash.Padding.CopyWords.effect, Write.AllHold, Operand.read] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have word := stores.2.2.1
    change memLoad t.external (rspOf s + 104) 64 =
      memLoad s.external (rspOf s + 0) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.1
    change memLoad t.external (rspOf s + 112) 64 =
      memLoad s.external (rspOf s + 8) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.1
    change memLoad t.external (rspOf s + 120) 64 =
      memLoad s.external (rspOf s + 16) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.2.1
    change memLoad t.external (rspOf s + 128) 64 =
      memLoad s.external (rspOf s + 24) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.2.2.1
    change memLoad t.external (rspOf s + 136) 64 =
      memLoad s.external (rspOf s + 32) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.2.2.2.1
    change memLoad t.external (rspOf s + 144) 64 =
      memLoad s.external (rspOf s + 40) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word
  · have word := stores.2.2.2.2.2.2.2.2
    change memLoad t.external (rspOf s + 152) 64 =
      memLoad s.external (rspOf s + 48) 64 at word
    rw [rsp] at word
    simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero] using word

theorem block_bytes_of_words {s t : RamState} {source destination : BitVec 64}
    (readable : MemReadable s source 64) (allocated : MemReadable t destination 64)
    (words : ∀ j < 8,
      memLoad t.external (destination + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (source + BitVec.ofNat 64 (8*j)) 64) :
    ∀ i < 64, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]? := by
  intro i hi
  have src := Bytes.of_memLoad (n := 64) (a := source + BitVec.ofNat 64 (8*(i/8)))
    (m := s.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem (8*(i/8)+j) (by omega))
  have dst := Bytes.of_memLoad (n := 64) (a := destination + BitVec.ofNat 64 (8*(i/8)))
    (m := t.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated.mem (8*(i/8)+j) (by omega))
  rw [words (i/8) (by omega)] at dst
  have eq := (dst (i%8) (by omega)).trans (src (i%8) (by omega)).symm
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8=i by omega] using eq

theorem copy_lower [Bindings] (last : Bool)
    {initial s : RamState} {inputs : Array Input} {chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context initial inputs v)
    (input : HashAt initial s hash v)
    (rip : s.RIP = if last then (v.pc 0x2cf) else (v.pc 0x213))
    (bytes : (⟨(stackPtr initial - 344).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk)
    (high : memLoad s.external (stackPtr initial - 184) 64 =
      memLoad s.external (stackPtr initial - 288) 64) :
    ∃ t, HashAt initial t hash v ∧
      t.RIP = (if last then (v.pc 0x320) else (v.pc 0x264)) ∧
      (⟨(stackPtr initial - 240).toNat, 64⟩ : MemoryRegion).HasBytes t.external chunk ∧
      AgreesExcept [.reg 0,.reg 1,.mem (stackPtr initial - 240) 56,.rip] s t := by
  let pc : Nat := if last then (v.textOffset + 0x2cf) else (v.textOffset + 0x213)
  have bound : pc + 81 ≤ 71757 := by cases v <;> cases last <;> decide
  have boundlt : pc + 81 < 71757 := by cases v <;> cases last <;> decide
  have next (i : Nat) (hi : i ≤ 81) :
      (Extracted.textAddress + BitVec.ofNat 64 pc) + BitVec.ofNat 64 i ≠
        (returnBoundary initial).rip := by
    apply boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (pc+i) (by omega)
  have pre : Sha2.Proofs.Wrapper.Hash.Padding.CopyWords.Pre (Extracted.textAddress + BitVec.ofNat 64 pc) s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases last <;> exact rip
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_readable ctx input.toState (by decide) (by decide)
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_writable8 ctx input.toState (by decide) (by decide)
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_codeApart ctx (by decide) (by decide) bound
  obtain ⟨_, t, run, ready, _, effect⟩ := Sha2.Proofs.Wrapper.Hash.Padding.CopyWords.run
    (Extracted.textAddress + BitVec.ofNat 64 pc) (returnBoundary initial) next s
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded) pc Sha2.Proofs.Wrapper.Hash.Padding.CopyWords.bytes bound
      (by cases v <;> cases last <;> decide +kernel)) pre
  have frame := lower_frame input.rsp effect
  have writes : Writes initial [.reg 0,.reg 1,.mem (stackPtr initial - 240) 56,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, he⟩ := ha
    exact .inr ⟨i, by omega, he⟩
  have state := preserve ctx input run ready frame writes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp)
  have top : memLoad t.external (stackPtr initial - 184) 64 =
      memLoad s.external (stackPtr initial - 288) 64 := by
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
    apply OffsetsApart.ne (c₁ := -240) (len₁ := 56) (c₂ := -184) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg] using he.symm
  have words : ∀ j < 8,
      memLoad t.external (stackPtr initial - 240 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (stackPtr initial - 344 + BitVec.ofNat 64 (8*j)) 64 := by
    intro j hj
    by_cases low : j < 7
    · exact lower_words input.rsp effect j low
    · have eq : j = 7 := by omega
      subst j
      simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
        BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using top
  have copied := block_bytes_of_words
    (stack_readable ctx input.toState (offset := 344) (len := 64) (by decide) (by decide))
    (stack_readable ctx state.toState (offset := 240) (len := 64) (by decide) (by decide)) words
  refine ⟨t, state, ?_, ⟨bytes.1, ?_⟩, frame⟩
  · have h := effect.rip
    cases v <;> cases last <;> exact h
  · intro i
    have h := copied i.val (by have hsize : chunk.size = 64 := bytes.1; omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat] using h.trans (by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat] using bytes.2 i)

end Sha2.Proofs.Wrapper.Hash.Finalize.Compress
