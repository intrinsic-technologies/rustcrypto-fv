import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Lower
import Sha2.Proofs.Wrapper.Hash.LengthEncoding

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Compress

variable {v : Variant}

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem last [Bindings]
    {initial s : RamState} {inputs : Array Input} {message : ByteArray} {hash : Array UInt32}
    (ctx : Context initial inputs v)
    (input : LengthReady initial s message hash v) :
    ∃ t, HashAt initial t hash v ∧ t.RIP = (v.pc 0x2cf) ∧
      (⟨(stackPtr initial - 344).toNat, 64⟩ : MemoryRegion).HasBytes t.external (finalBlock message) ∧
      memLoad t.external (stackPtr initial - 184) 64 =
        memLoad t.external (stackPtr initial - 288) 64 := by
  have pre : LastPre (v.pc 0x2c2) s := by
    refine ⟨input.rip, ?_, ?_⟩
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_writable8 ctx input.toState (by decide) (by decide)
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_codeApart ctx (codeOffset := (v.textOffset + 0x2c2)) (by decide) (by decide) (by cases v <;> decide)
  obtain ⟨_, t, run, ready, _, effect⟩ := last_head (v.pc 0x2c2) (returnBoundary initial)
    (by
      intro i hi
      apply boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
      rw [Variant.pc_add]
      exact v.pc_inProgram (by omega)) s
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x2c2) lastBytes
      (by cases v <;> decide) (by cases v <;> decide +kernel)) pre
  have rsp : rspOf s = stackPtr initial - 344 := input.rsp
  have frame : AgreesExcept [.mem (stackPtr initial - 288) 8,.mem (stackPtr initial - 184) 8,.rip] s t := by
    simpa only [lastEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Nat.reduceDiv,
      Write.component, Operand.component, rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using effect.agrees
  have writes : Writes initial [.mem (stackPtr initial - 288) 8,.mem (stackPtr initial - 184) 8,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · have w := writes_mem input.rsp (offset := 56) (len := 8) (.inl (by decide)) a
      rw [stack_address input.rsp] at w
      exact w ha
    · have w := writes_mem input.rsp (offset := 160) (len := 8) (.inr ⟨by decide, by decide⟩) a
      rw [stack_address input.rsp] at w
      exact w ha
    · exact ha.elim
  have state := preserve ctx input.toHashAt run ready frame writes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp)
  have kept : ∀ i < 56,
      t.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨j, hj, he⟩ := ha
      apply OffsetsApart.ne (c₁ := -288) (len₁ := 8) (c₂ := -344) (len₂ := 56)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg] using he.symm
    · obtain ⟨j, hj, he⟩ := ha
      apply OffsetsApart.ne (c₁ := -184) (len₁ := 8) (c₂ := -344) (len₂ := 56)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg] using he.symm
    · exact ha.elim
  have sourceWord : memLoad t.external (stackPtr initial-288) 64 =
      Common.Instructions.bswap64 (BitVec.ofNat 64 (8*message.size)) := by
    have word := effect.writes.1
    change memLoad t.external (rspOf s+56) 64 = s.regValue .r15 at word
    simpa only [rsp, input.lengthWord, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word
  have destinationWord : memLoad t.external (stackPtr initial-184) 64 =
      Common.Instructions.bswap64 (BitVec.ofNat 64 (8*message.size)) := by
    have word := effect.writes.2
    change memLoad t.external (rspOf s+160) 64 = s.regValue .r15 at word
    simpa only [rsp, input.lengthWord, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word
  have prefixSize : (finalPrefix message).size = 56 := input.prefixBytes.1
  have blockSize : (finalBlock message).size = 64 := by
    simp only [finalBlock, ByteArray.size_append, prefixSize, Common.Encoding.natToOctets_size]
  refine ⟨t, state, (effect.rip.trans (v.pc_add 0x2c2 13)), ⟨blockSize, ?_⟩, destinationWord.trans sourceWord.symm⟩
  intro i
  have hi : i.val < 64 := by have := i.isLt; omega
  have hi' : i.val < (finalPrefix message ++ NIST.Encoding.natToOctets 8 (8*message.size)).size := by
    simpa only [finalBlock] using i.isLt
  change t.external[BitVec.ofNat 64 ((stackPtr initial-344).toNat+i.val)]? =
    some ((finalPrefix message ++ NIST.Encoding.natToOctets 8 (8*message.size))[i.val]'hi')
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases low : i.val < 56
  · rw [ByteArray.getElem_append_left (by omega)]
    have h := kept i.val low
    apply h.trans
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]
      using input.prefixBytes.2 ⟨i.val, by omega⟩
  · rw [ByteArray.getElem_append_right (by omega)]
    have stored := Bytes.of_memLoad (n := 64)
      (stack_readable ctx state.toState (offset := 288) (len := 8) (by decide) (by decide)).mem
    simp only [BitVec.ofNat_eq_ofNat] at sourceWord
    rw [sourceWord] at stored
    have byte := stored (i.val-56) (by omega)
    rw [bswap64_ofNat_storedByte _ (by omega)] at byte
    have address : stackPtr initial-344 + BitVec.ofNat 64 i.val =
        stackPtr initial-288 + BitVec.ofNat 64 (i.val-56) := by
      have add : i.val = 56 + (i.val-56) := by omega
      conv => lhs; rw [add, BitVec.ofNat_add]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      rw [← BitVec.add_assoc (-344#64) (56#64)]
      rfl
    rw [address]
    simpa only [prefixSize, BitVec.ofNat_eq_ofNat] using byte

end Sha2.Proofs.Wrapper.Hash.Finalize.Compress
