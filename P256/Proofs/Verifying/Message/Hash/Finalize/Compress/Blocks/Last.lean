import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Lower
import P256.Proofs.SHA256.LengthEncoding

set_option autoImplicit false


namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SHA256

theorem last_head_result [Bindings]
    {initial s : RamState} {message : ByteArray} {boundary : ReturnBoundary} {hash : Array UInt32}
    (pre : Message.Pre initial boundary message)
    (input : LengthReady initial s boundary message hash) :
    ∃ t, HashAt initial t boundary hash ∧ t.RIP = 0x10d864 ∧
      (⟨(stackPtr initial - 1048).toNat, 64⟩ : MemoryRegion).HasBytes t.external (finalBlock message) ∧
      memLoad t.external (stackPtr initial - 1120) 64 =
        memLoad t.external (stackPtr initial - 992) 64 := by
  have hp : Machine.LastPre s := by
    refine ⟨input.rip, ?_, ?_⟩
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_writable8 pre input.toFrameState (by decide) (by decide)
    · intro i hi
      rw [stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      all_goals simp only [BitVec.reduceSub, BitVec.ofNat_eq_ofNat]
      all_goals exact stack_codeApart pre (codeOffset := 0xd857) (by decide) (by decide) (by decide)
  obtain ⟨_, t, run, ready, _, effect⟩ := Machine.last_head boundary
    pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0xd857 Machine.lastBytes
      (by decide) (by decide +kernel)) hp
  have rsp : rspOf s = stackPtr initial - 1176 := input.rsp
  have frame : AgreesExcept [.mem (stackPtr initial - 992) 8,.mem (stackPtr initial - 1120) 8,.rip] s t := by
    simpa only [Machine.lastEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Nat.reduceDiv,
      Write.component, Operand.component, rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using effect.agrees
  have writes : Writes initial [.mem (stackPtr initial - 992) 8,.mem (stackPtr initial - 1120) 8,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · have w := writes_mem input.rsp (offset := 184) (len := 8) (.inl ⟨by decide, by decide⟩) a
      rw [stack_address input.rsp] at w
      exact w ha
    · have w := writes_mem input.rsp (offset := 56) (len := 8) (.inr (by decide)) a
      rw [stack_address input.rsp] at w
      exact w ha
    · exact ha.elim
  have state := preserve pre input.toHashAt run ready frame writes (by simp) (by simp)
  have kept : ∀ i < 56,
      t.external[stackPtr initial - 1048 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 1048 + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨j, hj, he⟩ := ha
      apply OffsetsApart.ne (c₁ := -992) (len₁ := 8) (c₂ := -1048) (len₂ := 56)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg] using he.symm
    · obtain ⟨j, hj, he⟩ := ha
      apply OffsetsApart.ne (c₁ := -1120) (len₁ := 8) (c₂ := -1048) (len₂ := 56)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg] using he.symm
    · exact ha.elim
  have sourceWord : memLoad t.external (stackPtr initial-992) 64 =
      Common.Instructions.bswap64 (BitVec.ofNat 64 (8*message.size)) := by
    have word := effect.writes.1
    change memLoad t.external (rspOf s+184) 64 = s.regValue .r15 at word
    simpa only [rsp, input.lengthWord, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word
  have destinationWord : memLoad t.external (stackPtr initial-1120) 64 =
      Common.Instructions.bswap64 (BitVec.ofNat 64 (8*message.size)) := by
    have word := effect.writes.2
    change memLoad t.external (rspOf s+56) 64 = s.regValue .r15 at word
    simpa only [rsp, input.lengthWord, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word
  have prefixSize : (finalPrefix message).size = 56 := input.prefixBytes.1
  have blockSize : (finalBlock message).size = 64 := finalBlock_size message
  refine ⟨t, state, effect.rip, ⟨blockSize, ?_⟩, destinationWord.trans sourceWord.symm⟩
  intro i
  have hi : i.val < 64 := by have := i.isLt; omega
  have hi' : i.val < (finalPrefix message ++ Standards.SECG.ECC.Encoding.natToOctets 8 (8*message.size)).size := by
    simpa only [finalBlock] using i.isLt
  change t.external[BitVec.ofNat 64 ((stackPtr initial-1048).toNat+i.val)]? =
    some ((finalPrefix message ++ Standards.SECG.ECC.Encoding.natToOctets 8 (8*message.size))[i.val]'hi')
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases low : i.val < 56
  · rw [ByteArray.getElem_append_left (by omega)]
    have h := kept i.val low
    apply h.trans
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]
      using input.prefixBytes.2 ⟨i.val, by omega⟩
  · rw [ByteArray.getElem_append_right (by omega)]
    have stored := Bytes.of_memLoad (n := 64)
      (stack_readable pre state.toFrameState (offset := 992) (len := 8) (by decide) (by decide)).mem
    simp only [BitVec.ofNat_eq_ofNat] at sourceWord
    rw [sourceWord] at stored
    have byte := stored (i.val-56) (by omega)
    rw [bswap64_ofNat_storedByte _ (by omega)] at byte
    have address : stackPtr initial-1048 + BitVec.ofNat 64 i.val =
        stackPtr initial-992 + BitVec.ofNat 64 (i.val-56) := by
      have add : i.val = 56 + (i.val-56) := by omega
      conv => lhs; rw [add, BitVec.ofNat_add]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      rw [← BitVec.add_assoc (-1048#64) (56#64)]
      rfl
    rw [address]
    simpa only [prefixSize, BitVec.ofNat_eq_ofNat] using byte

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks
