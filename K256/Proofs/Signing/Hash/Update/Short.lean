import K256.Proofs.Verify.Hash.Update.Dispatch
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Signing.Hash.Update.Copy
import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.SignatureRun

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

namespace Update

namespace Short

private theorem call {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
    {n : Nat} (args : Slice sp src n a)
    (push : StoreOk Extracted.programImage m (sp - 8) 8 0x1054ce 3) :
    ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1054c0, a, m⟩ =
        .call ⟨.l12a820, b, memStore m (sp - 8) (0x1054d1 : BitVec 64)⟩
          (Verify.Hash.Update.returnFrame .l1054d1 0x1054d1) ∧
      b[2] = ⟨64, BitVec.ofNat 64 n⟩ ∧ b[4] = ⟨64, sp - 8⟩ ∧
      b[6] = ⟨64, src⟩ ∧ b[7] = ⟨64, sp + 488⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,22,39,50,51] → b[i] = a[i]) := by
  have rsp : a[4].get 64 = sp := by rw [args.rsp]; rfl
  have buffered : a[12].get 64 = 0 := by rw [args.buffered]; rfl
  have size : a[5].get 64 = BitVec.ofNat 64 n := by rw [args.size]; rfl
  have memcpy : a[15].get 64 = 0x12a820 := by rw [args.memcpy]; rfl
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, buffered, size, memcpy, push]
    rfl
  case post =>
    refine ⟨rfl, rfl, args.source, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
private theorem finish {a : Values Value Reg.count} {m : Ram} {sp : BitVec 64} {n : Nat}
    (rsp : a[4] = ⟨64, sp⟩) (size : a[5] = ⟨64, BitVec.ofNat 64 n⟩)
    (buffered : a[12] = ⟨64, 0⟩) (slice : a[14] = ⟨64, sp + 1136⟩)
    (limit : a[3] = ⟨64, sp + 1152⟩)
    (store : StoreOk Extracted.programImage m (sp + 551) 1 0x1054d4 8) :
    ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1054d1, a, m⟩ =
        .jump ⟨.l1055bf, b, memStore m (sp + 551) (BitVec.ofNat 8 n)⟩ ∧
      b[5].width = 64 ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,12,13,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    have next : sp + 1136 + 16 = sp + 1152 := by
      rw [BitVec.add_assoc]
      rfl
    have equal : (cmpSpec (sp + 1152) (sp + 1152)).ZF = true := by
      simp only [cmpSpec, subSpec, BitVec.sub_self]
      rfl
    have sp' : a[4].get 64 = sp := by rw [rsp]; rfl
    have n' : a[5].get 64 = BitVec.ofNat 64 n := by rw [size]; rfl
    have k' : a[12].get 64 = 0 := by rw [buffered]; rfl
    have sl' : a[14].get 64 = sp + 1136 := by rw [slice]; rfl
    have lim' : a[3].get 64 = sp + 1152 := by rw [limit]; rfl
    cfg_eval [sp', n', k', sl', lim', next, equal, store]
    simp only [setWidth_mergeGPR8,
      BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)]
    rfl
  case post =>
    refine ⟨rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Short

set_option maxRecDepth 4096 in
theorem short {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
    {message : ByteArray}
    (args : Slice sp src message.size a) (branch : message.size < 64)
    (_image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (bytes : (⟨src.toNat, message.size⟩ : MemoryRegion).HasBytes m message)
    (input : Readable m src message.size)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (inputLow : src.toNat + message.size < 2^32)
    (apart : 0 < message.size → src.toNat + message.size ≤ sp.toNat - 512 ∨ sp.toNat + 1160 ≤ src.toNat)
    (iv : Compression.StateAt m (sp + 552) initialHash)
    (_buffered : memLoad m (sp + 551) 8 = 0)
    (blocks : memLoad m (sp + 584) 64 = 0) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l1054c0, a, m⟩, []⟩ ⟨⟨.l1055bf, b, t⟩, []⟩ ∧
      Frame sp a b m t ∧ Buffer sp message b t := by
  let n := message.size
  let pushed := memStore m (sp - 8) (0x1054d1 : BitVec 64)
  have noBlocks : message.size / 64 = 0 := Nat.div_eq_of_lt branch
  have tailSize : message.size % 64 = n := Nat.mod_eq_of_lt branch
  have pushWrite : Writable Extracted.programImage m (sp - 8) 8 :=
    stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have push : StoreOk Extracted.programImage m (sp - 8) 8 0x1054ce 3 :=
    ParseSignature.storeOk_of_codeRange (off := 14) pushWrite
      (fun x hx => Common.fnCode_subset_programImage x (code_l1054c0 x hx)) (by decide)
  have pushFrame : RamWriteFrame m pushed (regions sp) := by
    apply (RamWriteFrame.refl m _).memStore
    refine ⟨_, List.mem_cons_self, ?_⟩
    change sp.toNat - 512 ≤ (sp - 8).toNat ∧
      (sp - 8).toNat + 8 ≤ sp.toNat - 512 + 624 ∧ (sp - 8).toNat + 8 ≤ 2^64
    have pos : (sp - 8).toNat = sp.toNat - 8 :=
      BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from (by change 8 ≤ sp.toNat; omega))
    rw [pos]
    omega
  have ret : memLoad pushed (sp - 8) 64 = 0x1054d1 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨c, call, c2, c4, c6, c7, saved⟩ := Short.call args push
  have direction : c[22] = ⟨1, 0⟩ := (saved 22 (by decide)).trans args.direction
  have len : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt (Nat.lt_trans branch (by decide))
  obtain ⟨out, run, copy, tag, rsp, kept, writes, tailBytes⟩ := copyTail
    (tail := src) (n := BitVec.ofNat 64 n)
    (congrArg (Value.get 64) c7) (congrArg (Value.get 64) c6)
    (congrArg (Value.get 64) c2) (congrArg (Value.get 64) c4) (congrArg (Value.get 1) direction)
    (by rw [noBlocks]; exact (BitVec.add_zero src).symm) (len.trans tailSize.symm)
    pushFrame bytes input stack depth limit inputLow apart (by rw [ret]; decide)
  have preserved (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,22,39,50,51]) :
      out.values[i] = a[i] :=
    (kept i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)).trans (saved i hi)
  have finishWrite : Writable Extracted.programImage out.store (sp + 551) 1 :=
    (stack.of_frame writes).of_offsets rfl (addr_sub _ _) (by decide)
  have finishStore : StoreOk Extracted.programImage out.store (sp + 551) 1 0x1054d4 8 :=
    ParseSignature.storeOk_of_codeRange (off := 3) finishWrite
      (fun x hx => Common.fnCode_subset_programImage x (code_l1054d1 x hx)) (by decide)
  obtain ⟨b, finish, w5, finishKept⟩ := Short.finish rsp
    ((preserved 5 (by decide)).trans args.size)
    ((preserved 12 (by decide)).trans args.buffered)
    ((preserved 14 (by decide)).trans args.slice)
    ((preserved 3 (by decide)).trans args.limit) finishStore
  have keep (i : Fin Reg.count) (hi : i.val ∈ [12,13,22,39,50,51]) : b[i] = a[i] :=
    (finishKept i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)).trans (preserved i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega))
  let final := memStore out.store (sp + 551) (BitVec.ofNat 8 n)
  have lenAddr : (sp + 551).toNat = sp.toNat + 551 := toNat_add_ofNat sp 551 (by omega)
  have lenSlot : InRegions (regions sp) (sp + 551) 1 := by
    refine ⟨⟨sp.toNat + 488, 104⟩, List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)), ?_⟩
    change sp.toNat + 488 ≤ (sp + 551).toNat ∧ (sp + 551).toNat + 1 ≤ sp.toNat + 488 + 104 ∧
      (sp + 551).toNat + 1 ≤ 2^64
    rw [lenAddr]
    omega
  refine ⟨b, final, ?_, ?_, ?_⟩
  · have resume := ParseSignature.exec_reaches_resume run
      (Verify.Hash.Update.returnFrame .l1054d1 0x1054d1) [] (by rw [tag, ret]; rfl)
    exact .step (congrArg (Transfer.next _ []) call)
      (resume.trans (.single (congrArg (Transfer.next _ []) finish)))
  · refine ⟨(finishKept 4 (by decide)).trans rsp, (keep 22 (by decide)).trans args.direction,
      fun i hi => keep i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        omega), writes.memStore _ lenSlot⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact w5
      · exact congrArg Value.width ((keep 12 (by decide)).trans args.buffered)
      · exact congrArg Value.width ((keep 13 (by decide)).trans args.rest)
    · change Compression.StateAt _ _ (compressBlocksFrom initialHash message 0 (message.size / 64))
      rw [noBlocks]
      apply Verify.Hash.Update.stateStore
      · rw [copy, len]
        unfold memCopy
        apply Verify.Hash.Update.stateStore
        · exact Verify.Hash.Update.stateStore iv _ (RangeApart.of_offsets (addr_sub _ _) rfl (by decide))
        · rw [show (8 * n) / 8 = n by omega]
          apply RangeApart.of_offsets rfl rfl
          exact ⟨Nat.le_of_lt branch, by decide⟩
      · exact RangeApart.of_offsets rfl rfl (by decide)
    · apply Verify.Hash.Update.bytesStore tailBytes
      apply RangeApart.of_offsets rfl rfl
      exact ⟨by decide, by rw [tailSize]; exact Nat.le_of_lt_succ branch⟩
    · change memLoad (memStore out.store (sp + 551) (BitVec.ofNat 8 n)) (sp + 551) 8 = _
      rw [memLoad_memStore_same _ _ _ (by decide) (by decide), tailSize]
    · change memLoad (memStore out.store (sp + 551) (BitVec.ofNat 8 n)) (sp + 584) 64 = _
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide)),
        copy, len, memCopy, memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          rw [show (8 * n) / 8 = n by omega]
          apply RangeApart.of_offsets rfl rfl
          exact ⟨Nat.le_trans (Nat.le_of_lt branch) (by decide : 64 ≤ 96), by decide⟩)]
      change memLoad (memStore m (sp - 8) (0x1054d1 : BitVec 64)) (sp + 584) 64 = _
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets (addr_sub _ _) rfl (by decide)),
        blocks, noBlocks]
      rfl

end Update
end K256.Proofs.Signing.Hash
