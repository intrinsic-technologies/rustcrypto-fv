import K256.Proofs.Signing.Hash.Update.Copy
import K256.Proofs.Verify.Hash.Update.Dispatch
import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

namespace Update

private theorem prepareCompression {b : Values Value Reg.count} {m : Ram}
    {sp src n : BitVec 64}
    (rsp : b[4].get 64 = sp) (rsi : b[6].get 64 = src) (rdx : b[2].get 64 = n)
    (record : StoreOk Extracted.programImage m (sp + 584) 8 0x10555a 8)
    (push : StoreOk Extracted.programImage
      (memStore m (sp + 584) (memLoad m (sp + 584) 64 + n)) (sp - 8) 8 0x10556d 5) :
    ∃ child : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l10555a, b, m⟩ =
        .call ⟨.l1218e0, child, memStore
          (memStore m (sp + 584) (memLoad m (sp + 584) 64 + n))
          (sp - 8) (0x105572 : BitVec 64)⟩ (Verify.Hash.Update.returnFrame .l105572 0x105572) ∧
      child[4].get 64 = sp - 8 ∧ child[7].get 64 = sp + 552 ∧
      child[6].get 64 = src ∧ child[2].get 64 = n ∧ child[5] = ⟨64, src⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,12,13,14,15,22,39,50,51] → child[i] = b[i] := by
  refine ⟨?child, ?step, ?rsp, ?dst, ?src, ?count, ?saveSrc, ?saved⟩
  case step =>
    cfg_eval [rsp, rsi, rdx, record, push]
    rw [ite_eq_left push]
  case rsp => rfl
  case dst => rfl
  case src => exact rsi
  case count => exact rdx
  case saveSrc => rfl
  case saved =>
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem resumeCompression {a : Values Value Reg.count} {m : Ram} {src : BitVec 64}
    (rbp : a[5].get 64 = src) :
    ∃ c : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l105572, a, m⟩ = .jump ⟨.l105575, c, m⟩ ∧
      c[6] = ⟨64, src⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → c[i] = a[i] := by
  refine ⟨?c, ?step, ?source, ?saved⟩
  case step =>
    cfg_eval [rbp]
    rfl
  case source => rfl
  case saved =>
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem compressSlice {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
    {message : ByteArray}
    {b : Values Value Reg.count} (args : Slice sp src message.size a)
    (saved : ∀ i : Fin Reg.count, i.val ∈ [3,4,12,14,15,22,39,50,51] → b[i] = a[i])
    (count : b[2] = ⟨64, BitVec.ofNat 64 (message.size / 64)⟩)
    (source : b[6] = ⟨64, src⟩) (length : b[13] = ⟨64, BitVec.ofNat 64 message.size⟩)
    (_image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (bytes : (⟨src.toNat, message.size⟩ : MemoryRegion).HasBytes m message)
    (input : Readable m src message.size)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (inputLow : src.toNat + message.size < 2^32)
    (apart : src.toNat + message.size ≤ sp.toNat - 512 ∨ sp.toNat + 1160 ≤ src.toNat)
    (iv : Compression.StateAt m (sp + 552) initialHash)
    (blocks : memLoad m (sp + 584) 64 = 0) :
    ∃ c t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l10555a, b, m⟩, []⟩ ⟨⟨.l105575, c, t⟩, []⟩ ∧
      Frame sp a c m t ∧ c[3] = ⟨64, sp+1152⟩ ∧ c[5].width = 64 ∧
      c[6] = ⟨64,src⟩ ∧ c[12].width = 64 ∧ c[13] = ⟨64, BitVec.ofNat 64 message.size⟩ ∧
      c[14] = ⟨64, sp+1136⟩ ∧ c[15] = ⟨64, 0x12a820⟩ ∧
      Compression.StateAt t (sp + 552) (compressBlocks initialHash message) ∧
      memLoad t (sp + 584) 64 = BitVec.ofNat 64 (message.size/64) := by
  let n := BitVec.ofNat 64 (message.size / 64)
  let counted := memStore m (sp + 584) n
  let pushed := memStore counted (sp - 8) (0x105572 : BitVec 64)
  have hb : (sp - 512).toNat = sp.toNat - 512 :=
    BitVec.toNat_sub_of_le (show (512 : BitVec 64) ≤ sp from depth)
  have hr : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from (by omega : 8 ≤ sp.toNat))
  have hc : (sp - 8 - 336).toNat = (sp - 8).toNat - 336 :=
    BitVec.toNat_sub_of_le (show (336 : BitVec 64) ≤ sp - 8 from
      (by omega : 336 ≤ (sp - 8).toNat))
  have ha (off : Nat) (bound : off ≤ 1160) :
      (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have h584 : (sp + 584).toNat = sp.toNat + 584 := ha 584 (by decide)
  have h552 : (sp + 552).toNat = sp.toNat + 552 := ha 552 (by decide)
  have countFrame : RamWriteFrame m counted (regions sp) :=
    (RamWriteFrame.refl _ _).memStore n
      ⟨⟨sp.toNat + 488, 104⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), by
        change sp.toNat + 488 ≤ (sp + 584).toNat ∧
          (sp + 584).toNat + 8 ≤ sp.toNat + 488 + 104 ∧ _
        omega⟩
  have pushFrame : RamWriteFrame m pushed (regions sp) :=
    countFrame.memStore (0x105572 : BitVec 64)
      ⟨_, List.mem_cons_self, by
        change sp.toNat - 512 ≤ (sp - 8).toNat ∧
          (sp - 8).toNat + 8 ≤ sp.toNat - 512 + 624 ∧ _
        omega⟩
  have code := fun x hx => Common.fnCode_subset_programImage x (code_l10555a x hx)
  have record : StoreOk Extracted.programImage m (sp + 584) 8 0x10555a 8 :=
    ParseSignature.storeOk_of_codeRange (off := 0) (stack.sub (by omega) (by omega)) code (by decide)
  have push : StoreOk Extracted.programImage counted (sp - 8) 8 0x10556d 5 :=
    ParseSignature.storeOk_of_codeRange (off := 19)
      ((stack.of_frame countFrame).sub (by omega) (by omega)) code (by decide)
  have rsp := (saved 4 (by decide)).trans args.rsp
  have countAdd : memLoad m (sp + 584) 64 + n = n := by
    rw [blocks]
    exact BitVec.zero_add n
  obtain ⟨child, called, childRsp, childDst, childSrc, childCount, childRbp, childSaved⟩ :=
    prepareCompression (sp := sp) (src := src) (n := n) (congrArg (Value.get 64) rsp)
      (congrArg (Value.get 64) source) (congrArg (Value.get 64) count) record
      (by rw [countAdd]; exact push)
  rw [countAdd] at called
  have written : Compression.StateAt pushed (sp + 552) initialHash := by
    apply Verify.Hash.Update.stateStore
      (Verify.Hash.Update.stateStore iv n (RangeApart.of_offsets rfl rfl (by decide)))
    exact RangeApart.of_offsets (addr_sub _ _) rfl (by decide)
  have ret : memLoad pushed (sp - 8) 64 = 0x105572 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have available := stack.of_frame pushFrame
  have childWidth : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → child[i].width = 64 := by
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width ((childSaved 3 (by decide)).trans ((saved 3 (by decide)).trans args.limit))
    · exact congrArg Value.width childRbp
    · exact congrArg Value.width
        ((childSaved 12 (by decide)).trans ((saved 12 (by decide)).trans args.buffered))
    · exact congrArg Value.width ((childSaved 13 (by decide)).trans length)
    · exact congrArg Value.width ((childSaved 14 (by decide)).trans ((saved 14 (by decide)).trans args.slice))
    · exact congrArg Value.width
        ((childSaved 15 (by decide)).trans ((saved 15 (by decide)).trans args.memcpy))
  have returnReadable : Readable pushed (sp - 8) 8 := (available.sub (by omega) (by omega)).readable
  have inputStack : src.toNat + message.size ≤ (sp - 8).toNat - 336 ∨
      (sp - 8).toNat ≤ src.toNat := by
    rw [hr]
    rcases apart with h | h
    · exact Or.inl (Nat.le_trans h (by omega))
    · exact Or.inr (by omega)
  have contract : Compression.Call child pushed (sp - 8) (sp + 552) src initialHash message := by
    refine ⟨childRsp, childDst, childSrc, childCount, childWidth, written,
      inputAfter pushFrame depth inputLow apart bytes, input.of_frame pushFrame,
      available.sub (by omega) (by omega), by omega, available.sub (by omega) (by omega),
      returnReadable, by rw [ret]; decide, Or.inr (by omega), inputStack⟩
  obtain ⟨out, run, post⟩ := Compression.execute contract
  have back := ParseSignature.exec_reaches_resume run (Verify.Hash.Update.returnFrame .l105572 0x105572)
    [] (by rw [post.tag, ret]; rfl)
  have before := (show (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l10555a, b, m⟩, []⟩ ⟨⟨.l105572, out.values, out.store⟩, []⟩ from
    .step (congrArg (Transfer.next _ []) called) back)
  have rbp := (post.preserved 5 (by decide)).trans childRbp
  obtain ⟨c, next, cSrc, cSaved⟩ :=
    resumeCompression (m := out.store) (src := src) (congrArg (Value.get 64) rbp)
  have keep (i : Fin Reg.count) (hi : i.val ∈ [3,12,13,14,15,22,39,50,51]) :
      c[i] = b[i] := (cSaved i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        omega)).trans ((post.preserved i (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
          omega)).trans (childSaved i hi))
  have within : RegionsWithin (Compression.footprint (sp - 8) (sp + 552)) (regions sp) := by
    intro r h
    simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · refine ⟨_, List.mem_cons_self, ?_⟩
      change sp.toNat - 512 ≤ (sp - 8).toNat - 336 ∧
        (sp - 8).toNat - 336 + 336 ≤ sp.toNat - 512 + 624
      omega
    · refine ⟨⟨sp.toNat + 488, 104⟩,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), ?_⟩
      change sp.toNat + 488 ≤ (sp + 552).toNat ∧
        (sp + 552).toNat + 32 ≤ sp.toNat + 488 + 104
      omega
  have outside : Outside (Compression.footprint (sp - 8) (sp + 552)) (sp + 584) 8 := by
    refine ⟨by omega, fun r h => ?_⟩
    simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inr (by change (sp - 8).toNat - 336 + 336 ≤ _; omega)
    · exact Or.inr (by change (sp + 552).toNat + 32 ≤ _; omega)
  refine ⟨c, out.store, before.trans (.single (congrArg (Transfer.next _ []) next)), ?_,
    (keep 3 (by decide)).trans ((saved 3 (by decide)).trans args.limit),
    congrArg Value.width ((cSaved 5 (by decide)).trans rbp), cSrc,
    congrArg Value.width ((keep 12 (by decide)).trans ((saved 12 (by decide)).trans args.buffered)),
    (keep 13 (by decide)).trans length,
    (keep 14 (by decide)).trans ((saved 14 (by decide)).trans args.slice),
    (keep 15 (by decide)).trans ((saved 15 (by decide)).trans args.memcpy), post.state, ?_⟩
  · refine ⟨?_, (keep 22 (by decide)).trans ((saved 22 (by decide)).trans args.direction),
      ?_, pushFrame.trans post.writes within⟩
    · exact (cSaved 4 (by decide)).trans
        (post.rsp.trans (congrArg (Value.mk 64) (BitVec.sub_add_cancel sp 8)))
    · intro i hi
      exact (keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
        (saved i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
  · rw [post.writes.memLoad_eq outside]
    unfold pushed counted
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets (addr_sub _ _) rfl (by decide)),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]

end Update
end K256.Proofs.Signing.Hash
