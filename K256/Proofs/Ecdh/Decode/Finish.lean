import K256.Proofs.Ecdh.Decode.Return
import K256.Proofs.Ecdh.Decode.Repr
import K256.Proofs.Ecdh.Decode.Convert.Barrier
import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Ecdh.Decode

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Spec.Program K256.Proofs.Ecdh.LIR Standards.SECG.ECC

set_option maxRecDepth 2048 in
theorem finish {args : Values Value Reg.count} {mem : Ram} {sp dst : BitVec 64}
    {q : Curve.Point} (point : AffinePointAt mem (sp + 144) q)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [2,8,9] → args[i].width = 64)
    (rsp : args[4].get 64 = sp) (rbx : args[3].get 64 = dst)
    (r14 : args[14].get 64 = sp + 144) (r15 : (args[15].get 64).setWidth 8 = 1)
    (df : args[22].get 1 = 0) (valid : memLoad mem (sp + 232) 8 = 1)
    (stack : Readable mem (sp - 9) 281) (scratch : Writable Extracted.programImage mem (sp - 9) 9)
    (dest : Writable Extracted.programImage mem dst 89)
    (apart : dst.toNat + 89 ≤ (sp - 9).toNat ∨ (sp - 9).toNat + 281 ≤ dst.toNat)
    (low : (memLoad mem (sp + 264) 64).toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121177,args,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64, memLoad mem (sp + 264) 64⟩ ∧ out.values[0] = ⟨64,dst⟩ ∧
      out.values[4] = ⟨64,sp + 272⟩ ∧ out.values[3] = ⟨64,memLoad mem (sp + 240) 64⟩ ∧
      out.values[14] = ⟨64,memLoad mem (sp + 248) 64⟩ ∧
      out.values[15] = ⟨64,memLoad mem (sp + 256) 64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,13,22,39,50,51] → out.values[i] = args[i]) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame mem out.store [⟨(sp-9).toNat,9⟩, ⟨dst.toNat,89⟩] ∧
      memLoad out.store (dst+88) 8 = 1 ∧ AffinePointAt out.store dst q := by
  let cp := memCopy mem dst (sp+144) 88
  let pushed := memStore cp (sp-8) (0x121196 : BitVec 64)
  let scratchRegion : MemoryRegion := ⟨(sp-9).toNat,9⟩
  let destRegion : MemoryRegion := ⟨dst.toNat,89⟩
  let regions := [scratchRegion,destRegion]
  have sl := stack.low
  have dl := dest.readable.low
  have addr (n : Nat) (hn : n ≤ 272) :
      (sp+BitVec.ofNat 64 n).toNat = (sp-9).toNat + 9+n := by
    have nx := toNat_of_offsets (a := sp) (n := 1) (addr_self sp) (addr_sub sp 9) sl (by decide)
    change sp.toNat = (sp-9).toNat + 9 at nx
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have daddr (n : Nat) (hn : n ≤ 89) : (dst+BitVec.ofNat 64 n).toNat = dst.toNat+n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (by omega)]
  have n144 : (sp+144).toNat = (sp-9).toNat+153 := addr 144 (by decide)
  have slotPos : (sp-8).toNat = (sp-9).toNat + 1 := by
    have h := toNat_of_offsets (addr_sub sp 8) (addr_sub sp 9) sl (n := 8) (by decide)
    exact h
  have slotWrite : Writable Extracted.programImage mem (sp-8) 8 := scratch.sub (by omega) (by omega)
  have dstIn : InRegions regions dst 88 := ⟨destRegion, by simp [regions], Nat.le_refl _, by
    change dst.toNat+88 ≤ dst.toNat+89 ∧ dst.toNat+88 ≤ 2^64; omega⟩
  have slotIn : InRegion scratchRegion (sp-8) 8 := by
    change (sp-9).toNat ≤ _ ∧ _ ≤ (sp-9).toNat+9 ∧ _ ≤ 2^64
    omega
  have copied : RamWriteFrame mem cp regions := (RamWriteFrame.refl _ _).memStore _ dstIn
  have pf : RamWriteFrame cp pushed [scratchRegion] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨scratchRegion,List.mem_cons_self,slotIn⟩
  have rd : Readable mem (sp+144) 88 := stack.of_offsets rfl (addr_sub sp 9) (by decide)
  have wr : StoreOk Extracted.programImage mem dst 88 0x12118a 3 :=
    ParseSignature.storeOk_of_codeRange (off := 19) (dest.sub (Nat.le_refl _) (by omega))
      (fun x hx => Common.fnCode_subset_programImage x (code_l121177 x hx)) (by decide)
  have rep : RepMovsOk Extracted.programImage mem (args[22].get 1) (sp+144) dst 11 8 0x12118a 3 :=
    ⟨df, rd.low, wr.low, rd.present, wr.present, by
      change (sp+144).toNat+88 ≤ dst.toNat ∨ dst.toNat+88 ≤ (sp+144).toNat
      omega, wr.tables, wr.apart, wr.notCode⟩
  obtain ⟨b,call,bwidth,one,bsp,keep⟩ := copyCall widths rsp rbx r14 r15
    (LoadOk.of_offsets stack rfl (addr_sub sp 9) (by decide)) valid rep
    (ParseSignature.storeOk_of_codeRange (off := 26) (slotWrite.of_frame copied)
      (fun x hx => Common.fnCode_subset_programImage x (code_l121177 x hx)) (by decide))
  have slotRet : memLoad pushed (sp-8) 64 = 0x121196 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have sameReg : RegionsWithin [scratchRegion] regions := fun r h =>
    ⟨r, List.mem_append_left [destRegion] h, Nat.le_refl _, Nat.le_refl _⟩
  have fpush := copied.trans pf sameReg
  have adj : sp-8-1 = sp-9 := by bv_omega
  obtain ⟨c,child,ret,csp,cax,cf,kept⟩ := Convert.convertBarrier (sp := sp-8) (congrArg (Value.get 64) bsp)
    (adj ▸ (scratch.sub (Nat.le_refl _) (by omega)).of_frame fpush)
    (slotWrite.readable.of_frame fpush) slotRet (by decide)
  rw [adj] at cf
  have narrow : RegionsWithin [⟨(sp-9).toNat,1⟩] [scratchRegion] := by
    rintro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨scratchRegion, List.mem_cons_self, Nat.le_refl _, by change (sp-9).toNat+1 ≤ (sp-9).toNat+9; omega⟩
  have scratchFrame := pf.trans cf narrow
  have fullFrame := copied.trans scratchFrame sameReg
  let m := memStore c.store (dst+88) (1 : BitVec 8)
  have n88 : (dst+88).toNat = dst.toNat+88 := daddr 88 (by decide)
  have finalFrame : RamWriteFrame mem m regions := fullFrame.memStore _
    ⟨destRegion,by simp [regions], by change dst.toNat ≤ _ ∧ _ ≤ dst.toNat+89 ∧ _ ≤ 2^64; omega⟩
  have unchanged (k : Nat) (h : 240 ≤ k) (h' : k ≤ 264) :
      memLoad m (sp+BitVec.ofNat 64 k) 64 = memLoad mem (sp+BitVec.ofNat 64 k) 64 := by
    have n := addr k (by omega)
    apply finalFrame.memLoad_eq
    refine ⟨by change _+8 ≤ 2^64; omega, ?_⟩
    intro r hr
    simp only [regions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · change _+8 ≤ (sp-9).toNat ∨ (sp-9).toNat+9 ≤ _; omega
    · change _+8 ≤ dst.toNat ∨ dst.toNat+89 ≤ _; omega
  have u240 : memLoad m (sp+240) 64 = memLoad mem (sp+240) 64 := unchanged 240 (by decide) (by decide)
  have u248 : memLoad m (sp+248) 64 = memLoad mem (sp+248) 64 := unchanged 248 (by decide) (by decide)
  have u256 : memLoad m (sp+256) 64 = memLoad mem (sp+256) 64 := unchanged 256 (by decide) (by decide)
  have u264 : memLoad m (sp+264) 64 = memLoad mem (sp+264) 64 := unchanged 264 (by decide) (by decide)
  have hcsp : c.values[4].get 64 = sp := by rw [csp,BitVec.sub_add_cancel]; rfl
  have hcbx : c.values[3].get 64 = dst :=
    (congrArg (Value.get 64) ((kept 3 (by decide)).trans (keep 3 (by decide)))).trans rbx
  have hax : (c.values[0].get 64).setWidth 8 = 1 := by rw [cax, one]; rfl
  obtain ⟨out,exit,store,ot,rax,osp,bx,r14',r15',keep'⟩ := returnBlock hcsp hcbx hax
    (ParseSignature.storeOk_of_codeRange (off := 0)
      ((dest.sub (a := dst+88) (by omega) (by omega)).of_frame fullFrame)
      (fun x hx => Common.fnCode_subset_programImage x (code_l121196 x hx)) (by decide))
    (fun k hk => by
      have h : k ≤ 264 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
      have n := addr k (by omega)
      exact LoadOk.of_region (stack.of_frame finalFrame) (by omega) (by omega))
    (by change (memLoad m (sp+264) 64).toNat < _; rw [u264]; exact low)
  refine ⟨out, ParseSignature.exec_call call child (by rw [ret]; rfl)
    (.done (by change Transfer.next _ [] _ = _; rw [show choiceReturn.resume c = ⟨.l121196,c.values,c.store⟩ by rfl, exit]; rfl)),
    ot.trans (by rw [u264]), rax, osp,
    bx.trans (by rw [u240]),
    r14'.trans (by rw [u248]),
    r15'.trans (by rw [u256]), ?_, ?_, store ▸ finalFrame, ?_, ?_⟩
  · intro i hi
    exact (keep' i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans ((kept i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
      (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)))
  · intro i hi
    have h : i.val ∈ [1,2,5,6,7,8,9,12,13,22,39,50,51] := by
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
    rw [keep' i h, kept i (by simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    exact bwidth i hi
  · rw [store]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · apply point.of_copy
    intro off width fits
    have d := daddr off (by omega)
    rw [store, memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_toNat (by change _+1 ≤ 2^64; omega)
      (by omega) (Or.inr (by omega)))]
    apply Eq.trans (scratchFrame.memLoad_eq ?_)
    · exact Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) fits
    · refine ⟨by omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change _ ≤ (sp-9).toNat ∨ (sp-9).toNat+9 ≤ _
      omega

end K256.Proofs.Ecdh.Decode
