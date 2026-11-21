import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.Guards
import K256.Proofs.Verify.LIR.Fn103f30

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

local macro "short_regs" : tactic => `(tactic|
  (rintro ⟨i, hi⟩ h
   simp only [List.mem_cons, List.not_mem_nil, or_false] at h
   repeat' first | rfl | (obtain rfl | h := h) | subst i))

private abbrev firstKeep : List Nat := [4,13,14,15,22,39,50,51]

set_option maxRecDepth 3200 in
private theorem loadFirst {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (last : Bool) (rsp : a[4].get 64 = sp fr)
    (ptr : a[15].get 64 = fr.rsi + BitVec.ofNat 64 (offset last))
    (rd : Readable m (fr.rsi + BitVec.ofNat 64 (offset last)) 8)
    (rdLen : Readable m (fr.rsi + BitVec.ofNat 64 (offset last) + 8) 8)
    (src : memLoad m (fr.rsi + BitVec.ofNat 64 (offset last)) 64 = source fr last)
    (len : memLoad m (fr.rsi + BitVec.ofNat 64 (offset last) + 8) 64 = BitVec.ofNat 64 (length last))
    (rdUsed : Readable m (context fr false + 127) 1)
    (byte : memLoad m (context fr false + 127) 8 = BitVec.ofNat 8 (used last)) :
    ∃ c : Verify.Core.Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l10422b,a,m⟩ = .jump ⟨.l104200,c,m⟩ ∧
      c[3] = ⟨64,source fr last⟩ ∧ c[12] = ⟨64,BitVec.ofNat 64 (length last)⟩ ∧
      c[7].get 64 = BitVec.ofNat 64 (used last) ∧
      (∀ i : Fin Reg.count, i.val ∈ firstKeep → c[i] = a[i]) := by
  have rd' : LoadOk m _ 8 := ⟨rd.low,rd.present⟩
  have rdLen' : LoadOk m _ 8 := ⟨rdLen.low,rdLen.present⟩
  have mark : context fr false + 127 = sp fr + 287 := by
    change sp fr + 160 + 127 = _
    bv_omega
  rw [mark] at rdUsed byte
  have used' : LoadOk m _ 1 := ⟨rdUsed.low,rdUsed.present⟩
  have borrow : (subSpec (BitVec.ofNat 64 (length last))
      (64 - BitVec.ofNat 64 (used last))).2.CF = true := by
    cases last <;> decide
  have extend : (BitVec.ofNat 8 (used last)).setWidth 64 = BitVec.ofNat 64 (used last) := by
    cases last <;> rfl
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · cfg_eval [rsp, ptr, rd', rdLen', used', src, len, byte]
    simp only [extend, borrow, ite_true]
    rfl
  · exact ⟨rfl, rfl, rfl, by short_regs⟩

private abbrev callKeep : List Nat := [3,12,13,14,15,22,39,50,51]

set_option maxRecDepth 3200 in
private theorem callFirst {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (last : Bool) (rsp : a[4].get 64 = sp fr) (buf : a[13].get 64 = context fr false + 64)
    (di : a[7].get 64 = BitVec.ofNat 64 (used last))
    (si : a[3].get 64 = source fr last) (dx : a[12].get 64 = BitVec.ofNat 64 (length last))
    (w : Writable Extracted.programImage m (sp fr - 8) 8)
    (got : Readable m 0x203dd0 8) (callee : memLoad m 0x203dd0 64 = 0x12a820) :
    ∃ c : Verify.Core.Registers,
      program.runBlock (dialect Extracted.programImage) ⟨copyAt false,a,m⟩ =
        .call ⟨.l12a820,c,pushed fr false m⟩
          (Verify.Core.Lincomb.callResume (resumeAt false) (returnAddress false)) ∧
      c[4].get 64 = sp fr - 8 ∧ c[7].get 64 = destination fr false last ∧
      c[6].get 64 = source fr last ∧ c[2].get 64 = BitVec.ofNat 64 (length last) ∧
      c[5] = ⟨64,BitVec.ofNat 64 (used last)⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ callKeep → c[i] = a[i]) := by
  have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x10420b 6 :=
    ParseSignature.storeOk_of_codeRange (off := 11) w
      (fun x hx => Common.fnCode_subset_programImage x (code_l104200 x hx)) (by decide +kernel)
  have load : LoadOk m 0x203dd0 8 := ⟨got.low,got.present⟩
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · change program.runBlock _ ⟨.l104200,a,m⟩ = _
    cfg_eval [rsp,buf,di,si,dx,push,load,callee]
    rfl
  · refine ⟨rfl, ?_, rfl, rfl, ?_, by short_regs⟩
    · change BitVec.ofNat 64 (used last) + (context fr false + 64) =
        context fr false + 64 + BitVec.ofNat 64 (used last)
      exact BitVec.add_comm ..
    · cases last <;> rfl

private abbrev resumeKeep : List Nat := [3,4,5,13,14,22,39,50,51]

set_option maxRecDepth 3200 in
private theorem resumeFirst {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (last : Bool) (rsp : a[4].get 64 = sp fr)
    (ptr : a[15].get 64 = fr.rsi + BitVec.ofNat 64 (offset last))
    (bp : a[5].get 64 = BitVec.ofNat 64 (used last))
    (len : a[12].get 64 = BitVec.ofNat 64 (length last))
    (w : Writable Extracted.programImage (copied fr false last m) (context fr false + 127) 1)
    (rd : Readable (result fr false last m) (sp fr + 8) 8)
    (stop : memLoad (result fr false last m) (sp fr + 8) 64 = fr.rsi + 48) :
    ∃ b : Verify.Core.Registers,
      program.runBlock (dialect Extracted.programImage) ⟨resumeAt false,a,copied fr false last m⟩ =
        .jump ⟨target false last,b,result fr false last m⟩ ∧
      b[15] = ⟨64,fr.rsi + BitVec.ofNat 64 (offset last + 16)⟩ ∧ b[12].width = 64 ∧
      (∀ i : Fin Reg.count, i.val ∈ resumeKeep → b[i] = a[i]) := by
  have mark : context fr false + 127 = sp fr + 287 := by
    change sp fr + 160 + 127 = _
    bv_omega
  rw [mark] at w
  have write : StoreOk Extracted.programImage (copied fr false last m) (sp fr + 287) 1 0x104214 8 :=
    ParseSignature.storeOk_of_codeRange (off := 3) w
      (fun x hx => Common.fnCode_subset_programImage x (code_l104211 x hx)) (by decide +kernel)
  have read : LoadOk (result fr false last m) (sp fr + 8) 8 := ⟨rd.low,rd.present⟩
  have next : fr.rsi + BitVec.ofNat 64 (offset last) + 16 =
      fr.rsi + BitVec.ofNat 64 (offset last + 16) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
    rfl
  have zf : (cmpSpec (fr.rsi + BitVec.ofNat 64 (offset last + 16)) (fr.rsi + 48)).ZF = last := by
    cases last
    · rw [cmpSpec_ZF, beq_eq_false_iff_ne]
      change fr.rsi + 32 ≠ fr.rsi + 48
      bv_omega
    · rw [cmpSpec_ZF]
      exact beq_self_eq_true _
  have byte : (mergeGPR 8
      ((BitVec.ofNat 64 (length last)).setWidth 8 + (BitVec.ofNat 64 (used last)).setWidth 8)
      (BitVec.ofNat 64 (length last))).setWidth 8 = 33 := by
    cases last <;> decide
  unfold result at read stop ⊢
  rw [mark] at read stop ⊢
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · change program.runBlock _ ⟨.l104211,a,_⟩ = _
    cfg_eval [rsp,ptr,bp,len,write,next,byte,read,stop,zf]
    simp only [byte,read,stop,zf,ite_true,target,loopAt]
    split
    · rename_i h
      rw [ite_eq_left h]
      rfl
    · rename_i h
      rw [ite_eq_right h]
      rfl
  · exact ⟨rfl,rfl,by short_regs⟩

theorem runFirst : Runs false := by
  intro fr secret reduced state a m last env live slots cursor usedAt
  obtain ⟨rSlot, dir, _⟩ := live.atoms
  obtain ⟨rdSrc, rdLen, src, len, srcRead⟩ := descriptor env live.writes last
  obtain ⟨push, mark, _, rdGot, got, wr, rdStop⟩ := guards env false last live
  obtain ⟨c, load, cSrc, cLen, cUsed, cKeep⟩ := loadFirst last
    (congrArg (Value.get 64) rSlot) (congrArg (Value.get 64) cursor.slice)
    rdSrc rdLen src len mark.readable usedAt
  obtain ⟨d, call, dSp, dDst, dSrc, dLen, dUsed, dKeep⟩ := callFirst last
    (congrArg (Value.get 64) ((cKeep 4 (by decide)).trans rSlot))
    (congrArg (Value.get 64) ((cKeep 13 (by decide)).trans cursor.buf))
    cUsed (congrArg (Value.get 64) cSrc) (congrArg (Value.get 64) cLen) push rdGot got
  obtain ⟨e, back, eSp, eKeep⟩ := runCopy env live.writes false last call dSp dDst dSrc dLen
    (congrArg (Value.get 1) ((dKeep 22 (by decide)).trans ((cKeep 22 (by decide)).trans dir))) srcRead
  have ec (i : Fin Reg.count) (hi : i.val ∈ callKeep) : e[i] = c[i] := by
    exact (eKeep i (by
      simp only [callKeep,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      omega)).trans (dKeep i hi)
  have ea (i : Fin Reg.count) (hi : i.val ∈ [13,14,15,22,39,50,51]) : e[i] = a[i] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    exact (ec i (by simp only [callKeep,List.mem_cons,List.not_mem_nil,or_false]; omega)).trans
      (cKeep i (by simp only [firstKeep,List.mem_cons,List.not_mem_nil,or_false]; omega))
  have eUsed := (eKeep 5 (by decide)).trans dUsed
  have eLen := (ec 12 (by decide)).trans cLen
  have stop := ((resultFrame env false last m).memLoad_eq
    (slotOutside env false last 8 (by decide))).trans slots.stop
  obtain ⟨b, next, bSlice, bLen, bKeep⟩ := resumeFirst last (congrArg (Value.get 64) eSp)
    (congrArg (Value.get 64) ((ea 15 (by decide)).trans cursor.slice))
    (congrArg (Value.get 64) eUsed) (congrArg (Value.get 64) eLen) wr rdStop stop
  refine ⟨b, .step (congrArg (Transfer.next _ []) load)
    (back.trans (.step (congrArg (Transfer.next _ []) next) (.refl _))), ?_, ?_, ?_, ?_⟩
  · exact ⟨(bKeep 13 (by decide)).trans ((ea 13 (by decide)).trans cursor.buf),
      bSlice, Bool.noConfusion, Bool.noConfusion⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    refine (bKeep i (by simp only [resumeKeep,List.mem_cons,List.not_mem_nil,or_false]; omega)).trans ?_
    rcases hi with h | h
    · obtain ⟨i, hi⟩ := i
      change i = 4 at h
      subst i
      exact eSp.trans rSlot.symm
    · exact ea i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega)
  · exact fun _ => (bKeep 14 (by decide)).trans (ea 14 (by decide))
  · rintro ⟨i, hi⟩ h
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h | h | h | h | h <;> subst i
    · exact congrArg Value.width ((bKeep 3 (by decide)).trans ((ec 3 (by decide)).trans cSrc))
    · exact congrArg Value.width ((bKeep 5 (by decide)).trans eUsed)
    · exact bLen
    · exact congrArg Value.width ((bKeep 13 (by decide)).trans ((ea 13 (by decide)).trans cursor.buf))
    · exact (congrArg Value.width ((bKeep 14 (by decide)).trans (ea 14 (by decide)))).trans
        (live.savedWidths 14 (by decide))
    · exact congrArg Value.width bSlice

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices
