import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.Guards
import K256.Proofs.Verify.LIR.Fn103f30

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private abbrev entryKept : List Nat := [4,5,13,14,22,39,50,51]
private abbrev callKept : List Nat := [3,5,12,13,14,22,39,50,51]
private abbrev returnKept : List Nat := [4,5,12,13,22,39,50,51]

local macro "kept_regs" : tactic => `(tactic|
  (rintro ⟨i,hi⟩ h
   simp only [entryKept,callKept,returnKept,List.mem_cons,List.not_mem_nil,or_false] at h
   repeat' first | rfl | (obtain rfl | h := h) | subst i))

set_option maxRecDepth 3200 in
private theorem loadSecond {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (last : Bool) (rsp : a[4].get 64 = sp fr)
    (ptr : a[14].get 64 = fr.rsi + BitVec.ofNat 64 (offset last))
    (rd : LoadOk m (fr.rsi + BitVec.ofNat 64 (offset last)) 8)
    (rdLen : LoadOk m (fr.rsi + BitVec.ofNat 64 (offset last) + 8) 8)
    (src : memLoad m (fr.rsi + BitVec.ofNat 64 (offset last)) 64 = source fr last)
    (len : memLoad m (fr.rsi + BitVec.ofNat 64 (offset last) + 8) 64 = BitVec.ofNat 64 (length last))
    (rdUsed : LoadOk m (sp fr + 455) 1)
    (byte : memLoad m (sp fr + 455) 8 = BitVec.ofNat 8 (used last)) :
    ∃ b : Verify.Core.Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l1047fb,a,m⟩ = .jump ⟨.l1047d0,b,m⟩ ∧
      b[3] = ⟨64,BitVec.ofNat 64 (length last)⟩ ∧
      b[6].get 64 = source fr last ∧ b[7] = ⟨64,BitVec.ofNat 64 (used last)⟩ ∧
      b[12].width = 64 ∧ (∀ i : Fin Reg.count, i.val ∈ entryKept → b[i] = a[i]) := by
  have extend : (BitVec.ofNat 8 (used last)).setWidth 64 = BitVec.ofNat 64 (used last) := by
    cases last <;> rfl
  have borrow : (subSpec (BitVec.ofNat 64 (length last))
      (64 - BitVec.ofNat 64 (used last))).2.CF = true := by
    cases last <;> decide
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,ptr,rd,rdLen,rdUsed,src,len,byte]
    simp only [extend,borrow,↓reduceIte]
    rfl
  case post =>
    exact ⟨rfl,rfl,rfl,rfl,by kept_regs⟩

set_option maxRecDepth 3200 in
private theorem callSecond {fr : Activation} {b : Verify.Core.Registers} {m : Ram}
    (last : Bool) (rsp : b[4].get 64 = sp fr)
    (di : b[7] = ⟨64,BitVec.ofNat 64 (used last)⟩)
    (buf : b[13].get 64 = context fr true + 64)
    (count : b[3].get 64 = BitVec.ofNat 64 (length last))
    (sourceReg : b[6].get 64 = source fr last)
    (store : StoreOk Extracted.programImage m (sp fr - 8) 8 0x1047d9 6)
    (gotRead : LoadOk m 0x203dd0 8) (got : memLoad m 0x203dd0 64 = 0x12a820) :
    ∃ c : Verify.Core.Registers,
      program.runBlock (dialect Extracted.programImage) ⟨copyAt true,b,m⟩ =
        .call ⟨.l12a820,c,pushed fr true m⟩
          (Verify.Core.Lincomb.callResume (resumeAt true) (returnAddress true)) ∧
      c[4].get 64 = sp fr - 8 ∧ c[7].get 64 = destination fr true last ∧
      c[6].get 64 = source fr last ∧ c[2].get 64 = BitVec.ofNat 64 (length last) ∧
      c[15] = ⟨64,BitVec.ofNat 64 (used last)⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ callKept → c[i] = b[i]) := by
  have di64 : b[7].get 64 = BitVec.ofNat 64 (used last) := congrArg (Value.get 64) di
  have di32 : b[7].get 32 = BitVec.ofNat 32 (used last) := by
    rw [di]
    cases last <;> rfl
  have dest : BitVec.ofNat 64 (used last) + (context fr true + 64) =
      destination fr true last := BitVec.add_comm _ _
  refine ⟨?_,?run,?post⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨.l1047d0,b,m⟩ = _
    cfg_eval [rsp,di64,di32,buf,count,gotRead,got,store,dest]
    rfl
  case post =>
    refine ⟨rfl,rfl,sourceReg,rfl,?_,by kept_regs⟩
    cases last <;> rfl

set_option maxRecDepth 3200 in
private theorem resumeSecond {fr : Activation} {d : Verify.Core.Registers} {m : Ram}
    (last : Bool) (rsp : d[4].get 64 = sp fr)
    (count : d[3].get 8 = BitVec.ofNat 8 (length last))
    (old : d[15].get 8 = BitVec.ofNat 8 (used last))
    (cursor : d[14].get 64 = fr.rsi + BitVec.ofNat 64 (offset last))
    (stopRead : LoadOk (copied fr true last m) (sp fr + 8) 8)
    (stop : memLoad (copied fr true last m) (sp fr + 8) 64 = fr.rsi + 48)
    (store : StoreOk Extracted.programImage (copied fr true last m) (sp fr + 455) 1 0x1047e7 7) :
    ∃ e : Verify.Core.Registers, Verify.Core.Reaches (resumeAt true) d (copied fr true last m)
        (target true last) e (result fr true last m) ∧
      e[3].width = 64 ∧ e[14] = ⟨64,fr.rsi + BitVec.ofNat 64 (offset last + 16)⟩ ∧
      e[15] = ⟨64,fr.rsi + 48⟩ ∧ (∀ i : Fin Reg.count, i.val ∈ returnKept → e[i] = d[i]) := by
  have next : fr.rsi + BitVec.ofNat 64 (offset last) + 16 =
      fr.rsi + BitVec.ofNat 64 (offset last + 16) := by
    rw [BitVec.add_assoc,BitVec.ofNat_add]
    rfl
  have cmp : (cmpSpec (fr.rsi + BitVec.ofNat 64 (offset last + 16)) (fr.rsi+48)).ZF = last := by
    rw [cmpSpec_ZF]
    cases last
    · apply beq_eq_false_iff_ne.mpr
      change fr.rsi + 32 ≠ fr.rsi + 48
      bv_omega
    · exact beq_self_eq_true _
  have marker : context fr true + 127 = sp fr + 455 := by
    change sp fr + 328 + 127 = _
    bv_omega
  have count' : (d[3].get 64).setWidth 8 = BitVec.ofNat 8 (length last) :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans count
  have old' : (d[15].get 64).setWidth 8 = BitVec.ofNat 8 (used last) :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans old
  have sum : BitVec.ofNat 8 (length last) + BitVec.ofNat 8 (used last) = 33 := by
    cases last <;> rfl
  obtain ⟨e,run,width,slice,stopReg,kept⟩ :
      ∃ e : Verify.Core.Registers, program.runBlock (dialect Extracted.programImage)
          ⟨.l1047df,d,copied fr true last m⟩ = .jump ⟨target true last,e,result fr true last m⟩ ∧
        e[3].width = 64 ∧ e[14] = ⟨64,fr.rsi + BitVec.ofNat 64 (offset last + 16)⟩ ∧
        e[15] = ⟨64,fr.rsi + 48⟩ ∧ (∀ i : Fin Reg.count, i.val ∈ returnKept → e[i] = d[i]) := by
    cases last <;>
      (refine ⟨?_,?run,?post⟩
       case run =>
         unfold result
         rw [marker]
         cfg_eval [rsp,cursor,stopRead,stop,store,next]
         simp only [count',old',sum,setWidth_mergeGPR8,cmp,Bool.false_eq_true,ite_false,ite_true]
         rfl
       case post =>
         exact ⟨rfl,rfl,rfl,by kept_regs⟩)
  refine ⟨e,.single ?_,width,slice,stopReg,kept⟩
  change (program.runBlock _ ⟨.l1047df,d,copied fr true last m⟩).next _ [] = _
  rw [run]
  rfl

theorem runSecond : Runs true := by
  intro fr secret reduced state a m last env live slots cursor usedEq
  have marker : context fr true + 127 = sp fr + 455 := by
    change sp fr + 328 + 127 = _
    bv_omega
  have ⟨rsp,df,_,_,_,_⟩ := live.atoms
  have rspv : a[4].get 64 = sp fr := congrArg (Value.get 64) rsp
  have slicev : a[14].get 64 = fr.rsi + BitVec.ofNat 64 (offset last) :=
    congrArg (Value.get 64) cursor.slice
  obtain ⟨rd,rdLen,src,len,srcRead⟩ := descriptor env live.writes last
  obtain ⟨push,mark,stopRead,gotRead,got,markAfter,_⟩ := guards env true last live
  rw [marker] at mark usedEq markAfter
  obtain ⟨b,load,lenReg,srcReg,usedReg,tempW,bKeep⟩ :=
    loadSecond last rspv slicev ⟨rd.low,rd.present⟩ ⟨rdLen.low,rdLen.present⟩ src len
      ⟨mark.readable.low,mark.readable.present⟩ usedEq
  have pushOk := ParseSignature.storeOk_of_codeRange (off := 9) (len := 6) push
    (fun x hx => Common.fnCode_subset_programImage x (code_l1047d0 x hx)) (by decide)
  obtain ⟨c,call,stack,di,si,dx,oldReg,cKeep⟩ := callSecond last
    ((congrArg (Value.get 64) (bKeep 4 (by decide))).trans rspv) usedReg
    (congrArg (Value.get 64) ((bKeep 13 (by decide)).trans cursor.buf))
    (congrArg (Value.get 64) lenReg) srcReg pushOk ⟨gotRead.low,gotRead.present⟩ got
  have dfv : c[22].get 1 = 0 :=
    congrArg (Value.get 1) ((cKeep 22 (by decide)).trans ((bKeep 22 (by decide)).trans df))
  obtain ⟨d,copy,back,dKeep⟩ :=
    runCopy env live.writes true last call stack di si dx dfv srcRead
  have markOk := ParseSignature.storeOk_of_codeRange (off := 8) (len := 7) markAfter
    (fun x hx => Common.fnCode_subset_programImage x (code_l1047df x hx)) (by decide)
  have stopAfter := stopRead.of_frame (copiedFrame env true last m)
  have dCount : d[3].get 8 = BitVec.ofNat 8 (length last) := by
    exact (congrArg (Value.get 8)
      ((dKeep 3 (by decide)).trans ((cKeep 3 (by decide)).trans lenReg))).trans (by cases last <;> rfl)
  have dUsed : d[15].get 8 = BitVec.ofNat 8 (used last) := by
    exact (congrArg (Value.get 8)
      ((dKeep 15 (by decide)).trans oldReg)).trans (by cases last <;> rfl)
  have dSlice := (dKeep 14 (by decide)).trans ((cKeep 14 (by decide)).trans (bKeep 14 (by decide)))
  obtain ⟨e,finish,w3,slice,stop,eKeep⟩ :=
    resumeSecond last (congrArg (Value.get 64) back) dCount dUsed
      ((congrArg (Value.get 64) dSlice).trans slicev) ⟨stopAfter.low,stopAfter.present⟩
      (copiedStop env true last slots) markOk
  have enter : Verify.Core.Reaches (loopAt true) a m (copyAt true) b m := by
    apply Semantics.Reaches.single
    change (program.runBlock _ ⟨.l1047fb,a,m⟩).next _ [] = _
    rw [load]
    rfl
  have keep (i : Fin Reg.count) (h : i.val ∈ [5,13,22,39,50,51]) : e[i] = a[i] := by
    exact (eKeep i (by
      simp only [returnKept,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans
      ((dKeep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans
        ((cKeep i (by simp only [callKept,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans
          (bKeep i (by simp only [entryKept,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega))))
  refine ⟨e,(enter.trans copy).trans finish,⟨(keep 13 (by decide)).trans cursor.buf,slice,
    fun _ => (keep 5 (by decide)).trans (cursor.hash rfl), fun _ => stop⟩,?_,(fun h => by cases h),?_⟩
  · intro i h
    by_cases h4 : i.val = 4
    · have same : i = 4 := Fin.ext h4
      subst i
      exact (eKeep 4 (by decide)).trans (back.trans rsp.symm)
    · apply keep
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      omega
  · rintro ⟨i,hi⟩ h
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact w3
    · exact congrArg Value.width ((keep 5 (by decide)).trans (cursor.hash rfl))
    · exact (congrArg Value.width ((eKeep 12 (by decide)).trans
        ((dKeep 12 (by decide)).trans (cKeep 12 (by decide))))).trans tempW
    · exact congrArg Value.width ((keep 13 (by decide)).trans cursor.buf)
    · exact congrArg Value.width slice
    · exact congrArg Value.width stop

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices
