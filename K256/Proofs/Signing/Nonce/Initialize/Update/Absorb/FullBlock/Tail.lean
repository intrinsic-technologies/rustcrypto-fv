import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock.TailAccess
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Verify.LIR.Fn103f30

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

private theorem reachesJump {l l' : Label} {a b : Verify.Core.Registers} {m n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨l, a, m⟩ = .jump ⟨l', b, n⟩) :
    Verify.Core.Reaches l a m l' b n := by
  apply Semantics.Reaches.single
  change (program.runBlock (dialect Extracted.programImage) _).next _ [] = _
  rw [run]
  rfl

set_option maxRecDepth 3200 in
set_option maxHeartbeats 1000000 in
theorem prepareCopy (second : Bool) : PrepareCopy second := by
  intro fr a m stack regs widths access
  have rsp : a[4].get 64 = sp fr := congrArg (Value.get 64) stack
  have dst : a[13].get 64 = context fr second + 64 := congrArg (Value.get 64) regs.buf
  have next := regs.next
  have len := regs.length
  have gotRead := access.gotRead
  have got := access.got
  have used := access.used
  have markedUsed := access.used.memStore (context fr second + 127) (0 : BitVec 8)
  have push := access.push
  cases second
  all_goals
    refine ⟨?_,?_,reachesJump ?enter,?call,?post⟩
    case enter =>
      first
      | change program.runBlock _ ⟨.l104280,a,m⟩ = _
        have wr : StoreOk Extracted.programImage m (context fr false+127) 1 0x104280 8 :=
          ParseSignature.storeOk_of_codeRange (off := 0) used
            (fun x hx => Common.fnCode_subset_programImage x (code_l104280 x hx)) (by decide +kernel)
        have addr : sp fr + 287 = context fr false+127 := by
          change sp fr + 287 = sp fr + 160 + 127
          bv_omega
        have src : a[12].get 64 = fr.rsp+351 := congrArg (Value.get 64) next
        have len64 : a[5].get 64 = 1 := congrArg (Value.get 64) len
        cfg_eval [rsp,addr,wr,src,len64]
      | change program.runBlock _ ⟨.l104848,a,m⟩ = _
        have wr : StoreOk Extracted.programImage m (context fr true+127) 1 0x104848 8 :=
          ParseSignature.storeOk_of_codeRange (off := 0) used
            (fun x hx => Common.fnCode_subset_programImage x (code_l104848 x hx)) (by decide +kernel)
        have addr : sp fr + 455 = context fr true+127 := by
          change sp fr + 455 = sp fr + 328 + 127
          bv_omega
        have src : a[3].get 64 = fr.rsp+351 := congrArg (Value.get 64) next
        have len64 : a[12].get 64 = 1 := congrArg (Value.get 64) len
        cfg_eval [rsp,addr,wr,src,len64]
      rfl
    case call =>
      first
      | change program.runBlock _ ⟨.l1042c0,_,cleared fr false m⟩ = _
        have wr : StoreOk Extracted.programImage (cleared fr false m) (context fr false+127) 1 0x1042cc 8 :=
          ParseSignature.storeOk_of_codeRange (off := 12) markedUsed
            (fun x hx => Common.fnCode_subset_programImage x (code_l1042c0 x hx)) (by decide +kernel)
        have ret : StoreOk Extracted.programImage (marked fr false m) (sp fr-8) 8 0x1042dd 6 :=
          ParseSignature.storeOk_of_codeRange (off := 29) push
            (fun x hx => Common.fnCode_subset_programImage x (code_l1042c0 x hx)) (by decide +kernel)
        have addr : sp fr + 287 = context fr false+127 := by
          change sp fr + 287 = sp fr + 160 + 127
          bv_omega
        have len64 : a[5].get 64 = 1 := congrArg (Value.get 64) len
        cfg_eval [rsp,dst,addr,wr,len64]
        refine Eq.trans (ite_eq_left ⟨got,ret,gotRead⟩) ?_
        rfl
      | change program.runBlock _ ⟨.l104872,_,cleared fr true m⟩ = _
        have wr : StoreOk Extracted.programImage (cleared fr true m) (context fr true+127) 1 0x104889 8 :=
          ParseSignature.storeOk_of_codeRange (off := 23) markedUsed
            (fun x hx => Common.fnCode_subset_programImage x (code_l104872 x hx)) (by decide +kernel)
        have ret : StoreOk Extracted.programImage (marked fr true m) (sp fr-8) 8 0x104897 6 :=
          ParseSignature.storeOk_of_codeRange (off := 37) push
            (fun x hx => Common.fnCode_subset_programImage x (code_l104872 x hx)) (by decide +kernel)
        have addr : sp fr + 455 = context fr true+127 := by
          change sp fr + 455 = sp fr + 328 + 127
          bv_omega
        have len64 : a[12].get 64 = 1 := congrArg (Value.get 64) len
        cfg_eval [rsp,dst,addr,wr,len64]
        refine Eq.trans (ite_eq_left ⟨got,ret,gotRead⟩) ?_
        rfl
    case post =>
      refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
      · exact regs.buf
      · exact regs.slice
      · intro h
        cases h <;> exact regs.hash rfl
      · exact regs.stop
      · rfl
      · rfl
      · rfl
      · rfl
      · rintro ⟨i, hi⟩ h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with h|h|h|h <;> cases h <;> rfl
      · intro eq
        first | rfl | cases eq
      · rintro i h
        have h' := h
        obtain ⟨i,hi⟩ := i
        simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h'
        rcases h' with h'|h'|h'|h'|h'|h' <;> cases h' <;> first | rfl | exact widths ⟨_,hi⟩ h

set_option maxHeartbeats 650000 in
theorem advance (second : Bool) : Advance second := by
  intro fr a m stack regs read stop widths
  have rsp : a[4].get 64 = sp fr := congrArg (Value.get 64) stack
  have zf : (cmpSpec (fr.rsi + 16) (fr.rsi + 48)).ZF = false := by
    rw [cmpSpec_ZF]
    have ne : fr.rsi + 16 ≠ fr.rsi + 48 := by bv_omega
    exact beq_eq_false_iff_ne.mpr ne
  have getCursor : (if second then a[14] else a[15]).get 64 = fr.rsi := by
    rw [regs.slice]
    exact BitVec.add_zero _
  cases second
  all_goals
    refine ⟨?_,reachesJump ?run,?_,?_,?_,?_⟩
    case run =>
      first
      | change program.runBlock _ ⟨.l1042e3,a,m⟩ = _
        change a[15].get 64 = fr.rsi at getCursor
        cfg_eval [rsp,read,stop,getCursor,zf]
      | change program.runBlock _ ⟨.l10489d,a,m⟩ = _
        change a[14].get 64 = fr.rsi at getCursor
        have stopReg : a[15].get 64 = fr.rsi + 48 := congrArg (Value.get 64) (regs.stop rfl)
        cfg_eval [getCursor,stopReg,zf]
      rfl
    · refine ⟨regs.buf,rfl,regs.hash,?_⟩
      intro h
      cases h <;> exact regs.stop rfl
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h|h|h|h <;> cases h <;> rfl
    · intro eq
      first | rfl | cases eq
    · rintro i h
      have h' := h
      obtain ⟨i,hi⟩ := i
      simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h'
      rcases h' with h'|h'|h'|h'|h'|h' <;> cases h' <;> first | rfl | exact widths ⟨_,hi⟩ h

theorem finish {fr : Activation} {state : State} {secret reduced : ByteArray}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr (.seeded secret reduced))
    (live : Live (tailAt second) fr a m state) (slots : Slots fr m)
    (regs : Pending second fr a) (ctx : Compressed second fr m state secret) :
    ∃ b n, Verify.Core.Reaches (tailAt second) a m (loopAt second) b n ∧
      Live (loopAt second) fr b n state ∧ Slots fr n ∧ Cursor second fr b 16 ∧
      UpdateV.HmacStateAt n (context fr second) state.key (taggedValue second state ++ secret) := by
  have access := tailAccess second env live
  have rsp : a[4] = ⟨64,sp fr⟩ := by cases second <;> exact live.atoms.1
  have df : a[22] = ⟨1,0⟩ := by cases second <;> exact live.atoms.2.1
  obtain ⟨b,c,start,called,setup⟩ := prepareCopy second rsp regs live.savedWidths access
  let off : Nat := if second then 392 else 224
  have destination : context fr second + 64 = sp fr + BitVec.ofNat 64 off := by
    cases second <;> simp only [context, off, Bool.false_eq_true, ite_false, ite_true,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
  have fits : off + 1 ≤ 664 := by cases second <;> decide
  have small : (tailRet second).toNat < 2^32 := by cases second <;> decide
  have low := env.limit
  have dep := env.depth
  have base := spNat env
  have src : (fr.rsp+351).toNat = fr.rsp.toNat+351 := by
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by change fr.rsp.toNat+351 < 2^64; omega)]
    rfl
  obtain ⟨d,path,back,kept,_⟩ := copyCall (len := 1) env access.written fits small called
    setup.rsp (setup.di.trans destination) setup.si setup.dx
    (congrArg (Value.get 1) ((setup.kept 22 (by decide)).trans df)) access.source
    (.inr (by cases second <;> simp only [off,Bool.false_eq_true,ite_false,ite_true] <;> omega))
  rw [← destination] at path
  let n := tailMemory fr second m (tailRet second)
  obtain ⟨frame,locality,slots',hmac⟩ := tailMemory_post second env live slots ctx (tailRet second)
  have c14 : d[14] = c[14] := kept 14 (by decide)
  have c15 : d[15] = c[15] := kept 15 (by decide)
  have cur : Cursor second fr d 0 := by
    refine ⟨(kept 13 (by decide)).trans setup.buf,?_,fun h => (kept 5 (by decide)).trans (setup.hash h),
      fun h => c15.trans (setup.stop h)⟩
    rw [c14,c15]
    exact setup.slice
  have wd (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) : d[i].width = 64 := by
    rw [kept i (by
      change i.val ∈ [3,5,12,13,14,15] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega)]
    exact setup.widths i hi
  obtain ⟨e,last,cursor',rest,r14,widths⟩ := advance second back cur (access.stopRead (tailRet second))
    slots'.stop wd
  have same (i : Fin Reg.count) (hi : i.val ∈ [4,22,39,50,51]) : e[i] = a[i] := by
    rw [rest i hi]
    rcases List.mem_cons.mp hi with h|h
    · obtain rfl : i = 4 := Fin.ext h
      exact back.trans rsp.symm
    · exact (kept i (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
        omega)).trans (setup.kept i h)
  exact ⟨e,n,start.trans (path.trans last),loopLive second env live slots' frame locality same
    (fun h => (r14 h).trans (c14.trans (setup.r14 h))) widths,slots',cursor',hmac⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock
