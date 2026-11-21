import K256.Proofs.Verify.Core.Scalars.Inverse.Adapter.Frame
import K256.Proofs.Verify.Core.Scalars.Inverse.Adapter.Guard
import K256.Proofs.Verify.Core.Scalars.Inverse.Adapter.Return

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Adapter

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

private theorem totalFrame {b k : Registers} {m : Ram} {x : BitVec 64}
    {o out : Output Value Ram Reg.count} (room : 728 ≤ x.toNat) (low : x.toNat + 233 ≤ 2^32)
    (inner : Generate.Generator.Affine.Invert.Core.CalleeResult k (staged b m x) (x-8)
      (x-8+16) 0x10a0f2 720 33 o)
    (finish : RamWriteFrame o.store out.store (returnWrites x)) :
    RamWriteFrame m out.store (writes x) := by
  have stage := stagedFrame b m (x := x) (by omega) (by omega)
  apply (((RamWriteFrame.refl m (writes x)).trans stage ?_).trans inner.frame ?_).trans finish ?_
  all_goals
    intro reg hr
    refine ⟨_,List.mem_cons_self,?_⟩
    simp only [stageWrites,returnWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    first | obtain rfl := hr | rcases hr with rfl|rfl
  all_goals dsimp only [writes]; bv_omega

theorem execute
    (inverse : ∀ {k m sp s}, Batch.Entry k m sp s → ∃ o,
      program.Exec (dialect Extracted.programImage) ⟨⟨.l109490,k,m⟩,[]⟩ o ∧ Batch.Result k m sp s o)
    {fr : Activation} {a b : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat} {m : Ram}
    (e : Core.Entry fr a p digest r s) (h : Reduced fr b m digest r s) :
    ∃ z n, Reaches .l10518b b m .l1051b1 z n ∧ Inverted fr z n digest r s := by
  let x := base fr
  have room := e.stackRoom
  have top := e.low
  have bot := e.low_toNat
  have xr : 728 ≤ x.toNat := by dsimp only [x,base]; bv_omega
  have xl : x.toNat + 584 ≤ 2^32 := by dsimp only [x,base]; bv_omega
  have baseSp : x+96 = localSp fr := by dsimp only [x,base,localSp]; bv_omega
  have area := e.stack.of_frame h.frame
  have win : Writable Extracted.programImage m (x-8) 104 := by
    apply area.sub <;> dsimp only [x,base] <;> bv_omega
  obtain ⟨c,wrap,cs,src,dst,keepC⟩ := callWrapper b m x ((congrArg (Value.get 64) h.sp).trans baseSp.symm) win
  obtain ⟨k,call,ks,ki,ko,kb,kc,kd,k8,keepK⟩ := callInverse c m x (congrArg (Value.get 64) cs)
    (congrArg (Value.get 64) dst) src (win.memStore _ _)
  have ent := enterBatch e (c := c) h ks ko ki kc kd k8
    ((keepK 22 (by decide)).trans ((keepC 22 (by decide)).trans h.df))
  obtain ⟨o,run,res,words,flag⟩ := inverse ent
  have ostack : o.values[4] = ⟨64,x⟩ := by simpa only [BitVec.sub_add_cancel] using res.rsp
  have odst : o.values[3] = ⟨64,x+104⟩ :=
    (res.kept 3 (by decide) (congrArg Value.width kb)).trans kb
  have stage := stagedFrame c m (x := x) (by omega) (by omega)
  have oarea := (area.of_frame stage).of_frame res.frame
  have owin : Writable Extracted.programImage o.store (x-9) 146 := by
    apply oarea.sub <;> dsimp only [x,base] <;> bv_omega
  have ret := (calleeSaved (x := x) res xr (by omega) 88 (by decide)).trans (stagedRet c m x)
  have atWords : base fr-8+16 = x+8 := by change x-8+16=x+8; bv_omega
  have atFlag : base fr-8+48 = x+40 := by change x-8+48=x+40; bv_omega
  rw [atWords] at words
  rw [atFlag] at flag
  obtain ⟨out,runret,tag,osp,kept,pops,owords,oflag,oframe⟩ :=
    returnInverse owin (by omega) (by omega) ostack odst words flag ret
  have wrapper := ParseSignature.exec_call (tail := []) call run (by rw [res.returned]; rfl) runret
  have back : Reaches .l10518b b m .l10519d out.values out.store := by
    refine .step (b := ⟨⟨.l10a0c0,c,pushed m x⟩,[Reduce.resume .l10519d 0x10519d]⟩) ?_ ?_
    · change program.step _ _ = _
      simp only [Program.step,wrap,Transfer.next]
    · exact ParseSignature.exec_reaches_resume wrapper _ [] (by rw [tag]; rfl)
  have before := totalFrame xr (by omega) res oframe
  have fspan : Writable Extracted.programImage out.store (localSp fr) 137 := by
    apply (area.of_frame before).sub <;> dsimp only [localSp] <;> bv_omega
  rw [baseSp] at osp
  have flagAddr : x+136 = localSp fr+40 := by rw [← baseSp,BitVec.add_assoc]; rfl
  have wordsAddr : x+104 = localSp fr+8 := by rw [← baseSp,BitVec.add_assoc]; rfl
  obtain ⟨z,passed,zregs⟩ := passGuard out.values out.store _ (congrArg (Value.get 64) osp)
    fspan (flagAddr ▸ oflag)
  let n := memStore out.store (localSp fr+136) (1 : BitVec 8)
  have delta : RamWriteFrame m n (writes x) := by
    apply before.memStore
    refine ⟨_,List.mem_cons_self,?_⟩
    rw [← baseSp]
    change (x-728).toNat ≤ (x+96+136).toNat ∧ _+1 ≤ (x-728).toNat+961 ∧ _
    bv_omega
  have regs (i : Fin Reg.count) (d : BitVec 64)
      (mem : (i.val,d) ∈ [(3,48),(12,56),(13,64),(14,72),(15,80)])
      (width : b[i].width = 64) : z[i] = b[i] := by
    have which : i.val ∈ [3,12,13,14,15] ∧ 48 ≤ d.toNat ∧ d.toNat ≤ 88 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at mem ⊢
      rcases mem with ⟨h,rfl⟩|⟨h,rfl⟩|⟨h,rfl⟩|⟨h,rfl⟩|⟨h,rfl⟩ <;> simp [h]
    have ofList := which.1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ofList
    rw [zregs i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega),pops i d mem,
      calleeSaved (x := x) res xr (by omega) d which.2,stagedSaved i d mem,
      keepC i (by simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false]; omega)]
    generalize b[i] = v at width ⊢
    obtain ⟨w,v⟩ := v
    change w = 64 at width
    subst w
    rfl
  have controls (i : Fin Reg.count) (mem : i.val ∈ [22,39,50,51]) : z[i] = b[i] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rw [zregs i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega),
      kept i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega),
      res.controls i (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using mem),
      keepK i (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega),
      keepC i (by simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false]; omega)]
  have bp := (keepK 5 (by decide)).trans ((keepC 5 (by decide)).trans h.rbp)
  have zbp := (zregs 5 (by decide)).trans ((kept 5 (by decide)).trans
    ((res.kept 5 (by decide) (congrArg Value.width bp)).trans bp))
  have savedSlot (d : BitVec 64) (small : d.toNat ≤ 40) :
      memLoad n (fr.rsp-d) 64 = memLoad m (fr.rsp-d) 64 := by
    apply delta.memLoad_eq
    refine ⟨by change _+8 ≤ 2^64; bv_omega,?_⟩
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (fr.rsp-584-728).toNat+961 ≤ (fr.rsp-d).toNat
    bv_omega
  have old := h.atoms
  simp only [Fn104f20.frameAt,Fn104f20.frameAtG6,Atom.All,Atom.Holds] at old
  obtain ⟨_,_,_,_,v12,v13,v14,v15,_,_,_,_,_,_,_,_,read,retMem,retLow,stk,oldroom,align,_⟩ := old
  have g3 := (regs 3 48 (by decide) (congrArg Value.width h.dst)).trans h.dst
  have saved : Saved fr z n :=
    ⟨(zregs 4 (by decide)).trans osp,g3,zbp,(controls 22 (by decide)).trans h.df,
     (controls 39 (by decide)).trans h.mxcsr,(controls 50 (by decide)).trans h.ftw,
     (controls 51 (by decide)).trans h.fcw,(savedSlot 40 (by decide)).trans h.rbx,
     (savedSlot 32 (by decide)).trans h.r12,(savedSlot 24 (by decide)).trans h.r13,
     (savedSlot 16 (by decide)).trans h.r14,(savedSlot 8 (by decide)).trans h.r15⟩
  have outside (d : BitVec 64) (hd : 137 ≤ d.toNat ∧ d.toNat ≤ 352) :
      Outside (writes x) (localSp fr+d) 32 := by
    rw [← baseSp]
    refine ⟨by bv_omega,?_⟩
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (x-728).toNat+961 ≤ (x+96+d).toNat
    bv_omega
  refine ⟨z,n,back.trans passed,⟨⟨saved,h.frame.trans delta (writesWithin e)⟩,?_,
    h.digestAt.of_frame delta (by decide) (outside 352 (by decide)),
    h.rAt.of_frame delta (by decide) (outside 256 (by decide)),?_⟩⟩
  · simp only [Fn104f20.frameAt,Fn104f20.frameAtG6,Atom.All,Atom.Holds]
    refine ⟨saved.sp,saved.df,g3,zbp,(regs 12 56 (by decide) (congrArg Value.width v12)).trans v12,
      (regs 13 64 (by decide) (congrArg Value.width v13)).trans v13,
      (regs 14 72 (by decide) (congrArg Value.width v14)).trans v14,
      (regs 15 80 (by decide) (congrArg Value.width v15)).trans v15,
      saved.mxcsr,saved.ftw,saved.fcw,saved.rbx,saved.r12,saved.r13,saved.r14,saved.r15,
      read.of_frame delta,?_,retLow,stk.of_frame delta,oldroom,align,trivial⟩
    have retEq := savedSlot 0 (by decide)
    rw [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] at retEq
    exact retEq.trans retMem
  · rw [wordsAddr] at owords
    intro i hi
    rw [← owords i hi]
    change memLoad (memStore _ _ _) _ _ = _
    apply memLoad_memStore_of_rangeApart
    intro j hj k hk
    change j < 1 at hj
    change k < 8 at hk
    dsimp only [wordAddr]
    change i < 4 at hi
    rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl|rfl|rfl|rfl <;> bv_omega

end K256.Proofs.Verify.Core.Scalars.Inverse.Adapter
