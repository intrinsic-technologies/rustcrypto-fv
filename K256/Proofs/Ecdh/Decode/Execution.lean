import K256.Proofs.Ecdh.Decode.Packing
import K256.Proofs.Ecdh.Decode.Frame
import K256.Proofs.Ecdh.Decode.Affine
import K256.Proofs.Ecdh.Decode.Finish
import K256.Proofs.Ecdh.LIR.Fn120f30.Frame

namespace K256.Proofs.Ecdh.Decode

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR Standards.SECG.ECC

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem execution (fr : Activation) (a : Values Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn120f30.frameAt .l120f30 fr))
    (src : Readable fr.original fr.rsi 33) (dst : Writable Extracted.programImage fr.original fr.rdi 89)
    (srcAbove : fr.rsp.toNat+8 ≤ fr.rsi.toNat) (dstAbove : fr.rsp.toNat+8 ≤ fr.rdi.toNat)
    (text : fr.rsp.toNat ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsp.toNat-1464)
    (image : ∀ x ∈ Extracted.programImage, fr.original[x.1]? = some x.2)
    {bytes : ByteArray} {q : Curve.Point}
    (input : ∀ i < 33, memByte fr.original (fr.rsi + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0)
    (h : K256.Spec.Secp256k1.groupPoint bytes = some q) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l120f30,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn120f30.doneAt fr) ∧
      out.values[0] = ⟨64,fr.rdi⟩ ∧ ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame fr.original out.store [fr.region,⟨fr.rdi.toNat,89⟩] ∧
      memLoad out.store (fr.rdi+88) 8 = 1 ∧ AffinePointAt out.store fr.rdi q := by
  simp only [Fn120f30.frameAt,Fn120f30.frameAtG5,Atom.All,Atom.Holds] at entry
  obtain ⟨rsp,df,_,_,rbx,rbp,rsi,rdi,r8,r9,r12,r13,r14,r15,mx,ft,fc,slot,ret,lo,wr,room,align,_⟩ := entry
  change fr.low.toNat+1464 ≤ fr.rsp.toNat at room
  let sp := workSP fr
  have sp264 : sp+264 = fr.rsp := by dsimp only [sp,workSP]; bv_omega
  have geom (k : BitVec 64) (hk : k.toNat ≤ 1464) :
      (fr.rsp-k).toNat = fr.rsp.toNat-k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have near (k : BitVec 64) (hk : (264+k).toNat ≤ 1464) :
      (sp-k).toNat = fr.rsp.toNat-(264+k).toNat := by
    change (fr.rsp-264-k).toNat = _
    rw [BitVec.sub_sub,geom _ hk]
  have n8 : (sp-8).toNat = fr.rsp.toNat-272 := near 8 (by decide)
  have n9 : (sp-9).toNat = fr.rsp.toNat-273 := near 9 (by decide)
  have below : Outside [Packing.window sp] fr.rsi 33 := by
    refine ⟨by have := src.low; omega,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change (sp-8).toNat+272 ≤ fr.rsi.toNat; omega)
  obtain ⟨b,m,path,bx,bsp,bs,bd,b14,b15,b15w,b8,b9,kept,encoded,bret,save3,save14,save15,pf⟩ :=
    Packing.packToAffine (sp := sp) [] (sp264 ▸ congrArg (Value.get 64) rsp) (congrArg (Value.get 64) rsi)
      (congrArg Value.width r8) (congrArg Value.width r9) (stackWindow wr) src below input h
      Common.fnCode_subset_programImage
  let child := affineActivation fr b m
  have childRegs : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,39,50,51] → b[i] = child.entryValue i.val := by
    rintro ⟨i,hi⟩ member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change b[3] = ⟨64, b[3].get 64⟩
      rw [bx]; rfl
    · change b[5] = ⟨64, b[5].get 64⟩
      have v := (kept 5 (by decide) (by decide)).trans rbp
      rw [v]; rfl
    · change b[12] = ⟨64, b[12].get 64⟩
      have v := (kept 12 (by decide) (by decide)).trans r12
      rw [v]; rfl
    · change b[13] = ⟨64, b[13].get 64⟩
      have v := (kept 13 (by decide) (by decide)).trans r13
      rw [v]; rfl
    · change b[14] = ⟨64, b[14].get 64⟩
      rw [b14]; rfl
    · change b[15] = ⟨64, b[15].get 64⟩
      exact b15w
    · change b[39] = ⟨32, b[39].get 32⟩
      have v := (kept 39 (by decide) (by decide)).trans mx
      rw [v]; rfl
    · change b[50] = ⟨16, b[50].get 16⟩
      have v := (kept 50 (by decide) (by decide)).trans ft
      rw [v]; rfl
    · change b[51] = ⟨16, b[51].get 16⟩
      have v := (kept 51 (by decide) (by decide)).trans fc
      rw [v]; rfl
  have bdf := (kept 22 (by decide) (by decide)).trans df
  have ce := affineEntry room align wr text image pf bsp bs bd b8 b9 bdf childRegs bret encoded
  obtain ⟨c,run,tag,crsp,keep,cf,flag,point,widths⟩ := Affine.execution ce h
  obtain ⟨frame,callerRet,saved⟩ := afterAffine room slot pf cf
  have ctr : memLoad c.store (sp+264) 64 = fr.ret := callerRet.trans ret
  have readable : Readable c.store (sp-9) 281 := by
    apply (readableWithSlot (n := 273) (slot := fr.rsp) ?_ slot (by omega)).of_frame frame
    exact wr.readable.of_offsets (x := fr.rsp) (c := 0-273)
      (by dsimp only [sp,workSP]; bv_omega) (addr_sub _ _) (by decide)
  have sw : Writable Extracted.programImage c.store (sp-9) 9 :=
    (wr.of_offsets (x := fr.rsp) (c := 0-273)
      (by dsimp only [sp,workSP]; bv_omega) (addr_sub _ _) (by decide)).of_frame frame
  have cbx : c.values[3].get 64 = fr.rdi := (congrArg (Value.get 64) ((keep 3 (by decide)).trans bx)).trans (congrArg (Value.get 64) rdi)
  have c14 : c.values[14].get 64 = sp+144 := congrArg (Value.get 64) ((keep 14 (by decide)).trans b14)
  have c15 : (c.values[15].get 64).setWidth 8 = 1 := by
    have ck : c.values[15] = b[15] := keep 15 (by decide)
    rw [ck]
    change _ = 1
    have eq : (b[15].get 64).setWidth 8 = b[15].get 8 := by
      rw [b15w]; rfl
    exact eq.trans b15
  have csp : c.values[4].get 64 = sp := by
    rw [crsp]; change sp-8+8 = sp; bv_omega
  have cdf : c.values[22].get 1 = 0 := congrArg (Value.get 1) ((keep 22 (by decide)).trans bdf)
  have validity : memLoad c.store (sp+232) 8 = 1 := by
    change memLoad c.store (sp+144+88) 8 = 1 at flag
    rwa [show sp+144+88 = sp+232 by bv_omega] at flag
  obtain ⟨out,last,ot,ax,osp,ob,or14,or15,ok,ow,tailFrame,status,value⟩ :=
    finish point widths csp cbx c14 c15 cdf validity readable sw (dst.of_frame frame)
      (.inr (by change (sp-9).toNat + 281 ≤ fr.rdi.toNat; omega)) (by rw [ctr]; exact lo)
  have restored (i : Fin Reg.count) (hi : i.val ∈ [5,12,13,22,39,50,51]) : out.values[i] = a[i] :=
    (ok i hi).trans ((keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
      (kept i.val (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega) i.isLt))
  have resume := ParseSignature.exec_reaches_resume run Packing.affineResume []
    (by rw [tag]; rfl)
  refine ⟨out,Program.Exec.of_sem (path.exec (resume.exec last.sem)),
    ot.trans (by rw [ctr]),?_,ax,ow,?_,status,value⟩
  · simp only [Fn120f30.doneAt,Atom.All,Atom.Holds]
    refine ⟨osp.trans ?_,(restored 22 (by decide)).trans df,ob.trans ?_,(restored 5 (by decide)).trans rbp,
      (restored 12 (by decide)).trans r12,(restored 13 (by decide)).trans r13,or14.trans ?_,or15.trans ?_,
      (restored 39 (by decide)).trans mx,(restored 50 (by decide)).trans ft,(restored 51 (by decide)).trans fc,trivial⟩
    · congr 1; dsimp only [sp,workSP]; bv_omega
    · rw [saved 240 (by decide) (by decide),save3]
      exact congrArg (fun v => (⟨64,v.get 64⟩ : Value)) rbx
    · rw [saved 248 (by decide) (by decide),save14]
      exact congrArg (fun v => (⟨64,v.get 64⟩ : Value)) r14
    · rw [saved 256 (by decide) (by decide),save15]
      exact congrArg (fun v => (⟨64,v.get 64⟩ : Value)) r15
  · apply ((RamWriteFrame.refl fr.original _).trans frame ?_).trans tailFrame
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · refine ⟨fr.region,List.mem_cons_self,?_,?_⟩
        · change fr.low.toNat ≤ (sp-9).toNat; omega
        · change (sp-9).toNat+9 ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat); omega
      · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨fr.region,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩

end K256.Proofs.Ecdh.Decode
