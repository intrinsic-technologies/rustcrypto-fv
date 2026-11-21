import K256.Proofs.Signing.UpdateV.Finalize.Callee
import K256.Proofs.Signing.UpdateV.Finalize.Caller
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

private theorem prepareFinalizeCall {fr : Activation} {a : Values Value Reg.count} {m : Ram} {key value : ByteArray}
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32)
    (frame : Frame .l104c21 fr a m) (ctx : a[14] = ⟨64, fr.rsp - 488 + 272⟩)
    (state : HmacStateAt m (fr.rsp - 488 + 272) key value) :
    ∃ b t, program.runBlock (dialect Extracted.programImage) ⟨.l104c21,a,m⟩ =
      .call ⟨.l107a50,b,t⟩ ⟨.l104c52,#v[],rfl,some ⟨64,0x104c52⟩⟩ ∧
      Finalize.Call b t (fr.rsp-488-8) (fr.rsp-488+272) (fr.rsp-488+72) ∧
      HmacStateAt t (fr.rsp-488+272) key value ∧
      memLoad t (fr.rsp-488-8) 64 = 0x104c52 ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m t (Finalize.callerWrites (fr.rsp-488)) := by
  let sp := fr.rsp-488
  let p := sp-8
  let src := sp+272
  let dst := sp+72
  have atoms := frame.atoms
  simp only [Fn104970.frameAt,Fn104970.frameAtG5,Atom.All,Atom.Holds] at atoms
  obtain ⟨rsp,df,_,_,_,_,_,_,_,_,_,_,_,_,stack,_⟩ := atoms
  have addr (k : BitVec 64) (hk : k.toNat ≤ 1200) : (fr.rsp-k).toNat = fr.rsp.toNat-k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have spNat : sp.toNat = fr.rsp.toNat-488 := addr 488 (by decide)
  have pNat : p.toNat = sp.toNat-8 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 8 ≤ sp.toNat; omega))
  have botNat := addr 1200 (by decide)
  simp only [BitVec.reduceToNat] at botNat
  have lowNat : fr.low.toNat = fr.rsp.toNat-1200 := by rw [low]; exact botNat
  have dstNat : dst.toNat = sp.toNat+72 := toNat_add_ofNat sp 72 (by omega)
  have srcNat : src.toNat = sp.toNat+272 := toNat_add_ofNat sp 272 (by omega)
  have childBot : p-704 = fr.rsp-1200 := by dsimp only [p,sp]; bv_omega
  obtain ⟨b,t,block,bsp,bsi,bdi,unchanged,ret,written⟩ :=
    Finalize.callBlock (sp := sp) (congrArg (Value.get 64) rsp)
      (by omega) (by omega) (stack.sub (by change (fr.rsp-1200).toNat ≤ p.toNat; omega)
      (by change p.toNat+112 ≤ (fr.rsp-1200).toNat+1200; omega))
  have stack' := stack.of_frame written
  have setupWithin : RegionsWithin (Finalize.callerWrites sp) [fr.region] := by
    intro r hr
    refine ⟨fr.region,List.mem_singleton_self _,?_⟩
    simp only [Finalize.callerWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · change fr.low.toNat ≤ p.toNat ∧ p.toNat+8 ≤ fr.low.toNat + (fr.rsp.toNat-fr.low.toNat)
      omega
    · change fr.low.toNat ≤ dst.toNat ∧ dst.toNat+32 ≤ fr.low.toNat + (fr.rsp.toNat-fr.low.toNat)
      omega
  have setup := frame.writes.trans written setupWithin
  have loaded : ∀ v ∈ Extracted.programImage, t[v.1]? = some v.2 := by
    intro v hv
    apply (setup.outside _ ⟨by have := v.1.isLt; omega, ?_⟩).trans (image v hv)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change v.1.toNat+1 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat-fr.low.toNat) ≤ v.1.toNat
    apply Classical.byContradiction
    intro no
    apply stack.notCode v hv (v.1.toNat - (fr.rsp-1200).toNat) (by omega)
    rw [← ofNat_toNat_add,Nat.add_sub_cancel' (by omega),BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have entry : Finalize.Call b t p src dst := by
    refine ⟨bsp,?_,bsi,(unchanged 22 (by decide)).trans df,?_,?_,by omega,by omega,?_,?_,?_,?_,by omega,by omega,loaded⟩
    · rw [bdi,ctx]; rfl
    · intro i hi
      apply (congrArg Value.width (unchanged i ?_)).trans (frame.widths rfl i hi)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with h|h|h <;> simp [h]
    · rw [childBot]; exact stack'.sub (Nat.le_refl _) (by omega)
    · exact stack'.readable.sub (by omega) (by omega)
    · change (memLoad t (sp-8) 64).toNat < 2^32
      rw [ret]; decide
    · exact stack'.readable.sub (by omega) (by omega)
    · exact stack'.sub (by omega) (by omega)
  have stable : Outside (Finalize.callerWrites sp) src 168 := by
    refine ⟨by omega,fun r hr => Or.inr ?_⟩
    simp only [Finalize.callerWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · change p.toNat+8 ≤ src.toNat; omega
    · change dst.toNat+32 ≤ src.toNat; omega
  exact ⟨b,t,block,entry,Finalize.hmacAfter written stable state,ret,unchanged,written⟩

theorem finalize {fr : Activation} {a : Values Value Reg.count} {m : Ram} {key value : ByteArray}
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32)
    (keySize : key.size = 32) (valSize : value.size = 32)
    (frame : Frame .l104c21 fr a m) (ctx : a[14] = ⟨64, fr.rsp - 488 + 272⟩)
    (state : HmacStateAt m (fr.rsp - 488 + 272) key value) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104c21, a, m⟩, []⟩ ⟨⟨.l104c52, b, t⟩, []⟩ ∧
      Frame .l104c52 fr b t ∧ ParseSignature.ArgumentWidths b ∧
      (⟨(fr.rsp - 488 + 72).toNat, 32⟩ : MemoryRegion).HasBytes t
        (HMAC.hmac SHA256.hashBytes 64 key value) := by
  let sp := fr.rsp-488
  let p := sp-8
  let src := sp+272
  let dst := sp+72
  have atoms := frame.atoms
  simp only [Fn104970.frameAt,Fn104970.frameAtG5,Atom.All,Atom.Holds] at atoms
  obtain ⟨rsp,df,mx,ft,fc,s3,s12,s13,s14,s15,s5,retRd,retVal,retLow,stack,room,align,_⟩ := atoms
  have addr (k : BitVec 64) (hk : k.toNat ≤ 1200) : (fr.rsp-k).toNat = fr.rsp.toNat-k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have spNat : sp.toNat = fr.rsp.toNat-488 := addr 488 (by decide)
  have pNat : p.toNat = sp.toNat-8 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 8 ≤ sp.toNat; omega))
  have botNat := addr 1200 (by decide)
  simp only [BitVec.reduceToNat] at botNat
  have lowNat : fr.low.toNat = fr.rsp.toNat-1200 := by rw [low]; exact botNat
  have dstNat : dst.toNat = sp.toNat+72 := toNat_add_ofNat sp 72 (by omega)
  obtain ⟨b,t,block,entry,prepared,ret,unchanged,written⟩ :=
    prepareFinalizeCall image low depth limit frame ctx state
  obtain ⟨out,run,tag,osp,regs,controls,calleeWrites,bytes,argWidths⟩ :=
    Finalize.execute (sp := p) (src := src) (dst := dst) entry prepared (by omega)
      (by rw [valSize]; decide)
  change memLoad t (sp-8) 64 = 0x104c52 at ret
  have sameTag : out.tag = some ⟨64,0x104c52⟩ := by rw [tag]; exact congrArg (fun w => some (Value.mk 64 w)) ret
  have resumed := Verify.Core.Lincomb.reachesCall block run sameTag
  have localFrame : RamWriteFrame m out.store [⟨(fr.rsp-1200).toNat,816⟩] := by
    refine ((RamWriteFrame.refl m _).trans written ?_).trans calleeWrites ?_
    · intro rr hr
      refine ⟨_,List.mem_singleton_self _,?_⟩
      simp only [Finalize.callerWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · change (fr.rsp-1200).toNat ≤ p.toNat ∧ p.toNat+8 ≤ (fr.rsp-1200).toNat+816
        omega
      · change (fr.rsp-1200).toNat ≤ dst.toNat ∧ dst.toNat+32 ≤ (fr.rsp-1200).toNat+816
        omega
    · intro rr hr
      refine ⟨_,List.mem_singleton_self _,?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · change (fr.rsp-1200).toNat ≤ p.toNat-704 ∧ p.toNat-704+704 ≤ (fr.rsp-1200).toNat+816
        omega
      · change (fr.rsp-1200).toNat ≤ dst.toNat ∧ dst.toNat+32 ≤ (fr.rsp-1200).toNat+816
        omega
  have total := frame.writes.trans localFrame (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    change fr.low.toNat ≤ (fr.rsp-1200).toNat ∧ (fr.rsp-1200).toNat+816 ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat)
    omega)
  have saved (k : BitVec 64) (hk : k.toNat ≤ 48) :
      memLoad out.store (fr.rsp-k) 64 = memLoad m (fr.rsp-k) 64 := by
    apply localFrame.memLoad_eq
    have pos := addr k (by omega)
    refine ⟨by omega,fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (fr.rsp-1200).toNat + 816 ≤ (fr.rsp-k).toNat
    omega
  have control (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : out.values[i] = a[i] := by
    apply (controls i hi).trans (unchanged i ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    rcases hi with h|h|h|h <;> simp [h]
  have r3 := regs 0
  change out.values[3] = ⟨64,b[3].get 64⟩ at r3
  have target : out.values[3] = ⟨64,fr.rdi+32⟩ := r3.trans
    (congrArg (fun v : Value => Value.mk 64 (v.get 64)) ((unchanged 3 (by decide)).trans frame.target))
  refine ⟨out.values,out.store,resumed,⟨?_,total,target,fun eq => by cases eq⟩,argWidths,bytes⟩
  simp only [Fn104970.frameAt,Fn104970.frameAtG5,Atom.All,Atom.Holds]
  have stackPtr : p+8=sp := by dsimp only [p]; bv_omega
  rw [stackPtr] at osp
  refine ⟨osp,(control 22 (by decide)).trans df,(control 39 (by decide)).trans mx,
    (control 50 (by decide)).trans ft,(control 51 (by decide)).trans fc,
    (saved 48 (by decide)).trans s3,(saved 40 (by decide)).trans s12,(saved 32 (by decide)).trans s13,
    (saved 24 (by decide)).trans s14,(saved 16 (by decide)).trans s15,(saved 8 (by decide)).trans s5,
    retRd.of_frame localFrame,?_,retLow,stack.of_frame localFrame,room,align,trivial⟩
  have retSame := saved 0 (by decide)
  rw [show fr.rsp - (0 : BitVec 64) = fr.rsp from BitVec.sub_zero _] at retSame
  exact retSame.trans retVal

end K256.Proofs.Signing.UpdateV
