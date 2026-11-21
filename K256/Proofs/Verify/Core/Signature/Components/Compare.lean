import K256.Proofs.Verify.Core.Signature.Components.Choice
import K256.Proofs.Verify.Core.Signature.Components.Memory

namespace K256.Proofs.Verify.Core.Components

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Generate.Generator.Multiply (scalarWords)

def compareChild (fr : Activation) (b : Registers) (m : Ram) (ret : Word) : Activation :=
  {fr with
    original := m, rsp := localSp fr-8, low := localSp fr-24, ret := ret,
    rbx := fr.rdi, r12 := fr.rdx, r13 := fr.rcx, r14 := fr.rsi, r15 := fr.r8,
    rsi := localSp fr+8, rdi := localSp fr+136, rcx := b[1].get 64, rdx := b[2].get 64,
    r8 := b[8].get 64, r9 := b[9].get 64}

private theorem eqWord (v : Value) (h : v.width=64) : v=⟨64,v.get 64⟩ := by
  obtain ⟨w,x⟩ := v
  cases h
  rfl

set_option maxRecDepth 4096 in
theorem check (k : Component) {l : Label} {fr : Activation} {a b : Registers} {m n : Ram} {v : Nat}
    (args : Arguments fr b) (pos : 0 < v) (bound : v < 2^256)
    (room : 24 ≤ (localSp fr).toNat) (align : (localSp fr).toNat % 16 = 0)
    (win : Writable Extracted.programImage n (localSp fr-24) 192)
    (call : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ =
      .call ⟨.l10a280,b,stage n (localSp fr) k.compareTag (scalarWords v)⟩
        (resumeAt k.compareReturn k.compareTag)) :
    ∃ c t, Reaches l a m k.passed c t ∧ Fixed fr c ∧ c[4] = ⟨64,localSp fr⟩ ∧
      c[2].width=64 ∧ c[8].width=64 ∧ c[9].width=64 ∧
      RamWriteFrame n t (area (localSp fr) 192) := by
  let sp := localSp fr
  change 24 ≤ sp.toNat at room
  change sp.toNat % 16 = 0 at align
  change Writable _ n (sp-24) 192 at win
  let st := stage n sp k.compareTag (scalarWords v)
  let ch := compareChild fr b st k.compareTag
  have low := win.readable.low
  have tagLow : k.compareTag.toNat < 2^32 := by cases k <;> decide
  have staged := stageFrame n sp k.compareTag (scalarWords v) low
  have window := win.of_frame staged
  obtain ⟨words,zero,tag⟩ := stageWords n sp k.compareTag (scalarWords v)
  have cs : ch.rsp.toNat = sp.toNat-8 := BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact Nat.le_trans (by decide : 8≤24) room)
  have cl : ch.low.toNat = sp.toNat-24 := BitVec.toNat_sub_of_le (by exact room)
  have cw : Writable Extracted.programImage st (ch.rsp-16) 16 :=
    window.of_offsets (show ch.rsp-16 = sp+(0-24) by change sp-8-16=sp+(0-24); bv_omega)
      (addr_sub sp 24) (by decide)
  have pre : Atom.All Extracted.programImage b st (Generate.LIR.Fn10a280.frameInfo.entryAtoms ch) := by
    change Atom.All _ _ _ (Generate.LIR.Fn10a280.frameAt .l10a280 ch)
    simp only [Generate.LIR.Fn10a280.frameAt,Generate.LIR.Fn10a280.frameAtG0,Atom.All,Atom.Holds]
    exact ⟨args.sp,args.df,eqWord _ args.cx,eqWord _ args.dx,args.bx,args.bp,args.si,args.di,
      eqWord _ args.r8,eqWord _ args.r9,args.r12,args.r13,args.r14,args.r15,args.mx,args.ft,args.fc,
      window.readable.of_offsets (addr_sub sp 8) (addr_sub sp 24) (by decide),tag,tagLow,cw,
      by rw [cl,cs]; omega,by rw [cs]; change sp.toNat % 16 = 0 at align; omega,trivial⟩
  have apart {off : Nat} (h : off+32 ≤ 168) : Outside [ch.region] (sp+BitVec.ofNat 64 off) 32 := by
    have offVal : (BitVec.ofNat 64 off).toNat=off := Nat.mod_eq_of_lt (by omega)
    change (sp-24).toNat+192 ≤ _ at low
    have lo : (sp-24).toNat = sp.toNat-24 := cl
    have addr : (sp+BitVec.ofNat 64 off).toNat = sp.toNat+off := by
      rw [BitVec.toNat_add,offVal,Nat.mod_eq_of_lt (by omega)]
    refine ⟨by omega,fun t ht => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp ht
    change ch.low.toNat + (ch.rsp.toNat - ch.low.toNat) ≤ _
    rw [cs,cl,addr]
    omega
  obtain ⟨out,exec,returns,post,writes,widths,flag⟩ := compareNonzero (fr := ch) pre
    (window.readable.of_offsets (a := sp+136) rfl (addr_sub sp 24) (by decide))
    (window.readable.of_offsets (a := sp+8) rfl (addr_sub sp 24) (by decide))
    (apart (off := 136) (by decide)) (apart (off := 8) (by decide)) words zero pos bound
  have reached := reachesOfCall call exec returns
  change Atom.All _ _ _ (Generate.LIR.Fn10a280.doneAt ch) at post
  obtain ⟨stack,df,bx,bp,r12,r13,r14,r15,mx,ft,fc,_⟩ := post
  have rs : out.values[4].get 64 = sp := (congrArg (Value.get 64) stack).trans (BitVec.sub_add_cancel ..)
  have window' : Writable Extracted.programImage out.store (sp-24) 40 :=
    (window.of_frame writes).of_offsets (addr_sub sp 24) (addr_sub sp 24) (by decide)
  obtain ⟨c,t,resume,stack',keep,frame⟩ := choicePass k rs flag window'
  have total := staged.trans writes (by
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    refine ⟨_,List.mem_cons_self,Nat.le_refl _,?_⟩
    change ch.low.toNat + (ch.rsp.toNat-ch.low.toNat) ≤ ch.low.toNat+192
    rw [cl,cs]; omega)
  exact ⟨c,t,reached.trans resume,
    ⟨(keep 3 (by decide)).trans bx,(keep 5 (by decide)).trans bp,
     (keep 12 (by decide)).trans r12,(keep 13 (by decide)).trans r13,(keep 14 (by decide)).trans r14,
     (keep 15 (by decide)).trans r15,(keep 22 (by decide)).trans df,(keep 39 (by decide)).trans mx,
     (keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc⟩,stack',
    (congrArg Value.width (keep 2 (by decide))).trans (widths 2 (by decide)),
    (congrArg Value.width (keep 8 (by decide))).trans (widths 8 (by decide)),
    (congrArg Value.width (keep 9 (by decide))).trans (widths 9 (by decide)),
    total.trans frame (areaWithin _ (by decide))⟩

end K256.Proofs.Verify.Core.Components
