import K256.Proofs.Signing.Nonce.Fill.Memory
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers)
open Initialize (State StateAt)

private theorem finish {fr : Activation} {a : Registers} {m : Ram} (env : Environment fr)
    (atoms : Atom.All Extracted.programImage a m (Fn100a40.frameAt .l100e0a fr))
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l100e0a,a,m⟩,[]⟩ out ∧
      out.store = m ∧ out.tag = some ⟨64,fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn100a40.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values := by
  simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨stackPointer,df,_,mx,ft,fc,_,_,_,bx,r12,r13,r14,r15,bp,retRead,ret,retLow,area,_⟩ := atoms
  have rsp : a[4].get 64 = fr.rsp - 232 := congrArg (Value.get 64) stackPointer
  have floor : (fr.rsp - 2160).toNat = fr.rsp.toNat - 2160 := env.subNat 2160 (by decide)
  have pop (k : BitVec 64) (hk : 8 ≤ k.toNat ∧ k.toNat ≤ 48) :
      LoadOk m (fr.rsp - k) 8 := by
    apply LoadOk.of_region area.readable <;> rw [env.subNat k (by omega),floor] <;>
      have := env.depth <;> omega
  have p48 := pop 48 (by decide)
  have p40 := pop 40 (by decide)
  have p32 := pop 32 (by decide)
  have p24 := pop 24 (by decide)
  have p16 := pop 16 (by decide)
  have p8 := pop 8 (by decide)
  have readRet : LoadOk m fr.rsp 8 := ⟨retRead.low,retRead.present⟩
  refine ⟨?_, .done ?run, ?mem, ?tag, ?atoms, ?widths⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [rsp, Lift.reduceAddOffset, BitVec.sub_add_cancel, p48,p40,p32,p24,p16,p8,
      bx,r12,r13,r14,r15,bp,readRet,ret,retLow,and_self,↓reduceIte]
    rfl
  case mem => rfl
  case tag => rfl
  case atoms => exact ⟨rfl,df,rfl,rfl,rfl,rfl,rfl,rfl,mx,ft,fc,trivial⟩
  case widths =>
    rintro ⟨i,hi⟩ member
    have width := widths ⟨i,hi⟩ member
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact width

private def encoderFrame (fr : Activation) (a : Registers) (m : Ram) : Activation :=
  { fr with
    original := memStore m (fr.rsp - 240) (0x100e0a#64)
    rsp := fr.rsp - 240
    low := fr.rsp - 448
    ret := 0x100e0a
    rbx := a[3].get 64
    rbp := a[5].get 64
    r12 := a[12].get 64
    r13 := fr.rdx
    r14 := a[14].get 64
    r15 := fr.rsp + 600
    rdi := sp fr + 72
    rsi := fr.rsp + 600
    rdx := fr.rsi
    rcx := fr.rdx
    r8 := a[8].get 64
    r9 := a[9].get 64 }

set_option maxRecDepth 2048 in
private theorem dispatch {fr : Activation} {state : State} {a : Registers} {m : Ram}
    (env : Environment fr) (tested : Tested fr state a m) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l100df5,a,m⟩ =
      .call ⟨.l100000,b,(encoderFrame fr a m).original⟩
        (Verify.Core.Lincomb.callResume .l100e0a 0x100e0a) ∧
      Atom.All Extracted.programImage b (encoderFrame fr a m).original
        (Fn100000.frameAt .l100000 (encoderFrame fr a m)) ∧
      RamWriteFrame m (encoderFrame fr a m).original [⟨(encoderFrame fr a m).rsp.toNat,8⟩] := by
  have atoms := tested.atoms
  simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨stackPointer,df,mx,ft,fc,dst,_,_,_,_,_,_,_,_,_,_,_,area,_,align,
    rd0,v0,rd1,v1,_,_,rd2,v2,apart,_⟩ := atoms
  have rsp : a[4].get 64 = fr.rsp - 232 := congrArg (Value.get 64) stackPointer
  have r13 : a[13].get 64 = fr.rdx := (congrArg (Value.get 64) tested.r13).trans env.size.symm
  have r15 : a[15].get 64 = fr.rsp + 600 := congrArg (Value.get 64) tested.r15
  let child := encoderFrame fr a m
  have areaNat : (fr.rsp - 2160).toNat = fr.rsp.toNat - 2160 := env.subNat 2160 (by decide)
  have pushNat : child.rsp.toNat = fr.rsp.toNat - 240 := env.subNat 240 (by decide)
  have lowNat : child.low.toNat = fr.rsp.toNat - 448 := env.subNat 448 (by decide)
  have depth := env.depth
  have lim := env.limit
  have pushSlot : Writable Extracted.programImage m (fr.rsp - 240) 8 := by
    rw [← (show sp fr - 8 = fr.rsp - 240 by unfold sp; bv_omega)]
    exact tested.toFrame.pushSlot env
  have loadDst : LoadOk m (fr.rsp - 192) 8 := by
    have read := (tested.toFrame.slot env 40 8 (by decide)).readable
    rw [show sp fr + 40 = fr.rsp - 192 by unfold sp; bv_omega] at read
    exact ⟨read.low,read.present⟩
  have pushFrame : RamWriteFrame m child.original [⟨child.rsp.toNat,8⟩] :=
    (RamWriteFrame.refl _ _).memStore (0x100e0a#64)
      ⟨_,List.mem_singleton_self _,Nat.le_refl _,Nat.le_refl _,by change child.rsp.toNat + 8 ≤ 2^64; rw [pushNat]; omega⟩
  have cut : child.rsp - 208 = child.low := by
    change fr.rsp - 240 - 208 = fr.rsp - 448
    bv_omega
  have slot (p : BitVec 64) (lo : 0x203dd0 ≤ p.toNat) (hi : p.toNat + 8 ≤ 0x203e28) :
      memLoad child.original p 64 = memLoad m p 64 := by
    apply pushFrame.memLoad_eq
    refine ⟨by omega,fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change p.toNat + 8 ≤ child.rsp.toNat ∨ child.rsp.toNat + 8 ≤ p.toNat
    change 0x204698 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at apart
    rw [pushNat]
    omega
  have widthVal (i : Fin Reg.count) (hi : i.val ∈ Activation.entryNumbers) :
      a[i] = ⟨64,a[i].get 64⟩ := by
    have width := tested.widths i hi
    generalize a[i] = v at width ⊢
    cases v
    cases width
    rfl
  refine ⟨?_, ?run, ?entry, pushFrame⟩
  case run =>
    cfg_eval
    simp only [rsp,r13,r15,reduceAddOffset,dst,loadDst,↓reduceIte,
      show fr.rsp - 232 - 8 = fr.rsp - 240 by bv_omega]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l100df5)
    rfl
  case entry =>
    change Atom.All _ _ child.original (Fn100000.frameAt .l100000 child)
    simp only [Fn100000.frameAt, Fn100000.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨rfl,df,rfl,rfl,widthVal 3 (by decide),widthVal 5 (by decide),rfl,?_,widthVal 8 (by decide),widthVal 9 (by decide),
      widthVal 12 (by decide),?_,widthVal 14 (by decide),tested.r15,mx,ft,fc,
      (pushSlot.of_frame pushFrame).readable,memLoad_memStore_same _ _ _ (by decide) (by decide),
      by change (0x100e0a#64).toNat < 2^32; decide,?_,?_,?_,rd0.of_frame pushFrame,(slot _ (by decide) (by decide)).trans v0,
      rd1.of_frame pushFrame,(slot _ (by decide) (by decide)).trans v1,
      rd2.of_frame pushFrame,(slot _ (by decide) (by decide)).trans v2,?_⟩
    · apply congrArg (Value.mk 64)
      change fr.rsp - 160 = fr.rsp - 232 + 72
      bv_omega
    · exact tested.r13.trans (congrArg (Value.mk 64) env.size.symm)
    · rw [cut]
      exact (area.of_frame pushFrame).sub (by rw [areaNat,lowNat]; omega)
        (by rw [areaNat,lowNat]; omega)
    · rw [lowNat,pushNat]; omega
    · rw [pushNat]
      change fr.rsp.toNat % 16 = 8 at align
      omega
    · refine ⟨?_,trivial⟩
      change 0x203ef8 ≤ child.rsp.toNat ∨ child.rsp.toNat ≤ 0x203dd0
      change 0x204698 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at apart
      rw [pushNat]; omega

private def encoderWrites (fr : Activation) : List MemoryRegion :=
  [⟨(fr.rsp - 448).toNat,216⟩, ⟨fr.rsi.toNat,32⟩]

private theorem frameAfterEncode {fr child : Activation} {m n : Ram}
    (env : Environment fr) {w : Ram}
    (push : RamWriteFrame m w [⟨child.rsp.toNat,8⟩])
    (writes : RamWriteFrame w n [child.region,⟨fr.rsi.toNat,32⟩])
    (childSp : child.rsp = fr.rsp - 240) (childLow : child.low = fr.rsp - 448) :
    RamWriteFrame m n (encoderWrites fr) := by
  have lo : child.low.toNat = fr.rsp.toNat - 448 := by
    rw [childLow]
    exact env.subNat 448 (by decide)
  have rsp : child.rsp.toNat = fr.rsp.toNat - 240 := by
    rw [childSp]
    exact env.subNat 240 (by decide)
  have depth := env.depth
  refine ((RamWriteFrame.refl m (encoderWrites fr)).trans push ?_).trans writes ?_
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_cons_self,?_,?_⟩
    · change (fr.rsp - 448).toNat ≤ child.rsp.toNat
      rw [← childLow,lo,rsp]
      omega
    · change child.rsp.toNat + 8 ≤ (fr.rsp - 448).toNat + 216
      rw [← childLow,lo,rsp]
      omega
  · intro r hr
    rcases List.mem_cons.mp hr with eq | mem
    · subst r
      refine ⟨_,List.mem_cons_self,?_,?_⟩
      · change (fr.rsp - 448).toNat ≤ child.low.toNat
        rw [childLow]
        exact Nat.le_refl _
      · change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ (fr.rsp - 448).toNat + 216
        rw [← childLow,lo,rsp]
        omega
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩

private theorem encoderOutside {fr : Activation} (env : Environment fr) {p : BitVec 64}
    {n : Nat} (lo : fr.rsp.toNat - 232 ≤ p.toNat) (hi : p.toNat + n ≤ 2^64)
    (away : p.toNat + n ≤ fr.rsp.toNat + 392 ∨ fr.rsp.toNat + 424 ≤ p.toNat) :
    Outside (encoderWrites fr) p n := by
  have low : (fr.rsp - 448).toNat = fr.rsp.toNat - 448 := env.subNat 448 (by decide)
  have dst : fr.rsi.toNat = fr.rsp.toNat + 392 := env.dst ▸ env.addNat 392 (by decide)
  have depth := env.depth
  refine ⟨hi, fun r hr => ?_⟩
  rcases List.mem_cons.mp hr with eq | mem
  · subst r
    right
    change (fr.rsp - 448).toNat + 216 ≤ _
    rw [low]
    omega
  · obtain rfl := List.mem_singleton.mp mem
    change _ ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 32 ≤ _
    rw [dst]
    exact away

private theorem resumeAtoms {fr : Activation} {a b : Registers} {m n : Ram}
    (env : Environment fr) (frame : Frame fr a m)
    (writes : RamWriteFrame m n (encoderWrites fr))
    (done_ : Atom.All Extracted.programImage b n (Fn100000.doneAt (encoderFrame fr a m))) :
    Atom.All Extracted.programImage b n (Fn100a40.frameAt .l100e0a fr) := by
  have atoms := frame.atoms
  simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at atoms ⊢
  obtain ⟨_,_,_,_,_,dst,len,gen,bx,r12,r13,r14,r15,bp,readRet,ret,retLow,area,space,align,_⟩ := atoms
  simp only [Fn100000.doneAt, Atom.All, Atom.Holds] at done_
  obtain ⟨rsp,df,_,_,_,r13',_,_,mx,ft,fc,_⟩ := done_
  have depth := env.depth
  have lim := env.limit
  have save (k : BitVec 64) (h : k.toNat ≤ 192) :
      memLoad n (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply writes.memLoad_eq
    apply encoderOutside env <;> rw [env.subNat k (by omega)] <;> omega
  have keepRet := save 0 (by decide)
  rw [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] at keepRet
  have stackPointer : b[4] = ⟨64,fr.rsp - 232⟩ := rsp.trans (congrArg (Value.mk 64) (by
    change fr.rsp - 240 + 8 = fr.rsp - 232
    bv_omega))
  exact ⟨stackPointer,df,r13',mx,ft,fc,(save 192 (by decide)).trans dst,(save 184 (by decide)).trans len,
    (save 88 (by decide)).trans gen,(save 48 (by decide)).trans bx,(save 40 (by decide)).trans r12,
    (save 32 (by decide)).trans r13,(save 24 (by decide)).trans r14,(save 16 (by decide)).trans r15,
    (save 8 (by decide)).trans bp,readRet.of_frame writes,keepRet.trans ret,retLow,area.of_frame writes,
    space,align,trivial⟩

theorem returnPath {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (tested : Tested fr state a m) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l100df5,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn100a40.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ RamWriteFrame fr.original out.store (regions fr) ∧
      StateAt out.store (fr.rdi+8) (retry state) ∧
      (⟨fr.rsi.toNat,32⟩ : MemoryRegion).HasBytes out.store (Encoding.natToOctets 32 (candidate state).1) := by
  obtain ⟨b,call,entry,pushed⟩ := dispatch env tested
  let child := encoderFrame fr a m
  have depth := env.depth
  have limit := env.limit
  have pushNat : child.rsp.toNat = fr.rsp.toNat - 240 := env.subNat 240 (by decide)
  have srcNat : child.rdi.toNat = fr.rsp.toNat - 232 + 72 := env.slotNat 72 (by decide)
  have dstNat : fr.rsi.toNat = fr.rsp.toNat + 392 := env.dst ▸ env.addNat 392 (by decide)
  have orderNat : child.rsi.toNat = fr.rsp.toNat + 600 := env.addNat 600 (by decide)
  have cut : child.low = child.rsp - 208 := by
    change fr.rsp - 448 = fr.rsp - 240 - 208
    bv_omega
  have abovePush (p : BitVec 64) (lo : fr.rsp.toNat - 232 ≤ p.toNat) (hi : p.toNat + 32 ≤ 2^64) :
      Outside [⟨child.rsp.toNat,8⟩] p 32 := by
    refine ⟨hi, fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change child.rsp.toNat + 8 ≤ _
    rw [pushNat]
    omega
  have srcWords := tested.words.of_frame pushed (by decide)
    (abovePush child.rdi (by rw [srcNat]; omega) (by rw [srcNat]; omega))
  have orderWords := (tested.toFrame.orderWords env).of_frame pushed (by decide)
    (abovePush child.rsi (by rw [orderNat]; omega) (by rw [orderNat]; omega))
  have srcRead := (tested.toFrame.slot env 72 32 (by decide)).readable.of_frame pushed
  have upper := (env.window.of_frame tested.writes).of_frame pushed
  have dstWrite : Writable Extracted.programImage child.original child.rdx 32 :=
    upper.sub (by change fr.rsp.toNat ≤ fr.rsi.toNat; rw [dstNat]; omega)
      (by change fr.rsi.toNat + 32 ≤ fr.rsp.toNat + 768; rw [dstNat]; omega)
  have orderRead : Readable child.original child.rsi 32 :=
    upper.readable.sub (by change fr.rsp.toNat ≤ child.rsi.toNat; rw [orderNat]; omega)
      (by change child.rsi.toNat + 32 ≤ fr.rsp.toNat + 768; rw [orderNat]; omega)
  obtain ⟨mid,exec,tag,done_,widths,cWritten,encoded⟩ := Initialize.encodeWords (fr := child) entry
    (by rw [pushNat]; omega) cut (by rw [pushNat,srcNat]; omega)
    (by change child.rdi.toNat + 32 ≤ fr.rsi.toNat; rw [srcNat,dstNat]; omega)
    (by rw [pushNat,orderNat]; omega) env.size srcRead orderRead dstWrite srcWords orderWords
  have reach := Verify.Core.Lincomb.reachesCall call exec tag
  have written := frameAfterEncode env pushed cWritten rfl rfl
  have resumed := resumeAtoms env tested.toFrame written done_
  obtain ⟨out,finishExec,store,ret,doneOut,widthsOut⟩ := finish env resumed widths
  have total := tested.writes.trans written (by
    intro r hr
    rcases List.mem_cons.mp hr with eq | mem
    · subst r
      refine ⟨fr.region,List.mem_cons_self,?_⟩
      simp only [Activation.region,env.low,
        show (fr.rsp - 2160).toNat = fr.rsp.toNat - 2160 from env.subNat 2160 (by decide),
        show (fr.rsp - 448).toNat = fr.rsp.toNat - 448 from env.subNat 448 (by decide)]
      omega
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩)
  have stAddr : (fr.rdi + 8).toNat = fr.rsp.toNat + 704 := by
    rw [env.gen,show fr.rsp + 696 + 8 = fr.rsp + 704 by bv_omega]
    exact env.addNat 704 (by decide)
  have stateAt := stateAfter written (encoderOutside env
    (by rw [stAddr]; omega) (by rw [stAddr]; omega) (Or.inr (by rw [stAddr]; omega))) tested.stateAt
  exact ⟨out,Program.Exec.of_sem (reach.exec finishExec.sem),ret,doneOut,widthsOut,
    store.symm ▸ total,store.symm ▸ stateAt,store.symm ▸ encoded⟩

end K256.Proofs.Signing.Nonce.Fill
