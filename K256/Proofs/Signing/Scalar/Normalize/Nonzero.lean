import K256.Proofs.Signing.Scalar.Normalize.State
import K256.Proofs.Verify.LIR.Fn104c90
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Scalar.Normalize

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Verify.LIR Generate.Generator.Multiply Standards.SECG.DomainParameters.Secp256k1

private abbrev Limbs := Vector (BitVec 64) 4

private def stage (fr : Activation) (w : Limbs) : Ram :=
  let sp := fr.rsp
  let m := memStore fr.original (sp - 8) fr.r15
  let m := memStore m (sp - 16) fr.r14
  let m := memStore m (sp - 24) fr.r12
  let m := memStore m (sp - 32) fr.rbx
  let m := memStore m (sp - 72) w[3]
  let m := memStore m (sp - 80) w[2]
  let m := memStore m (sp - 88) w[1]
  let m := memStore m (sp - 96) w[0]
  let m := memStore m (sp - 104) (0 : BitVec 64)
  let m := memStore m (sp - 112) (0 : BitVec 64)
  let m := memStore m (sp - 120) (0 : BitVec 64)
  let m := memStore m (sp - 128) (0 : BitVec 64)
  memStore m (sp - 144) (0x104cf8 : BitVec 64)

local macro "stack_bounds" : tactic => `(tactic|
  (simp only [InRegion, Activation.region, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat,
    Nat.reducePow, Nat.reduceDiv] at *
   omega))

private theorem stageFrame {fr : Activation} {r s : Nat} (input : Inputs fr r s) (w : Limbs) :
    RamWriteFrame fr.original (stage fr w) [fr.region] := by
  have lo := input.low
  have room := input.room
  have high := input.high
  unfold stage
  repeat' refine RamWriteFrame.memStore ?_ _ ⟨_, List.mem_singleton_self _, ?_⟩
  all_goals first | exact .refl _ _ | (rw [Activation.region,lo]; stack_bounds)

private theorem stageWords (fr : Activation) (w : Limbs) :
    WordsAt (stage fr w) (fr.rsp-96) 64 w ∧ WordsAt (stage fr w) (fr.rsp-128) 64 (Vector.replicate 4 0) := by
  constructor <;> intro i hi
  all_goals
    obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
    all_goals
      simp only [stage, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat]
      segment_words []
      try rfl

private def compareFrame (fr : Activation) (w : Limbs) : Activation :=
  { fr with
    original := stage fr w, rsp := fr.rsp - 144, low := fr.rsp - 160,
    ret := 0x104cf8, rcx := w[1], rbx := fr.rdi, r14 := fr.rsi, rdi := fr.rsp - 96, rsi := fr.rsp - 128 }

private theorem carryLoad {m : Ram} {a dst : BitVec 64} {len n : Nat} {x : BitVec n}
    (h : LoadOk m a len) : LoadOk (memStore m dst x) a len :=
  ⟨h.low, fun i hi => memStore_isSome m dst x _ (h.present i hi)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem enterCompare {fr : Activation} {a : Verify.Core.Registers} {r s : Nat}
    (input : Inputs fr r s)
    (entry : Atom.All Extracted.programImage a fr.original (Fn104c90.frameAt .l104c90 fr)) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l104c90,a,fr.original⟩ =
      .call ⟨.l10a280,b,stage fr (scalarWords s)⟩ (Verify.resumeAt .l104cf8 0x104cf8) ∧
      Atom.All Extracted.programImage b (stage fr (scalarWords s))
        (Generate.LIR.Fn10a280.frameInfo.entryAtoms (compareFrame fr (scalarWords s))) := by
  simp only [Fn104c90.frameAt, Fn104c90.frameAtG5, Atom.All, Atom.Holds] at entry
  obtain ⟨rsp,df,rcx,rdx,rbx,rbp,rsi,rdi,r8,r9,r12,r13,r14,r15,mx,ft,fc,_,_,_,stack,_,align,_⟩ := entry
  have gsp : a[4].get 64 = fr.rsp := congrArg (Value.get 64) rsp
  have g3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) rbx
  have g6 : a[6].get 64 = fr.rsp + 200 := (congrArg (Value.get 64) rsi).trans input.src
  have g7 : a[7].get 64 = fr.rdi := congrArg (Value.get 64) rdi
  have g12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have g14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have g15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have read := input.read
  rw [input.src] at read
  have words := input.sWords
  rw [input.src, show fr.rsp+200+32 = fr.rsp+232 by bv_omega] at words
  obtain ⟨s0,s1,s2,s3⟩ := Verify.Core.Components.wordsToLoads (off := 232) words
  change memLoad fr.original (fr.rsp+232) 64 = _ at s0
  change memLoad fr.original (fr.rsp+240) 64 = _ at s1
  change memLoad fr.original (fr.rsp+248) 64 = _ at s2
  change memLoad fr.original (fr.rsp+256) 64 = _ at s3
  refine ⟨?b, ?run, ?pre⟩
  case run =>
    unfold stage
    have rd (o : BitVec 64) (fit : (o-200).toNat + 8 ≤ 64) : LoadOk fr.original (fr.rsp+o) 8 :=
      LoadOk.of_offsets read rfl (show fr.rsp+200 = fr.rsp+200 from rfl) fit
    have rd0 := rd 232 (by decide)
    have rd1 := rd 240 (by decide)
    have rd2 := rd 248 (by decide)
    have rd3 := rd 256 (by decide)
    have guard {m : Ram} {addr pc : BitVec 64} {len : Nat}
        (w : Writable Extracted.programImage m addr 8)
        (fit : (pc-0x104c90).toNat + len ≤ bytes_l104c90.length) :
        StoreOk Extracted.programImage m addr 8 pc len := by
      have h := ParseSignature.storeOk_of_codeRange w
        (fun x hx => Common.fnCode_subset_programImage x (code_l104c90 x hx)) fit
      rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show 0x104c90 + (pc-0x104c90) = pc by bv_omega] at h
    cfg_eval [gsp,g3,g6,g7,g12,g14,g15]
    segment_words [s0,s1,s2,s3]
    iterate 17 (refine Eq.trans (ite_eq_left ?_) ?_; rotate_left)
    rfl
    all_goals first
      | (apply guard
         · repeat' apply Writable.memStore
           exact stack.of_offsets (addr_sub _ _) (addr_sub _ 464) (by decide)
         · decide +kernel)
      | (repeat' apply carryLoad
         assumption)
  case pre =>
    change Atom.All _ _ _ (Generate.LIR.Fn10a280.frameAt .l10a280 (compareFrame fr (scalarWords s)))
    simp only [Generate.LIR.Fn10a280.frameAt, Generate.LIR.Fn10a280.frameAtG0, compareFrame, Atom.All, Atom.Holds]
    have staged := stack.of_frame (stageFrame input (scalarWords s))
    have room := input.room
    refine ⟨rfl,df,rfl,rdx,rfl,rbp,rfl,rfl,r8,r9,r12,r13,?_,r15,mx,ft,fc,?_,?_,by decide,?_,?_,?_,trivial⟩
    · rw [input.src]; rfl
    · exact staged.readable.of_offsets (addr_sub _ 144) (addr_sub _ 464) (by decide)
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [show fr.rsp-144-16 = fr.rsp-160 by bv_omega]
      exact staged.of_offsets (addr_sub _ 160) (addr_sub _ 464) (by decide)
    · stack_bounds
    · stack_bounds

private abbrev kept := [3,5,13,14,22,39,50,51]

private def scratch (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp-160).toNat,40⟩]

private theorem scratchInside {sp addr off : BitVec 64} {len : Nat}
    (room : 160 ≤ sp.toNat) (high : sp.toNat < 2^32)
    (addrEq : addr = sp - off) (before : off.toNat ≤ 160) (after : 120 + len ≤ off.toNat) :
    InRegions (scratch sp) addr len := by
  refine ⟨_,List.mem_singleton_self _,?_⟩
  change (sp-160).toNat ≤ addr.toNat ∧ addr.toNat + len ≤ (sp-160).toNat + 40 ∧ _
  subst addr
  rw [BitVec.toNat_sub_of_le (show (160 : BitVec 64) ≤ sp from BitVec.le_def.mpr room),
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega : off.toNat ≤ sp.toNat))]
  simp only [BitVec.reduceToNat]
  omega

private theorem choiceCall {a : Verify.Core.Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp-136) (zero : a[0].get 8 = 0)
    (win : Writable Extracted.programImage m (sp-160) 40) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l104cf8,a,m⟩ =
        .call ⟨.l127d50,b,memStore m (sp-144) (0x104d04 : BitVec 64)⟩ (Verify.resumeAt .l104d04 0x104d04) ∧
      b[4].get 64 = sp-144 ∧ b[7].get 64 = 1 ∧
      (∀ i : Fin Reg.count, i.val ∈ kept → b[i] = a[i]) := by
  have low : (a[0].get 64).setWidth 8 = a[0].get 8 := BitVec.setWidth_setWidth_of_le _ (by decide)
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l104cf8
    · rfl
  case post =>
    refine ⟨rfl,?_,?_⟩
    · change ((mergeGPR 8 _ _).setWidth 8).setWidth 64 = 1
      simp only [setWidth_mergeGPR8,low,zero]
      rfl
    · intro ⟨i,_⟩ mem
      simp only [kept,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem choiceJump {a : Verify.Core.Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp-136) (one : a[0].get 64 = 1)
    (win : Writable Extracted.programImage m (sp-160) 40) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l104d04,a,m⟩ =
        .jump ⟨.l104d10,b,memStore m (sp-128) (1 : BitVec 8)⟩ ∧
      b[4] = a[4] ∧ ∀ i : Fin Reg.count, i.val ∈ kept → b[i] = a[i] := by
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,one]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l104d04
    · rfl
  case post =>
    refine ⟨rfl,?_⟩
    intro ⟨i,_⟩ mem
    simp only [kept,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem passChoice {a : Verify.Core.Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp-136) (zero : a[0].get 8 = 0)
    (win : Writable Extracted.programImage m (sp-160) 40)
    (room : 160 ≤ sp.toNat) (high : sp.toNat < 2^32) :
    ∃ b n, Verify.Core.Reaches .l104cf8 a m .l104d10 b n ∧ b[4] = ⟨64,sp-136⟩ ∧
      RamWriteFrame m n (scratch sp) ∧ (∀ i : Fin Reg.count, i.val ∈ kept → b[i] = a[i]) := by
  obtain ⟨b,call,bs,b1,bk⟩ := choiceCall rsp zero win
  have callPush : sp-136-8 = sp-144 := by bv_omega
  rw [← callPush] at call bs
  have work : Writable Extracted.programImage m (sp-136-8-1) 1 :=
    win.of_offsets (show _ = sp+(0-145) by bv_omega) (addr_sub sp 160) (by decide)
  have ret := win.readable.of_offsets (n := 8) (addr_sub sp 144) (addr_sub sp 160) (by decide)
  rw [← callPush] at ret
  obtain ⟨c,n,reached,cs,c1,frame,ck⟩ := Verify.resumeChoice call bs work ret (by decide)
  have one : c[0].get 64 = 1 := by rw [c1,b1]; rfl
  have pushed : RamWriteFrame m (memStore m (sp-136-8) (0x104d04 : BitVec 64)) (scratch sp) :=
    (RamWriteFrame.refl _ _).memStore _ (scratchInside room high callPush (by decide) (by decide))
  have total := pushed.trans frame (by
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    obtain ⟨reg,mem,start,last,_⟩ := scratchInside room high
      (show sp-136-8-1 = sp-145 by bv_omega) (len := 1) (by decide) (by decide)
    exact ⟨reg,mem,start,last⟩)
  obtain ⟨d,jump,ds,dk⟩ := choiceJump (congrArg (Value.get 64) cs) one (win.of_frame total)
  have finish : Verify.Core.Reaches .l104d04 c n .l104d10 d _ :=
    .step (by change (program.runBlock _ _).next _ _ = _; rw [jump]; rfl) (.refl _)
  refine ⟨d,_,reached.trans finish,ds.trans cs,
    total.memStore _ (scratchInside room high rfl (off := 128) (by decide) (by decide)),?_⟩
  intro i hi
  refine (dk i hi).trans ((ck i ?_).trans (bk i hi))
  simp only [kept,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem nonzero {fr : Activation} {a : Verify.Core.Registers} {r s : Nat}
    (input : Inputs fr r s)
    (entry : Atom.All Extracted.programImage a fr.original (Fn104c90.frameAt .l104c90 fr)) :
    ∃ b m, Verify.Core.Reaches .l104c90 a fr.original .l104d10 b m ∧ Saved fr b m := by
  obtain ⟨b,call,pre⟩ := enterCompare input entry
  let ch := compareFrame fr (scalarWords s)
  let st := stage fr (scalarWords s)
  have staged := stageFrame input (scalarWords s)
  obtain ⟨words,zeroWords⟩ := stageWords fr (scalarWords s)
  simp only [Fn104c90.frameAt,Fn104c90.frameAtG5,Atom.All,Atom.Holds] at entry
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,retRead,retAt,retSmall,stack,roomAt,align,_⟩ := entry
  have stagedWindow := stack.of_frame staged
  have readLeft : Readable st ch.rdi 32 :=
    stagedWindow.readable.of_offsets (addr_sub _ 96) (addr_sub _ 464) (by decide)
  have readRight : Readable st ch.rsi 32 :=
    stagedWindow.readable.of_offsets (addr_sub _ 128) (addr_sub _ 464) (by decide)
  have room := input.room
  have high := input.high
  have leftApart : Outside [ch.region] ch.rdi 32 := by
    simp only [Outside,List.mem_singleton,forall_eq,Activation.region,ch,compareFrame]
    stack_bounds
  have rightApart : Outside [ch.region] ch.rsi 32 := by
    simp only [Outside,List.mem_singleton,forall_eq,Activation.region,ch,compareFrame]
    stack_bounds
  have bound : s < 2^256 := Nat.lt_trans input.sBound (by decide)
  obtain ⟨out,exec,tag,post,writes,_,zero⟩ :=
    Verify.Core.compareNonzero (fr := ch) pre readLeft readRight leftApart rightApart words zeroWords input.sPos bound
  have compared := Verify.reachesOfCall call exec tag
  change Atom.All _ _ _ (Generate.LIR.Fn10a280.doneAt ch) at post
  simp only [Generate.LIR.Fn10a280.doneAt,Atom.All,Atom.Holds] at post
  obtain ⟨osp,df,bx,bp,_,r13,r14,_,mx,ft,fc,_⟩ := post
  have rsp : out.values[4].get 64 = fr.rsp-136 :=
    (congrArg (Value.get 64) osp).trans (show fr.rsp-144+8 = fr.rsp-136 by bv_omega)
  have window : Writable Extracted.programImage out.store (fr.rsp-160) 40 :=
    (stagedWindow.of_frame writes).of_offsets (addr_sub _ 160) (addr_sub _ 464) (by decide)
  obtain ⟨c,n,reached,sp,chosen,keep⟩ := passChoice rsp zero window (by omega) (by omega)
  have childWithin : RegionsWithin [ch.region] (scratch fr.rsp) := by
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    refine ⟨_,List.mem_singleton_self _,Nat.le_refl _,?_⟩
    change (fr.rsp-160).toNat + ((fr.rsp-144).toNat - (fr.rsp-160).toNat) ≤ (fr.rsp-160).toNat + 40
    stack_bounds
  have callFrame : RamWriteFrame st n (scratch fr.rsp) :=
    ((RamWriteFrame.refl _ _).trans writes childWithin).trans chosen (fun t ht => ⟨t,ht,Nat.le_refl _,Nat.le_refl _⟩)
  have lo := input.low
  have total := staged.trans callFrame (by
    intro t ht
    change t ∈ [⟨(fr.rsp-160).toNat,40⟩] at ht
    obtain rfl := List.mem_singleton.mp ht
    refine ⟨fr.region,List.mem_singleton_self _,?_⟩
    simp only [Activation.region,lo]
    stack_bounds)
  have loadSp : memLoad n fr.rsp 64 = fr.ret := by
    rw [total.memLoad_eq, retAt]
    simp only [Outside,List.mem_singleton,forall_eq,Activation.region,lo]
    stack_bounds
  have savedSlot (off : BitVec 64) (fit : off.toNat ≤ 32) :
      memLoad n (fr.rsp-off) 64 = memLoad st (fr.rsp-off) 64 := by
    apply callFrame.memLoad_eq
    simp only [Outside,scratch,List.mem_singleton,forall_eq]
    rw [BitVec.toNat_sub_of_le (show off ≤ fr.rsp from BitVec.le_def.mpr (by omega))]
    stack_bounds
  refine ⟨c,n,compared.trans reached,?_,total⟩
  simp only [Fn104c90.frameAt,Fn104c90.frameAtG5,Atom.All,Atom.Holds]
  refine ⟨sp,(keep 22 (by decide)).trans df,(keep 3 (by decide)).trans bx,
    (keep 5 (by decide)).trans bp,(keep 13 (by decide)).trans r13,(keep 14 (by decide)).trans r14,
    (keep 39 (by decide)).trans mx,(keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,
    ?_,?_,?_,?_,retRead.of_frame total,loadSp,retSmall,stack.of_frame total,roomAt,align,trivial⟩
  all_goals
    rw [savedSlot _ (by decide)]
    unfold st stage
    segment_words [] <;> rfl

end K256.Proofs.Signing.Scalar.Normalize
