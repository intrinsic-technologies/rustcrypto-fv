import K256.Proofs.Signing.Composition.Memory
import K256.Proofs.Signing.Composition.Reach
import K256.Proofs.Signing.Nonce.Fill
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Signing.LIR.Fn105420

namespace K256.Proofs.Signing.Composition

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

private def fillCallMemory (m : Ram) (p : BitVec 64) : Ram :=
  memStore (memStore (memStore (memStore (memStore m (p+408) (0 : BitVec 64))
    (p+400) (0 : BitVec 64)) (p+392) (0 : BitVec 64)) (p+384) (0 : BitVec 64))
    (p-8) (0x1058d0 : BitVec 64)

set_option maxHeartbeats 600000 in
private theorem fillCallBlock {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4] = ⟨64,p⟩)
    (slot : Writable Extracted.programImage m (p+384) 32)
    (push : Writable Extracted.programImage m (p-8) 8) :
    ∃ b : Registers,
      LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105886,a,m⟩ =
        .call ⟨.l100a40,b,fillCallMemory m p⟩ (resume .l1058d0 0x1058d0) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+688⟩ ∧ b[6] = ⟨64,p+384⟩ ∧ b[2] = ⟨64,32⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,3,5,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have addr : a[4].get 64 = p := congrArg (Value.get 64) rsp
  refine ⟨?b, ?step, ?outRsp, ?outGen, ?outDst, ?outLen, ?keep⟩
  case step =>
    cfg_eval [addr]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using LIR.code_l105886)
    rfl
  case outRsp => rfl
  case outGen => rfl
  case outDst => rfl
  case outLen => rfl
  case keep =>
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private def fillActivation (s : RamState) (a : Registers) (m : Ram) : Activation where
  original := fillCallMemory m (sp s)
  rsp := sp s - 8
  ret := 0x1058d0
  low := sp s - 2168
  rbx := a[3].get 64
  rbp := a[5].get 64
  r12 := a[12].get 64
  r13 := a[13].get 64
  r14 := a[14].get 64
  r15 := a[15].get 64
  rdi := sp s + 688
  rsi := sp s + 384
  rdx := 32
  rcx := a[1].get 64
  r8 := a[8].get 64
  r9 := a[9].get 64
  mxcsr := a[39].get 32
  ftw := a[50].get 16
  fcw := a[51].get 16
  fs := s.FS

private def fillRegions (p : Nat) : List MemoryRegion :=
  [⟨p-2168,2168⟩, ⟨p+384,32⟩, ⟨p+696,64⟩]

private def setupRegions (p : Nat) : List MemoryRegion :=
  [⟨p-2168,2168⟩, ⟨p+384,32⟩]

private theorem addOffset (p : BitVec 64) (limit : p.toNat + 1296 < 2^32)
    (i : Nat) (h : i ≤ 1296) : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem fillOutside {p : BitVec 64} (depth : 2168 ≤ p.toNat)
    (limit : p.toNat + 1296 < 2^32)
    {i n : Nat} (fits : i+n ≤ 1296) (buf : i+n ≤ 384 ∨ 416 ≤ i)
    (gen : i+n ≤ 696 ∨ 760 ≤ i) :
    Outside (fillRegions p.toNat) (p + BitVec.ofNat 64 i) n := by
  rw [Outside, addOffset p limit i (by omega)]
  refine ⟨?_, fun r hr => ?_⟩
  · omega
  · simp only [fillRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp <;> omega

private theorem setupWrites {m : Ram} {p : BitVec 64} (depth : 2168 ≤ p.toNat)
    (limit : p.toNat + 1296 < 2^32) :
    RamWriteFrame m (fillCallMemory m p) (setupRegions p.toNat) := by
  have sub : (p-8).toNat = p.toNat-8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ p from by change 8 ≤ p.toNat; omega)
  have buffer (i : Nat) (lo : 384 ≤ i) (hi : i ≤ 408) :
      InRegions (setupRegions p.toNat) (p + BitVec.ofNat 64 i) 8 := by
    refine ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),?_⟩
    rw [InRegion, addOffset p limit i (by omega)]
    dsimp
    omega
  have tag : InRegions (setupRegions p.toNat) (p-8) 8 := by
    refine ⟨_,List.mem_cons_self,?_⟩
    rw [InRegion,sub]
    dsimp
    omega
  exact (((((RamWriteFrame.refl m _).memStore (0 : BitVec 64) (buffer 408 (by decide) (by decide))).memStore
    (0 : BitVec 64) (buffer 400 (by decide) (by decide))).memStore
    (0 : BitVec 64) (buffer 392 (by decide) (by decide))).memStore
    (0 : BitVec 64) (buffer 384 (by decide) (by decide))).memStore
    (0x1058d0 : BitVec 64) tag

private theorem fillWithin {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RegionsWithin (fillRegions (sp s).toNat) [Stack.region s signingKeyTrySign.minStackBytes] := by
  obtain ⟨room,_,nat⟩ := stackBounds call
  rw [stackRegion call]
  intro r hr
  refine ⟨_,List.mem_cons_self,?_⟩
  simp only [fillRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp only [nat] <;> dsimp <;> omega

private theorem coreAfterFill {s : RamState} {secret msg : ByteArray} {d : Nat} {m n : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (coreMem : CoreMemory s d m) (writes : RamWriteFrame m n (fillRegions (sp s).toNat)) :
    CoreMemory s d n := by
  have ⟨room,top,nat⟩ := stackBounds call
  refine coreMem.preserve writes (fillWithin call) ?_
  intro i hi
  simp only [protectedOffsets, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact fillOutside (by omega) (by omega) (by decide) (by decide) (by decide)

private theorem valueWidth (v : Value) {w : Nat} (width : v.width = w) :
    v = ⟨w,v.get w⟩ := by
  obtain ⟨n,b⟩ := v
  change n = w at width
  subst n
  simp only [Value.get,BitVec.setWidth_eq]

private theorem fillReach {src dst src' dst'} (entry : (src,dst) ∈ Transfer.sharedLabels)
    (finish : (src',dst') ∈ Transfer.sharedLabels)
    {a b : Registers} {m n : Ram}
    (run : Verify.Core.Reaches src a m src' b n) :
    Reach (fill dst a m) (fill dst' b n) := by
  exact appendStack (Transfer.verifyReaches entry finish run)
    [resume .l1058d0 0x1058d0,resume .l102795 0x102795]

set_option maxHeartbeats 550000 in
set_option maxRecDepth 1024 in
theorem enter {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} (outer : Outer s d msg st a m) :
    ∃ x, Reach (core .l105886 a m) x ∧ AtCandidate s d msg st x := by
  obtain ⟨room,top,nat⟩ := stackBounds call
  let p := sp s
  let fr := fillActivation s a m
  change p.toNat = (stackPtr s).toNat - 1288 at nat
  have depth : 2168 ≤ p.toNat := by omega
  have limit : p.toNat + 1296 < 2^32 := by omega
  have add (i : Nat) (hi : i ≤ 1296) := addOffset p limit i hi
  have sub (i : BitVec 64) (hi : i.toNat ≤ 2168) : (p-i).toNat = p.toNat-i.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have frRsp : fr.rsp.toNat = p.toNat-8 := sub 8 (by decide)
  have frLow : fr.low.toNat = p.toNat-2168 := sub 2168 (by decide)
  have frLowEq : fr.low = fr.rsp - 2160 := by change p-2168 = p-8-2160; bv_omega
  have frRegion : fr.region = ⟨p.toNat-2168,2160⟩ := by
    simp only [Activation.region,frRsp,frLow]
    rw [show p.toNat-8-(p.toNat-2168) = 2160 by omega]
  have oldAlign := call.stackAvailable.2.2.2
  change (stackPtr s).toNat % 16 = 8 at oldAlign
  have align : fr.rsp.toNat % 16 = 8 := by rw [frRsp,nat]; omega
  have bottom : (stackPtr s - 11192).toNat = (stackPtr s).toNat - 11192 :=
    Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  have window := outer.toMemory.window call
  have lowBase : (stackPtr s - 11192).toNat ≤ p.toNat - 2168 := by
    rw [bottom,nat]
    omega
  have highBase : p.toNat + 760 ≤ (stackPtr s - 11192).toNat + 11200 := by
    rw [bottom,nat]
    omega
  have part {q : BitVec 64} {len : Nat} (lo : p.toNat-2168 ≤ q.toNat)
      (hi : q.toNat+len ≤ p.toNat+760) : Writable Extracted.programImage m q len :=
    window.sub (Nat.le_trans lowBase lo) (Nat.le_trans hi highBase)
  have bufNat : (p+384).toNat = p.toNat+384 := add 384 (by decide)
  have seedNat : (p+696).toNat = p.toNat+696 := add 696 (by decide)
  have buf := part (q := p+384) (len := 32) (by rw [bufNat]; omega) (by rw [bufNat]; omega)
  have push : Writable Extracted.programImage m fr.rsp 8 :=
    part (by rw [frRsp]; omega) (by rw [frRsp]; omega)
  obtain ⟨b,block,rsp,rdi,rsi,rdx,kept⟩ := fillCallBlock outer.rsp buf push
  have callStep : Reach (core .l105886 a m) (fill .l100a40 b fr.original) :=
    .single (congrArg (Transfer.next (dialect Extracted.programImage) [resume .l102795 0x102795]) block)
  have actualWrites : RamWriteFrame m fr.original (setupRegions p.toNat) := setupWrites depth limit
  have setup : RamWriteFrame m fr.original (fillRegions p.toNat) := by
    apply (RamWriteFrame.refl _ _).trans actualWrites
    intro r hr
    refine ⟨r,?_,Nat.le_refl _,Nat.le_refl _⟩
    simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  have img := (coreAfterFill call outer.toCoreMemory setup).toMemory.image call
  have rd := push.readable.of_frame setup
  have lowWin : Writable Extracted.programImage fr.original (fr.rsp-2160) 2160 := by
    rw [← frLowEq]
    exact (part (by rw [frLow]; exact Nat.le_refl _) (by rw [frLow]; omega)).of_frame setup
  have hiWin : Writable Extracted.programImage fr.original fr.rsp 768 :=
    (part (by rw [frRsp]; omega) (by rw [frRsp]; omega)).of_frame setup
  have ret : memLoad fr.original fr.rsp 64 = fr.ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have rodata : Verify.LIR.rodataSection ∈ Extracted.programSections :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have tables := Verify.LIR.Fn100a40.callSlots_loaded rodata img
  obtain ⟨rd0,v0⟩ := tables (0x203dd0,0x12a820) (by decide)
  obtain ⟨rd1,v1⟩ := tables (0x203de0,0x129770) (by decide)
  obtain ⟨rd2,v2⟩ := tables (0x203e10,0x12a700) (by decide)
  obtain ⟨rd3,v3⟩ := tables (0x203e20,0x100a20) (by decide)
  have gap : 0x204698 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 := by
    have memStack : Stack.region s signingKeyTrySign.minStackBytes ∈
        writtenRegions signingKeyTrySign s := by simp [writtenRegions]
    have h := apart_of_avoids (call.separation.2 _ memStack).1
      (lo := 0x203dd0) (hi := 0x203e28)
      (fun addr lo hi => by
        obtain ⟨byte,member⟩ := Verify.LIR.Fn100a40.callSlots_span rodata addr lo hi
        exact Or.inl ⟨byte,Common.programSections_fetchByte_of_mem member⟩)
      (by rw [stackRegion call]; change 0 < 11200; decide) (by decide) (by decide)
    rw [stackRegion call] at h
    change (stackPtr s - 11192).toNat + 11200 ≤ 0x203dd0 ∨
      0x203e28 ≤ (stackPtr s - 11192).toNat at h
    rw [bottom] at h
    rw [frRsp,nat]
    omega
  have widths : ∀ i : Fin Reg.count, i.val ∈ [1,8,9] → a[i].width = 64 := by
    intro i hi
    exact outer.widths i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with h|h|h <;> simp only [Activation.argumentNumbers,h,List.mem_cons,
        List.not_mem_nil,or_false,true_or,or_true])
  have rbx := valueWidth a[3] (congrArg Value.width outer.rbx)
  have rbp := valueWidth a[5] (congrArg Value.width outer.rbp)
  have r12 := valueWidth a[12] (congrArg Value.width outer.r12)
  have r13 := valueWidth a[13] (congrArg Value.width outer.r13)
  have r14 := valueWidth a[14] outer.r14
  have r15 := valueWidth a[15] (congrArg Value.width outer.r15)
  have mx := valueWidth a[39] outer.fp.1
  have ft := valueWidth a[50] outer.fp.2.1
  have fc := valueWidth a[51] outer.fp.2.2
  have atoms : Atom.All Extracted.programImage b fr.original (Verify.LIR.Fn100a40.frameAt .l100a40 fr) := by
    simp only [Verify.LIR.Fn100a40.frameAt,Verify.LIR.Fn100a40.frameAtG1,Atom.All,Atom.Holds]
    exact ⟨rsp,(kept 22 (by decide)).trans outer.df,
      (kept 1 (by decide)).trans (valueWidth a[1] (widths 1 (by decide))),rdx,
      (kept 3 (by decide)).trans rbx,(kept 5 (by decide)).trans rbp,rsi,rdi,
      (kept 8 (by decide)).trans (valueWidth a[8] (widths 8 (by decide))),
      (kept 9 (by decide)).trans (valueWidth a[9] (widths 9 (by decide))),
      (kept 12 (by decide)).trans r12,(kept 13 (by decide)).trans r13,
      (kept 14 (by decide)).trans r14,(kept 15 (by decide)).trans r15,
      (kept 39 (by decide)).trans mx,(kept 50 (by decide)).trans ft,
      (kept 51 (by decide)).trans fc,rd,ret,by change (0x1058d0 : BitVec 64).toNat < 2^32; decide,lowWin,by rw [frLow,frRsp]; omega,
      align,rd0,v0,rd1,v1,rd2,v2,rd3,v3,gap,trivial⟩
  have gen : fr.rdi = fr.rsp + 696 := by change p+688 = p-8+696; bv_omega
  have dst : fr.rsi = fr.rsp + 392 := by change p+384 = p-8+392; bv_omega
  have stateAddr : fr.rdi + 8 = p+696 := by change p+688+8 = p+696; bv_omega
  have orderAddr : fr.rsp + 600 = p+592 := by change p-8+600 = p+592; bv_omega
  have pushPtr : fr.rsp + 8 = p := by change p-8+8 = p; bv_omega
  have outBuf := fun {i n} => @fillOutside p depth limit i n
  have orderPtr : memLoad fr.original fr.rdi 64 = fr.rsp+600 := by
    rw [orderAddr]
    exact (setup.memLoad_eq (outBuf (by decide) (by decide) (by decide))).trans outer.orderPtr
  have orderWords : WordsAt fr.original (fr.rsp+600) 64 (Generate.Generator.Multiply.scalarWords domain.n) := by
    rw [orderAddr]
    exact outer.order.of_frame setup (by decide) (outBuf (by decide) (by decide) (by decide))
  have seed : Nonce.Initialize.StateAt fr.original (fr.rdi+8) st := by
    have seedOutside : Outside (setupRegions p.toNat) (p+696) 64 := by
      rw [Outside,seedNat]
      refine ⟨by omega,fun r hr => ?_⟩
      simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> dsimp <;> omega
    exact Nonce.Fill.stateAfter (fr := fr) actualWrites (stateAddr.symm ▸ seedOutside)
      (stateAddr.symm ▸ outer.state)
  obtain ⟨head,c,t,entered,atHead,iter⟩ := Nonce.fill atoms img frLowEq
    (by rw [frRsp]; omega) (by rw [frRsp]; omega) hiWin gen dst rfl orderPtr orderWords seed
  have entryLabel : (Verify.LIR.Label.l100a40,LIR.Label.l100a40) ∈ Transfer.sharedLabels := by
    simp only [Transfer.sharedLabels,List.mem_cons,true_or,or_true]
  have headLabel : (Verify.LIR.Label.l100ab0,LIR.Label.l100ab0) ∈ Transfer.sharedLabels := by
    simp only [Transfer.sharedLabels,List.mem_cons,true_or,or_true]
  have midLabel : (Verify.LIR.Label.l100ac0,LIR.Label.l100ac0) ∈ Transfer.sharedLabels := by
    simp only [Transfer.sharedLabels,List.mem_cons,true_or,or_true]
  refine ⟨fill .l100ab0 c t, callStep.trans (fillReach entryLabel headLabel entered),
    head,c,t,rfl,atHead,?_⟩
  constructor
  · intro state c t ready
    dsimp
    intro pos bound
    have step := iter state c t ready
    rw [ite_eq_left (And.intro pos bound)] at step
    obtain ⟨out,ran,tag,done,widthsOut,wrote,stateOut,bytes⟩ := step
    have signing := Transfer.verifyExec headLabel ran
    have resumed := ParseSignature.exec_reaches_resume signing (resume .l1058d0 0x1058d0)
      [resume .l102795 0x102795] (by rw [tag]; rfl)
    simp only [Verify.LIR.Fn100a40.doneAt,Atom.All,Atom.Holds] at done
    obtain ⟨s4,s22,s3,s5,s12,s13,s14,s15,s39,s50,s51,_⟩ := done
    have full : RamWriteFrame m out.store (fillRegions p.toNat) := by
      apply setup.trans wrote
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · refine ⟨_,List.mem_cons_self,?_⟩
        rw [frRegion]
        dsimp
        omega
      · refine ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),?_⟩
        change p.toNat+384 ≤ (p+384).toNat ∧ (p+384).toNat+32 ≤ p.toNat+384+32
        rw [bufNat]
        exact ⟨Nat.le_refl _,Nat.le_refl _⟩
      · refine ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),?_⟩
        rw [stateAddr, seedNat]
        exact ⟨Nat.le_refl _,Nat.le_refl _⟩
    refine ⟨out.values,out.store,?_,⟨coreAfterFill call outer.toCoreMemory full,?_,?_,?_,?_,?_,?_⟩,bytes⟩
    · have loc : (resume .l1058d0 0x1058d0).resume out =
          (⟨.l1058d0,out.values,out.store⟩ : LIR.lifted.Location) := by
        exact congrArg (fun args => (⟨.l1058d0,args,out.store⟩ : LIR.lifted.Location))
          (ParseSignature.resume_arguments (resume .l1058d0 0x1058d0) out)
      rw [loc] at resumed
      exact resumed
    · rw [pushPtr] at s4
      exact ⟨s4,s22,s3.trans (rbx.symm.trans outer.rbx),s5.trans (rbp.symm.trans outer.rbp),
        s12.trans (r12.symm.trans outer.r12),s13.trans (r13.symm.trans outer.r13),
        congrArg Value.width s14,s15.trans (r15.symm.trans outer.r15),widthsOut⟩
    · exact ⟨congrArg Value.width s39,congrArg Value.width s50,congrArg Value.width s51⟩
    · exact UpdateV.Finalize.bytesAfter full (outBuf (by decide) (by decide) (by decide)) outer.hash
    · exact outer.order.of_frame full (by decide) (outBuf (by decide) (by decide) (by decide))
    · exact (full.memLoad_eq (outBuf (by decide) (by decide) (by decide))).trans outer.orderPtr
    · simpa only [stateAddr] using stateOut
  · intro state c t ready invalid
    have step := iter state c t ready
    rw [ite_eq_right invalid] at step
    obtain ⟨x,y,u,v,front,back,next⟩ := step
    exact ⟨x,y,u,v,fillReach headLabel midLabel front,fillReach midLabel headLabel back,next⟩

end K256.Proofs.Signing.Composition
