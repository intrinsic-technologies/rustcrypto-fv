import K256.Proofs.Signing.Composition.Attempt.Arithmetic.Base

namespace K256.Proofs.Signing.Composition.Attempt.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Verify.LIR

private theorem fillAtoms {s : RamState} {secret msg : ByteArray} {a : Registers} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (mem : Memory s m)
    (rsp : a[4] = ⟨64,sp s-8⟩) (df : a[22] = ⟨1,0⟩)
    (gp : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64)
    (fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16)
    (args : ParseSignature.ArgumentWidths a) (tag : memLoad m (sp s-8) 64 = 0x105bf2) :
    Atom.All Extracted.programImage a m (Fn127d70.frameAt .l127d70 (activation s m a 208 0x105bf2)) ∧
      ((sp s).toNat + 1048 ≤ 0x203dd0 ∨ 0x203e28 ≤ (sp s).toNat - 329) := by
  let info : FrameInfo := { Fn127d70.frameInfo with callSlots := [] }
  have base := childAtoms call mem info rfl (by decide) (by decide) rsp df gp fp args tag (by decide)
  change Atom.All Extracted.programImage a m (info.entryAtoms (activation s m a 208 0x105bf2)) at base
  have ro : Verify.LIR.rodataSection ∈ Extracted.programSections := by
    simp only [Verify.LIR.rodataSection,Extracted.programSections,List.mem_cons, true_or,or_true]
  have got := Fn127d70.callSlots_loaded ro (mem.image call)
  obtain ⟨r₁,v₁⟩ := got (0x203dd0,0x12a820) (by decide)
  obtain ⟨r₂,v₂⟩ := got (0x203de0,0x129770) (by decide)
  obtain ⟨r₃,v₃⟩ := got (0x203e20,0x100a20) (by decide)
  have member : Stack.region s signingKeyTrySign.minStackBytes ∈ writtenRegions signingKeyTrySign s := by
    simp [writtenRegions]
  have apart := apart_of_avoids (lo := 0x203dd0) (hi := 0x203e28) (call.separation.2 _ member).1
    (fun a lo hi => by
      obtain ⟨b,hb⟩ := Fn127d70.callSlots_span ro a lo hi
      exact Or.inl ⟨b, Common.programSections_fetchByte_of_mem hb⟩)
    (by rw [stackRegion call]; exact (by decide : 0 < 11200)) (by decide) (by decide)
  have ⟨room,_,baseNat⟩ := stackBounds call
  rw [stackRegion call] at apart
  change (stackPtr s-11192).toNat + 11200 ≤ 0x203dd0 ∨ 0x203e28 ≤ (stackPtr s-11192).toNat at apart
  have bottom : (stackPtr s-11192).toNat = (stackPtr s).toNat-11192 :=
    Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  rw [bottom] at apart
  have rspNat : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (depth := 8) (by decide)
  simp only [Fn127d70.frameAt,Fn127d70.frameAtG28,Atom.All,Atom.Holds]
  simp only [info,Fn127d70.frameInfo,FrameInfo.entryAtoms,FrameInfo.frameAtoms,FrameInfo.entryFrame,
    FrameInfo.entryRegs,FrameInfo.stackAtoms,FrameInfo.callSlotAtoms,Activation.below,FrameInfo.window,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,Atom.All,Atom.Holds,↓reduceIte] at base
  obtain ⟨v4,vdf,cx,dx,bx,bp,si,di,r8,r9,r12,r13,r14,r15,mx,ft,fc,rd,rv,small,wr,depth,align,_⟩ := base
  have sep : 0x203ef8 ≤ (sp s-8).toNat ∨ (sp s-8).toNat ≤ 0x203dd0 := by
    rw [rspNat]
    omega
  exact ⟨⟨v4,vdf,cx,dx,bx,bp,si,di,r8,r9,r12,r13,r14,r15,mx,ft,fc,rd,rv,small,wr,depth,align,
    r₁,v₁,r₂,v₂,r₃,v₃,sep,trivial⟩,by omega⟩

structure ReducedX (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k r : Nat)
    (a : Registers) (m : Ram) : Prop
    extends LoopMemory s d msg st m, RegistersAt s a (sp s+256) (sp s+192) (sp s+656) (sp s+456) where
  temp : a[14] = ⟨64,sp s+160⟩
  rWords : WordsAt m (sp s+128) 64 (scalarWords r)
  digest : WordsAt m (sp s+656) 64 (scalarWords (digestScalar msg))
  inverse : WordsAt m (sp s+424) 64 (scalarWords (Curve.inverse domain.n k))

local macro "arith_bounds" : tactic => `(tactic|
  (simp only [activation,Activation.region,ParseSignature.callStack,ParseSignature.buffer,
    BitVec.sub_sub,BitVec.reduceAdd,BitVec.toNat_sub,BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]
   omega))

private def reductionRegions (s : RamState) : List MemoryRegion :=
  [⟨(sp s-216).toNat,440⟩, ⟨(sp s+456).toNat,4⟩]

private theorem reductionWithin {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RegionsWithin (reductionRegions s) (workRegions s) := by
  obtain ⟨room,limit,base⟩ := stackBounds call
  simp only [BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow] at base
  intro r hr
  simp only [reductionRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,List.mem_cons_self,by dsimp only [workRegions]; arith_bounds⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),by
      dsimp only [workRegions]; arith_bounds⟩

private theorem reductionMemory {s : RamState} {secret msg : ByteArray} {d : Nat} {st : State} {m n : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (before : LoopMemory s d msg st m)
    (frame : RamWriteFrame m n (reductionRegions s)) :
    LoopMemory s d msg st n :=
  before.preserve_work call (extendFrame frame (reductionWithin call))

private theorem initialArgumentWidths {a b : Registers} (w : ParseSignature.ArgumentWidths a)
    (r1 : b[1].width = 64) (r2 : b[2].width = 64)
    (r6 : b[6].width = 64) (r7 : b[7].width = 64)
    (r8 : b[8].width = 64) (r9 : b[9] = a[9]) : ParseSignature.ArgumentWidths b := by
  intro ⟨i,hi⟩ h
  simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · exact r7
  · exact r6
  · exact r2
  · exact r1
  · exact r8
  · exact (congrArg Value.width r9).trans (w 9 (by decide))

private theorem carryArgumentWidths {a b : Registers} (w : ParseSignature.ArgumentWidths a)
    (r1 : b[1].width = 64) (r2 : b[2].width = 64)
    (r6 : b[6].width = 64) (r7 : b[7].width = 64)
    (r8 : b[8] = a[8]) (r9 : b[9] = a[9]) : ParseSignature.ArgumentWidths b :=
  initialArgumentWidths w r1 r2 r6 r7
    ((congrArg Value.width r8).trans (w 8 (by decide))) r9


theorem reduceX {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k x y : Nat}
    (ready : CoordinatesReady s d msg st k x y a m) :
    ∃ b n, Reach (core .l105b88 a m) (core .l105c3e b n) ∧ ReducedX s d msg st k (x % domain.n) b n := by
  obtain ⟨room,lim,base⟩ := stackBounds call
  simp only [BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow] at base
  have m0 := ready.toLoopMemory
  have stack0 := negativeWindow (off := 8) (n := 468) call m0.toMemory (by decide)
  obtain ⟨c,n,fillCall,csp,di,si,dx,cx,r8,r9,keep,fillSetup,tag⟩ :=
    setupFill (getWord ready.rsp) (getWord ready.xDst)
      (getWord ready.rbp) stack0
  have fillFrame : RamWriteFrame m n (reductionRegions s) := (RamWriteFrame.refl m _).trans fillSetup (by
    intro q hq
    simp only [fillWrites,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_self,by dsimp only [reductionRegions]; arith_bounds⟩
    · exact ⟨_,List.mem_cons_self,by dsimp only [reductionRegions]; arith_bounds⟩
    · exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,by dsimp only [reductionRegions]; arith_bounds⟩)
  have m1 := reductionMemory call m0 fillFrame
  have w := initialArgumentWidths ready.widths (congrArg Value.width cx) (congrArg Value.width dx)
      (congrArg Value.width si) (congrArg Value.width di) (congrArg Value.width r8) r9
  have df := (keep 22 (by decide)).trans ready.df
  have gp := savedGP keep (regsGP ready.toRegistersAt)
  have fp := savedFP keep ready.fp
  obtain ⟨atoms,gotApart⟩ := fillAtoms call m1.toMemory csp df gp fp w tag
  let fr := activation s n c 208 0x105bf2
  have dstNat : (sp s+192).toNat = (sp s).toNat+192 := offsetNat call (offset := 192) (by decide)
  have cdst : fr.rdx = sp s+192 := getWord dx
  have csrc : fr.rdi = sp s+160 := getWord di
  have srcAt := hasBytes_of_frame fillSetup (a := sp s+160) (size := 32)
    (by simp only [Outside,fillWrites,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq];
        arith_bounds) ready.xBytes
  obtain ⟨u,run,returned,post,wf,widths,status,words⟩ :=
    Verify.Core.fillScalar (fr := fr) atoms (getWord si)
      (getWord cx) (getWord r8)
      (by rw [csrc]; exact (stackWindow call m1.toMemory (by decide)).readable)
      (by rw [cdst]; exact stackWindow call m1.toMemory (by decide))
      (by rw [csrc]; simp only [Outside,List.mem_singleton,forall_eq]; dsimp only [fr]; arith_bounds)
      (by rw [cdst]; simp only [Outside,List.mem_singleton,forall_eq]; dsimp only [fr]; arith_bounds)
      (by rw [csrc,cdst]; simp only [Outside,ParseSignature.buffer,List.mem_singleton,forall_eq]; arith_bounds)
      (by rw [cdst]; simp only [Outside,ParseSignature.buffer,List.mem_singleton,forall_eq,dstNat,
            BitVec.reduceToNat,Nat.reducePow]
          omega)
  have fillPath := callReaches fillCall (Transfer.verifyExecAt rfl run) returned
  obtain ⟨up,uk⟩ := savedReturn df gp fp post
  obtain ⟨b,jump,bk,bp,b2,b8,b9⟩ := afterFill (m := u.store) status
  have bkeep : SavedRegs b a := fun i hi => (bk i hi).trans ((uk i hi).trans (keep i hi))
  have uw : RamWriteFrame m u.store (reductionRegions s) := fillFrame.trans wf (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_,List.mem_cons_self,by dsimp only [reductionRegions,fr]; arith_bounds⟩
    · exact ⟨_,List.mem_cons_self,by rw [cdst]; dsimp only [reductionRegions,ParseSignature.buffer]; arith_bounds⟩)
  have m2 := reductionMemory call m0 uw
  have filledWords : WordsAt u.store (sp s+192) 64 (scalarWords x) := by
    change WordsAt u.store fr.rdx 64 (scalarWords (ParseSignature.scalarValue n fr.rdi)) at words
    rw [cdst,csrc,Verify.Core.Affine.scalarValue_of_octets srcAt ready.xBound] at words
    exact words
  obtain ⟨e,t,reduceCall,esp,edi,esi,e1,e2,e8,e9,ekeep,reduceSetup,etag,raw⟩ :=
    setupReduce (getWord (bp.trans up))
      (getWord ((bkeep 12 (by decide)).trans ready.r12))
      (negativeWindow call m2.toMemory (by decide)) filledWords
  have m3Frame : RamWriteFrame m t (reductionRegions s) := uw.trans reduceSetup (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,by dsimp only [reductionRegions]; arith_bounds⟩)
  have m3 := reductionMemory call m0 m3Frame
  have eargs := carryArgumentWidths widths e1
    ((congrArg Value.width (e2.trans b2)).trans (widths 2 (by decide)))
    (congrArg Value.width esi) (congrArg Value.width edi) (e8.trans b8) (e9.trans b9)
  have ek : SavedRegs e a := fun i hi => (ekeep i hi).trans (bkeep i hi)
  have edf := (ek 22 (by decide)).trans ready.df
  have egp := savedGP ek (regsGP ready.toRegistersAt)
  have efp := savedFP ek ready.fp
  let er := activation s t e 97 0x105c3e
  have ent : Atom.All Extracted.programImage e t (Fn109f80.frameAt .l109f80 er) :=
    childAtoms call m3.toMemory Fn109f80.frameInfo rfl (by decide) (by decide) esp edf egp efp
      eargs etag (by decide)
  have es : er.rsi = sp s+8 := getWord esi
  have ed : er.rdi = sp s+128 := getWord edi
  obtain ⟨v,rr,rt,rp,frame,rwords,vw⟩ := Verify.Core.reduceScalar ent
    (by rw [es]; exact (stackWindow call m3.toMemory (by decide)).readable)
    (by rw [ed]; exact stackWindow call m3.toMemory (by decide))
    (by rw [es]; simp only [Outside,List.mem_singleton,forall_eq]; dsimp only [er]; arith_bounds)
    (by rw [ed]; simp only [Outside,List.mem_singleton,forall_eq]; dsimp only [er]; arith_bounds)
    (es.symm ▸ raw) ready.xBound
  have reached := callReaches reduceCall (Transfer.verifyExecAt rfl rr) rt
  obtain ⟨vsp,vk⟩ := savedReturn edf egp efp rp
  have va : SavedRegs v.values a := fun i hi => (vk i hi).trans (ek i hi)
  have vwFrame : RamWriteFrame m v.store (reductionRegions s) := m3Frame.trans frame (by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact ⟨_,List.mem_cons_self,by dsimp only [reductionRegions,er]; arith_bounds⟩
    · exact ⟨_,List.mem_cons_self,by rw [ed]; dsimp only [reductionRegions,ParseSignature.buffer]; arith_bounds⟩)
  refine ⟨_,_,fillPath.trans (jump.trans reached),⟨reductionMemory call m0 vwFrame,
    keepRegisters ready.toRegistersAt va vsp vw,(va 14 (by decide)).trans ready.xDst,ed ▸ rwords,?_,?_⟩⟩
  · exact WordsAt.of_frame ready.digest vwFrame (by decide) (by
      simp only [Outside,reductionRegions,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      arith_bounds)
  · exact WordsAt.of_frame ready.inverse vwFrame (by decide) (by
      simp only [Outside,reductionRegions,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      arith_bounds)

end K256.Proofs.Signing.Composition.Attempt.Arithmetic
