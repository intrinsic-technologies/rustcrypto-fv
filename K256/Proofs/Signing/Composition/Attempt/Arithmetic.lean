import K256.Proofs.Signing.Composition.Attempt.Arithmetic.Binary
import K256.Proofs.Signing.Composition.Attempt.Arithmetic.ReduceX
import K256.Proofs.Common.Field.PowMod

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Arithmetic

private def scalarWrites (s : RamState) : List MemoryRegion :=
  [⟨(sp s-329).toNat,369⟩,⟨(sp s+160).toNat,64⟩,⟨(sp s+456).toNat,32⟩]

local macro "arith_bounds" : tactic => `(tactic|
  (simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]
   omega))

private theorem scalarWithinWork {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RegionsWithin (scalarWrites s) (workRegions s) := by
  obtain ⟨room,lim,base⟩ := stackBounds call
  simp only [BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow] at base
  intro r hr
  simp only [scalarWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact ⟨_,List.mem_cons_self,by dsimp only [workRegions]; arith_bounds⟩
  · exact ⟨_,List.mem_cons_self,by dsimp only [workRegions]; arith_bounds⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),by
      dsimp only [workRegions]; arith_bounds⟩

private theorem scalarMemory {s : RamState} {secret msg : ByteArray} {d : Nat} {st : State} {m n : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (before : LoopMemory s d msg st m)
    (frame : RamWriteFrame m n (scalarWrites s)) :
    LoopMemory s d msg st n :=
  before.preserve_work call (extendFrame frame (scalarWithinWork call))

private theorem updateGP {a : Registers} {j : Nat} {hj : j < Reg.count} {v : Value}
    (old : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64)
    (width : v.width = 64) :
    ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → (a.set j v hj)[i].width = 64 := by
  intro ⟨i,hi⟩ h
  by_cases eq : j=i
  · subst i
    simpa only [Fin.getElem_fin,Vector.getElem_set_self] using width
  · simpa only [Fin.getElem_fin,Vector.getElem_set_ne _ _ eq] using old ⟨i,hi⟩ h

local macro "binary_apart" : tactic => `(tactic|
  (intro p hp
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
   rcases hp with ha|ha <;> subst p <;> arith_bounds))

local macro "not_written" regions:Lean.Parser.Tactic.simpLemma : tactic => `(tactic|
  (simp only [Outside,$regions,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
   arith_bounds))

set_option maxHeartbeats 1000000 in
private theorem scalarMultiplyAdd {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k r : Nat}
    (ready : ReducedX s d msg st k r a m) (rBound : r < domain.n) (secretBound : d < domain.n) :
    ∃ b n, Reach (core .l105c3e a m) (core .l105ce7 b n) ∧
      SignatureScalars s d msg st r (signatureScalar d msg k r) b n := by
  obtain ⟨room,lim,base⟩ := stackBounds call
  have depth : 8 ≤ (sp s).toNat := by omega
  simp only [BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow] at base
  have nPos : 0 < domain.n := by decide
  have invBound : Curve.inverse domain.n k < domain.n := by
    rw [Curve.inverse,Common.Field.PowMod.powMod_eq_pow_mod]
    exact Nat.mod_lt _ nPos
  have m0 := ready.toLoopMemory
  obtain ⟨c,t,site,p4,p7,p6,p2,p1,cp,setup,ret,rWords,invWords⟩ :=
    setupProduct (getWord ready.rsp) (getWord ready.r12)
      (getWord ready.rbp) ready.keyPtr
      (negativeWindow call m0.toMemory (by decide)) ready.rWords ready.inverse
  have frame1 : RamWriteFrame m t (scalarWrites s) := (RamWriteFrame.refl m _).trans setup (by
    intro q hq
    simp only [productSetupWrites,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact ⟨_,List.mem_cons_self,by dsimp only [scalarWrites]; arith_bounds⟩
    · exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,by dsimp only [scalarWrites]; arith_bounds⟩)
  have mem1 := scalarMemory call m0 frame1
  have ci : BinaryInputs s c (sp s+8) (sp s+1016) (sp s+192) :=
    ⟨p4,(cp 22 (by decide)).trans ready.df,savedGP cp (regsGP ready.toRegistersAt),
      savedFP cp ready.fp,p1,p7,p6,p2⟩
  obtain ⟨e,u,product,ep,ec,ew,prod,productFoot⟩ :=
    invokeMultiply call site (Or.inr rfl) mem1.toMemory ret (by decide) ci
      ((stackWindow call mem1.toMemory (by decide)).readable)
      ((stackWindow call mem1.toMemory (by decide)).readable)
      (stackWindow call mem1.toMemory (by decide)) (by arith_bounds) (by binary_apart)
      rBound secretBound rWords mem1.key
  have frame2 : RamWriteFrame m u (scalarWrites s) := frame1.trans productFoot (by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact ⟨_,List.mem_cons_self,by dsimp only [scalarWrites]; arith_bounds⟩
    · exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,by dsimp only [scalarWrites]; arith_bounds⟩)
  have mem2 := scalarMemory call m0 frame2
  have ea : SavedRegs e a := fun i hi => (ec i hi).trans (cp i hi)
  have er := keepRegisters ready.toRegistersAt ea ep ew
  obtain ⟨f,sumSite,f4,f7,f6,f2,f1,f8,f9,fe⟩ :=
    setupAdd (getWord er.rsp) (getWord er.r12)
      (getWord er.r13) (getWord er.rbp)
      (negativeWindow call mem2.toMemory (by decide))
  let v := memStore u (sp s-8) (0x105cd6 : BitVec 64)
  have push1 : RamWriteFrame u v [⟨(sp s-8).toNat,8⟩] := pushFrame depth
  have pushWithin : RegionsWithin [⟨(sp s-8).toNat,8⟩] (scalarWrites s) := by
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    exact ⟨_,List.mem_cons_self,by dsimp only [scalarWrites]; arith_bounds⟩
  have frame3 : RamWriteFrame m v (scalarWrites s) := frame2.trans push1 pushWithin
  have mem3 := scalarMemory call m0 frame3
  have fi : BinaryInputs s f (sp s+656) (sp s+192) (sp s+8) := by
    refine ⟨f4,?_,savedGP fe (updateGP (v := ⟨64,sp s+192⟩) (regsGP er) rfl),?_,
      (congrArg Value.width f1).trans (ew 1 (by decide)),f7,f6,f2⟩
    · exact (fe 22 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact er.df)
    · apply savedFP fe
      simpa (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne] using er.fp
  have dig : WordsAt v (sp s+656) 64 (scalarWords (digestScalar msg)) :=
    ready.digest.of_frame frame3 (by decide) (by not_written scalarWrites)
  have prod' : WordsAt v (sp s+192) 64 (scalarWords ((r*d)%domain.n)) :=
    prod.of_frame push1 (by decide) (by
      simp only [Outside,List.mem_singleton,forall_eq]
      arith_bounds)
  have args := fi.widths ((congrArg Value.width f8).trans (ew 8 (by decide)))
    ((congrArg Value.width f9).trans (ew 9 (by decide)))
  obtain ⟨g,w,sumRun,gp,gf,gw,sum,addFoot⟩ :=
    invokeAdd call sumSite mem3.toMemory (memLoad_memStore_same _ _ _ (by decide) (by decide)) (by decide)
      fi args ((stackWindow call mem3.toMemory (by decide)).readable)
      ((stackWindow call mem3.toMemory (by decide)).readable)
      (stackWindow call mem3.toMemory (by decide)) (by arith_bounds) (by binary_apart)
      (Nat.mod_lt _ nPos) (Nat.mod_lt _ nPos) dig prod'
  have frame4 : RamWriteFrame m w (scalarWrites s) := frame3.trans addFoot (by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> exact ⟨_,List.mem_cons_self,by dsimp only [scalarWrites]; arith_bounds⟩)
  have mem4 := scalarMemory call m0 frame4
  have gf₄ (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      g[i] = (e.set 13 ⟨64,sp s+192⟩)[i] :=
    (gf i hi).trans (fe i hi)
  have gr12 : g[12] = ⟨64,sp s+8⟩ :=
    (gf₄ 12 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact er.r12)
  have gr14 : g[14] = ⟨64,sp s+160⟩ :=
    (gf₄ 14 (by decide)).trans (by
      simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]
      exact (ea 14 (by decide)).trans ready.temp)
  have gr15 : g[15] = ⟨64,sp s+456⟩ :=
    (gf₄ 15 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact er.r15)
  obtain ⟨h,mulSite,h4,h7,h6,h2,h1,hg⟩ :=
    setupFinal (getWord gp) (getWord gr12)
      (getWord gr14) (getWord gr15)
      (negativeWindow call mem4.toMemory (by decide))
  let z := memStore w (sp s-8) (0x105ce7 : BitVec 64)
  have push2 : RamWriteFrame w z [⟨(sp s-8).toNat,8⟩] := pushFrame depth
  have frame5 : RamWriteFrame m z (scalarWrites s) := frame4.trans push2 pushWithin
  have mem5 := scalarMemory call m0 frame5
  have gdf := (gf 22 (by decide)).trans fi.df
  have ggp := savedGP gf fi.gp
  have gfp := savedFP gf fi.fp
  have hi : BinaryInputs s h (sp s+160) (sp s+8) (sp s+456) := by
    refine ⟨h4,?_,savedGP hg (updateGP (v := ⟨64,sp s+456⟩) ggp rfl),?_,
      (congrArg Value.width h1).trans (gw 1 (by decide)),h7,h6,h2⟩
    · exact (hg 22 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact gdf)
    · apply savedFP hg
      simpa (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne] using gfp
  have inv' : WordsAt z (sp s+160) 64 (scalarWords (Curve.inverse domain.n k)) := by
    apply WordsAt.of_frame _ push2 (by decide)
      (by simp only [Outside,List.mem_singleton,forall_eq]; arith_bounds)
    apply WordsAt.of_frame _ addFoot (by decide)
      (by simp only [Outside,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]; arith_bounds)
    apply WordsAt.of_frame _ push1 (by decide)
      (by simp only [Outside,List.mem_singleton,forall_eq]; arith_bounds)
    exact WordsAt.of_frame invWords productFoot (by decide) (by
      simp only [Outside,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      arith_bounds)
  have sum' := WordsAt.of_frame sum push2 (by decide) (by
    simp only [Outside,List.mem_singleton,forall_eq]; arith_bounds)
  obtain ⟨j,n,finalRun,jsp,jh,jw,sWords,finalFoot⟩ :=
    invokeMultiply call mulSite (Or.inl rfl) mem5.toMemory
      (memLoad_memStore_same _ _ _ (by decide) (by decide)) (by decide) hi
      ((stackWindow call mem5.toMemory (by decide)).readable)
      ((stackWindow call mem5.toMemory (by decide)).readable)
      (stackWindow call mem5.toMemory (by decide)) (by arith_bounds) (by binary_apart)
      invBound (Nat.mod_lt _ nPos) inv' sum'
  have frame6 : RamWriteFrame m n (scalarWrites s) := frame5.trans finalFoot (by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact ⟨_,List.mem_cons_self,by dsimp only [scalarWrites]; arith_bounds⟩
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),by
        dsimp only [scalarWrites]; arith_bounds⟩)
  have out (i : Fin Reg.count) (hl : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      j[i] = (g.set 3 ⟨64,sp s+456⟩)[i] := (jh i hl).trans (hg i hl)
  have g13 : g[13] = ⟨64,sp s+192⟩ :=
    (gf₄ 13 (by decide)).trans (Vector.getElem_set_self _)
  have g5 : g[5] = ⟨64,sp s+192⟩ :=
    (gf₄ 5 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact er.rbp)
  have jt : j[14] = ⟨64,sp s+160⟩ := (out 14 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact gr14)
  have regs : RegistersAt s j (sp s+456) (sp s+192) (sp s+192) (sp s+456) := by
    refine ⟨jsp,?_,(out 3 (by decide)).trans (Vector.getElem_set_self _),?_,?_,?_,
      congrArg Value.width jt,?_,jw,savedFP jh hi.fp⟩
    · exact (jh 22 (by decide)).trans hi.df
    all_goals
      first
      | exact (out 5 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact g5)
      | exact (out 12 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact gr12)
      | exact (out 13 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact g13)
      | exact (out 15 (by decide)).trans (by simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne]; exact gr15)
  exact ⟨_,_,product.trans (sumRun.trans finalRun),
    ⟨scalarMemory call m0 frame6,regs,jt,ready.rWords.of_frame frame6 (by decide) (by not_written scalarWrites),sWords⟩⟩

theorem arithmetic {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k x y : Nat}
    (ready : CoordinatesReady s d msg st k x y a m) (secretBound : d < domain.n) :
    ∃ b n, Reach (core .l105b88 a m) (core .l105ce7 b n) ∧
      SignatureScalars s d msg st (Nat.mod x domain.n) (signatureScalar d msg k (Nat.mod x domain.n)) b n := by
  obtain ⟨b,n,red,h⟩ := reduceX call ready
  obtain ⟨c,t,scalars,post⟩ := scalarMultiplyAdd call h (Nat.mod_lt _ (by decide)) secretBound
  exact ⟨c,t,red.trans scalars,post⟩

end K256.Proofs.Signing.Composition.Attempt
