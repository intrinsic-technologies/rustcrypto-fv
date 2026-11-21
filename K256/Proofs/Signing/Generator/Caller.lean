import K256.Proofs.Signing.Generator.Core
import K256.Proofs.Signing.Generator.FirstCopy
import K256.Proofs.Generate.Generator.Multiply.Return
import K256.Proofs.Generate.Generator.Multiply.Caller.Execution

namespace K256.Proofs.Signing.Generator

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  K256.Proofs.Generate K256.Proofs.Generate.Generator
  K256.Proofs.Generate.Generator.Multiply K256.Proofs.Generate.Generator.Multiply.Caller
  Standards.SECG.DomainParameters

set_option maxRecDepth 4096 in
set_option maxHeartbeats 700000 in
private theorem makeCoreEntry {fr : Activation} {a b : Registers} {m : Ram} {d : Nat}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ v ∈ Extracted.programImage, fr.original[v.1]? = some v.2)
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 352 ≤ 2^32) (outputAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (dest : Writable Extracted.programImage fr.original fr.rdi 120)
    (frame : RamWriteFrame fr.original m [fr.region])
    (regs : Atom.All Extracted.programImage b m
      [ .gpr 4 (localSp fr - 8), .reg 22 ⟨1,0⟩, .gpr 1 (localSp fr + 4000), .gpr 2 1,
        .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 6 (localSp fr + 3848), .gpr 7 fr.rdi,
        .gpr 8 1, .gpr 9 (localSp fr + 8), .gpr 12 (localSp fr + 8), .gpr 13 0x12a820,
        .gpr 14 (localSp fr + 3848), .gpr 15 (localSp fr + 4000), .reg 39 ⟨32,fr.mxcsr⟩,
        .reg 50 ⟨16,fr.ftw⟩, .reg 51 ⟨16,fr.fcw⟩ ])
    (tag : memLoad m (localSp fr - 8) 64 = 0x10f12f) (count : memLoad m (localSp fr) 64 = 1)
    (generator : ∀ i : Fin 15, memLoad m (wordAddr (localSp fr + 3848) 64 i.val) 64 =
      memLoad m (wordAddr 0x202bc8 64 i.val) 64)
    (scalar : WordsAt m (localSp fr + 3968) 64 (scalarWords d)) :
    CoreEntry (coreActivation fr m) b d := by
  simp only [Fn10ee80.frameAt, Fn10ee80.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,stack,_,align,_,_,_,_,apart,_⟩ := atoms
  have loaded := callerImage room low stack frame image
  have w := stack.of_frame frame
  have slot {k : BitVec 64} {n : Nat} (fit : (k - (0 - 9768)).toNat + n ≤ 9768) :
      Writable Extracted.programImage m (fr.rsp + k) n :=
    w.of_offsets rfl (addr_sub fr.rsp 9768) fit
  have access {x : BitVec 64} {k : BitVec 64} {n : Nat}
      (eq : x = fr.rsp + k) (fit : (k - (0 - 9768)).toNat + n ≤ 9768) :
      Writable Extracted.programImage m x n := eq ▸ slot fit
  have spNat : (localSp fr - 8).toNat = fr.rsp.toNat - 5968 := by
    rw [show localSp fr - 8 = fr.rsp - 5968 by unfold localSp; bv_omega]
    apply BitVec.toNat_sub_of_le
    change 5968 ≤ fr.rsp.toNat
    omega
  have lowNat : fr.low.toNat = fr.rsp.toNat - 9768 := by
    rw [low, BitVec.toNat_sub_of_le (by change 9768 ≤ fr.rsp.toNat; exact room)]
    rfl
  have slots := Fn11c880.callSlots_loaded (sections := Extracted.programSections)
    (by simp [Extracted.programSections, rodataSection]) loaded
  obtain ⟨g1,v1⟩ := slots (0x203de0,0x129770) (by decide)
  obtain ⟨g2,v2⟩ := slots (0x203e20,0x100a20) (by decide)
  have plus : localSp fr - 8 + 8 = localSp fr := by bv_omega
  refine ⟨?_,loaded,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,?_,?_,?_,?_,?_,dest.of_frame frame,generator,?_⟩
  · simp only [Fn11c880.frameAt, Fn11c880.frameAtG1, coreActivation, Atom.All, Atom.Holds] at regs ⊢
    obtain ⟨r4,df,r1,r2,r3,r5,r6,r7,r8,r9,r12,r13,r14,r15,mx,ft,fc,_⟩ := regs
    refine ⟨r4,df,r1,r2,r3,r5,r6,r7,r8,r9,r12,r13,r14,r15,mx,ft,fc,
      (access (k := 0 - 5968) (by unfold localSp; bv_omega) (by decide)).readable,tag,by decide,
      access (k := 0 - 9768) (by unfold localSp; bv_omega) (by decide),?_,?_,g1,v1,g2,v2,?_,trivial⟩
    all_goals omega
  · change fr.low = localSp fr - 8 - 3800
    rw [low]; unfold localSp; bv_omega
  · change 3800 ≤ (localSp fr - 8).toNat; omega
  · change (localSp fr - 8).toNat + 6320 ≤ _; omega
  · change localSp fr + 3848 = localSp fr - 8 + 3856; bv_omega
  · change localSp fr + 4000 = localSp fr - 8 + 4008; bv_omega
  · change localSp fr + 8 = localSp fr - 8 + 16; bv_omega
  · change (localSp fr - 8).toNat + 8 ≤ fr.rdi.toNat; omega
  · exact plus ▸ count
  · exact (access (k := 0 - 5960) (by change localSp fr - 8 + 8 = _; unfold localSp; bv_omega) (by decide)).readable
  · exact (access (k := 0 - 2112) (by change localSp fr + 3848 = _; unfold localSp; bv_omega) (by decide)).readable
  · exact access (k := 0 - 1960) (by change localSp fr + 4000 = _; unfold localSp; bv_omega) (by decide)
  · exact access (k := 0 - 5952) (by change localSp fr + 8 = _; unfold localSp; bv_omega) (by decide)
  · change WordsAt m (localSp fr + 3848 + 120) 64 _
    exact (show localSp fr + 3848 + 120 = localSp fr + 3968 by bv_omega) ▸ scalar

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
private theorem afterCore {fr : Activation} {a : Registers} {m : Ram} {d : Nat}
    {out : Output Value Ram Reg.count}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 352 ≤ 2^32) (outputAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (frame : RamWriteFrame fr.original m [fr.region])
    (s3 : memLoad m (fr.rsp - 40) 64 = fr.rbx) (s12 : memLoad m (fr.rsp - 32) 64 = fr.r12)
    (s13 : memLoad m (fr.rsp - 24) 64 = fr.r13) (s14 : memLoad m (fr.rsp - 16) 64 = fr.r14)
    (s15 : memLoad m (fr.rsp - 8) 64 = fr.r15)
    (result : CoreResult (coreActivation fr m) d out) :
    Atom.All Extracted.programImage out.values out.store (Fn10ee80.frameAt .l10f12f fr) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → out.values[i].width = 64) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,120⟩] ∧
      Affine.ProjectiveAt out.store fr.rdi (Curve.generatorWindow d) := by
  obtain ⟨_,done_,widths,writes,point⟩ := result
  simp only [Fn10ee80.frameAt, Fn10ee80.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,read,ret,retLow,stack,below,align,_⟩ := atoms
  simp only [Fn11c880.doneAt, Atom.All, Atom.Holds, coreActivation, BitVec.sub_add_cancel] at done_
  obtain ⟨r4,df,r3,r5,_,_,_,_,mx,ft,fc,_⟩ := done_
  have subNat (k : BitVec 64) (hk : k.toNat ≤ 9768) : (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_trans hk room))
  have loNat : fr.low.toNat = fr.rsp.toNat - 9768 := by rw [low]; exact subNat 9768 (by decide)
  have hsp : (localSp fr - 8).toNat = fr.rsp.toNat - 5968 := by
    rw [show localSp fr - 8 = fr.rsp - 5968 by unfold localSp; bv_omega]; exact subNat 5968 (by decide)
  have digits : (localSp fr + 8).toNat = fr.rsp.toNat - 5952 := by
    rw [show localSp fr + 8 = fr.rsp - 5952 by unfold localSp; bv_omega]; exact subNat 5952 (by decide)
  have table : (localSp fr + 4000).toNat = fr.rsp.toNat - 1960 := by
    rw [show localSp fr + 4000 = fr.rsp - 1960 by unfold localSp; bv_omega]; exact subNat 1960 (by decide)
  have keep (k : BitVec 64) (hk : k.toNat ≤ 40) :
      memLoad out.store (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    have nat := subNat k (by omega)
    apply writes.memLoad_eq
    simp only [Outside,coreWrites,coreActivation,Activation.region,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,Nat.reduceDiv]
    omega
  have inner : RegionsWithin (coreWrites (coreActivation fr m)) [fr.region,⟨fr.rdi.toNat,120⟩] := by
    intro r hr
    simp only [coreWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    rotate_left 3
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩
    all_goals refine ⟨fr.region,List.mem_cons_self,?_,?_⟩
    all_goals simp only [coreActivation, Activation.region] <;> omega
  have frame' : RamWriteFrame fr.original m [fr.region,⟨fr.rdi.toNat,120⟩] := by
    apply (RamWriteFrame.refl _ _).trans frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  have savedRet : memLoad m fr.rsp 64 = fr.ret := by
    apply (frame.memLoad_eq ?_).trans ret
    simp only [Outside,List.mem_singleton,forall_eq,Activation.region,Nat.reduceDiv]
    omega
  refine ⟨?_,widths,frame'.trans writes inner,point⟩
  simp only [Fn10ee80.frameAt, Fn10ee80.frameAtG1, Atom.All, Atom.Holds]
  refine ⟨r4,df,r3,r5,mx,ft,fc,(keep 40 (by decide)).trans s3,(keep 32 (by decide)).trans s12,
    (keep 24 (by decide)).trans s13,(keep 16 (by decide)).trans s14,(keep 8 (by decide)).trans s15,
    (read.of_frame frame).of_frame writes,?_,retLow,(stack.of_frame frame).of_frame writes,below,align,trivial⟩
  have eq := keep 0 (by decide)
  rw [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] at eq
  exact eq.trans savedRet

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
theorem executionOfRegions {fr : Activation} {a : Values Value Reg.count} {d : Nat}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 352 ≤ 2^32)
    (sourceAbove : fr.rsp.toNat ≤ fr.rsi.toNat) (outputAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (source : Readable fr.original fr.rsi 32)
    (destination : Writable Extracted.programImage fr.original fr.rdi 120)
    (words : WordsAt fr.original fr.rsi 64
      (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val))))
    (pos : 0 < d) (bound : d < Secp256k1.domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10ee80, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn10ee80.doneAt fr) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → out.values[i].width = 64) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 120⟩] ∧
      K256.Proofs.Generate.Generator.Affine.ProjectiveAt out.store fr.rdi (Curve.generatorWindow d) := by
  let sp := localSp fr
  let m₁ := firstCopyMemory fr
  let m₂ := secondCopyMemory m₁ sp
  let m₃ := tableCopyMemory m₂ sp
  let m₄ := coreCallMemory m₃ sp
  have initial := atoms
  simp only [Fn10ee80.frameAt,Fn10ee80.frameAtG1,Atom.All,Atom.Holds] at initial
  obtain ⟨_,df,_,_,_,bp,_,_,_,_,_,_,_,_,mx,ft,fc,_,_,_,stack,_⟩ := initial
  have window : Writable Extracted.programImage fr.original (sp - 8) 5928 :=
    stack.of_offsets (x := fr.rsp) (c := 0 - 5968) (by unfold sp localSp; bv_omega)
      (addr_sub fr.rsp 9768) (by decide)
  have stackEnd : (fr.rsp - 9768).toNat + 9768 = fr.rsp.toNat := by
    rw [BitVec.toNat_sub_of_le (by change 9768 ≤ fr.rsp.toNat; exact room)]
    exact Nat.sub_add_cancel room
  obtain ⟨b,p,bsp,b3,b13,b14,bkeep⟩ :=
    Signing.Generator.firstCopy atoms image (Or.inl (stackEnd ▸ sourceAbove)) source
  have w₁ : RamWriteFrame fr.original m₁ [fr.region] := firstCopyFrame room low
  have w₂ : RamWriteFrame fr.original m₂ [fr.region] := secondCopyFrame room low w₁
  have w₄ : RamWriteFrame fr.original m₄ [fr.region] := tableCoreFrame room low w₂
  have bdf := (bkeep 22 (by decide)).trans df
  obtain ⟨c,q,csp,c12,c15,ckeep⟩ := secondCopy
    ((window.of_frame w₁).sub (Nat.le_refl _) (by omega))
    (callerImage room low stack w₁ image) (congrArg (Value.get 64) bsp)
    (congrArg (Value.get 64) b13) (congrArg (Value.get 1) bdf)
  have c13 := (ckeep 13 (by decide) (by decide) (by decide)).trans b13
  have cdf := (ckeep 22 (by decide) (by decide) (by decide)).trans bdf
  obtain ⟨e,r,esp,e15,ekeep⟩ := tableCopies (window.of_frame w₂) (congrArg (Value.get 64) csp)
    (congrArg (Value.get 64) c13) (congrArg (Value.get 64) c15) (congrArg (Value.get 64) c12)
    (congrArg (Value.get 1) cdf)
  have window₃ : Writable Extracted.programImage m₃ (sp - 8) 82 := by
    have w := (window.of_frame w₂).sub (Nat.le_refl _) (show (sp-8).toNat + 82 ≤ (sp-8).toNat + 5928 by omega)
    unfold m₃ tableCopyMemory memCopy
    iterate 4 apply Writable.memStore
    exact w
  obtain ⟨u,call,usp,u1,u2,u6,u7,u8,u9,uk⟩ := coreCall (congrArg (Value.get 64) esp) window₃
  have saved (i : Fin Reg.count) (hi : i.val ∈ [3,5,13,14,22,39,50,51]) : e[i] = b[i] := by
    apply (ekeep i ?_ ?_).trans (ckeep i ?_ ?_ ?_)
    all_goals simp only [memcpyPreserved,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢ <;> omega
  have e3 := (saved 3 (by decide)).trans b3
  have e14 := (saved 14 (by decide)).trans b14
  obtain ⟨generator,scalar,s3,s12,s13,s14,s15⟩ := callerMemoryFacts (d := d) atoms image room low words
  have slots := coreCallSlots m₃ sp
  have entry : CoreEntry (coreActivation fr m₄) u d := by
    apply makeCoreEntry atoms image room low high outputAbove destination w₄ ?_ slots.1 slots.2 generator scalar
    simp only [Atom.All,Atom.Holds]
    refine ⟨usp,?_,?_,u2,?_,?_,?_,?_,u8,u9,?_,?_,?_,?_,?_,?_,?_,trivial⟩
    · exact (uk 22 (by decide)).trans ((saved 22 (by decide)).trans bdf)
    · exact u1.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) e15)
    · exact (uk 3 (by decide)).trans e3
    · exact (uk 5 (by decide)).trans ((saved 5 (by decide)).trans ((bkeep 5 (by decide)).trans bp))
    · exact u6.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) e14)
    · exact u7.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) e3)
    · exact (uk 12 (by decide)).trans ((ekeep 12 (by decide) (by decide)).trans c12)
    · exact (uk 13 (by decide)).trans ((saved 13 (by decide)).trans b13)
    · exact (uk 14 (by decide)).trans e14
    · exact (uk 15 (by decide)).trans e15
    · exact (uk 39 (by decide)).trans ((saved 39 (by decide)).trans ((bkeep 39 (by decide)).trans mx))
    · exact (uk 50 (by decide)).trans ((saved 50 (by decide)).trans ((bkeep 50 (by decide)).trans ft))
    · exact (uk 51 (by decide)).trans ((saved 51 (by decide)).trans ((bkeep 51 (by decide)).trans fc))
  obtain ⟨out,exec,result⟩ := Specialized.coreExecution entry pos bound
  have finish := Sample.reachesAfterSampleCall call exec result.1 []
  have path := ((p.trans q).trans r).trans finish
  obtain ⟨ready,widths,frame,point⟩ :=
    afterCore atoms room low high outputAbove w₄ s3 s12 s13 s14 s15 result
  obtain ⟨ret, run, tag, store, done_, _, kept⟩ := Multiply.returnBlock fr out.values out.store ready
  have last : program.Exec (dialect Extracted.programImage) ⟨⟨.l10f12f, out.values, out.store⟩, []⟩ ret :=
    .done (by simp only [Program.step, run, Transfer.next])
  refine ⟨ret, Program.Exec.of_sem (path.exec last.sem), tag, store ▸ done_, ?_, store ▸ frame, store ▸ point⟩
  intro i hi
  have arg : i.val ∈ Activation.argumentNumbers := by
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  rw [kept i arg]
  exact widths i hi

end K256.Proofs.Signing.Generator
