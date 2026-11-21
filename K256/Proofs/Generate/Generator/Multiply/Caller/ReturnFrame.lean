import K256.Proofs.Generate.Generator.Multiply.Caller.CoreEntry
import K256.Proofs.Generate.Generator.Multiply.Loop.Execution

namespace K256.Proofs.Generate.Generator.Multiply.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
theorem afterCore {fr : Activation} {a : Registers} {m : Ram} {d : Nat}
    {out : Output Value Ram Reg.count}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 352 ≤ 2^32) (dst : fr.rdi = fr.rsp + 232)
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
  have destOff : fr.rdi.toNat = fr.rsp.toNat + 232 := by rw [dst]; exact Affine.add_toNat high 232 (by decide)
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

end K256.Proofs.Generate.Generator.Multiply.Caller
