import K256.Proofs.Sec1.Affine.Compressed.SqrtEntry

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

theorem sqrtResume {code : CodeMap} {fr : Activation} {args next : Values Value Reg.count}
    {mem m : Ram} {v : Inputs} {want : BitVec 8} (entry : CubeReady code fr args mem v want)
    (cube : CubePost args next mem m (workSP fr) v.masked v.valid)
    (out : Output Value Ram Reg.count)
    (doneAt : Atom.All code out.values out.store (Fn115950.doneAt (sqrtActivation fr next m)))
    (writes : RamWriteFrame m out.store [(sqrtActivation fr next m).region,⟨(workSP fr + 304).toNat,41⟩]) :
    BodyAt code fr out.values out.store v.masked v.valid want ∧
    (∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15] → out.values[i] = ⟨64,out.values[i].get 64⟩) ∧
    RamWriteFrame mem out.store [fr.region] := by
  have frame := entry.atoms
  simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds] at frame
  obtain ⟨_,_,_,_,_,di,bx,r12,r13,r14,r15,bp,slot,ret,low,stack,room,align,_⟩ := frame
  change fr.low.toNat + 1048 ≤ fr.rsp.toNat at room
  simp only [Fn115950.doneAt,sqrtActivation,Atom.All,Atom.Holds] at doneAt
  obtain ⟨sp,df,obx,obp,o12,o13,o14,o15,mx,ft,fc,_⟩ := doneAt
  have addr (n : Nat) (h : n ≤ 1048) := stackOffset (fr := fr) (by omega) n h
  have lowN : (fr.rsp - 1048).toNat = fr.rsp.toNat - 1048 := addr 1048 (by decide)
  have spN : (workSP fr - 8).toNat = fr.rsp.toNat - 496 := by
    rw [show workSP fr - 8 = fr.rsp - 496 by unfold workSP; bv_omega]; exact addr 496 (by decide)
  have addN (off : Nat) (h : off ≤ 488) :
      (workSP fr + BitVec.ofNat 64 off).toNat = fr.rsp.toNat - 488 + off := by
    have o : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
    have base : (workSP fr).toNat = fr.rsp.toNat - 488 := addr 488 (by decide)
    rw [BitVec.toNat_add_of_lt,base,o]
    have := slot.low
    omega
  have dstN : (workSP fr + 304).toNat = fr.rsp.toNat - 184 := by
    have a := addN 304 (by decide)
    change (workSP fr + 304).toNat = _ at a
    omega
  have cubeWithin : RegionsWithin [⟨(workSP fr - 8).toNat,192⟩] [fr.region] := by
    intro r h
    obtain rfl := List.mem_singleton.mp h
    exact ⟨fr.region,by simp,by simp only [Activation.region]; omega,by simp only [Activation.region]; omega⟩
  have sqWithin : RegionsWithin [(sqrtActivation fr next m).region,⟨(workSP fr + 304).toNat,41⟩] [fr.region] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;>
      exact ⟨fr.region,by simp,by simp only [Activation.region,sqrtActivation]; omega,
        by simp only [Activation.region,sqrtActivation]; omega⟩
  have total := ((RamWriteFrame.refl mem [fr.region]).trans cube.frame cubeWithin).trans writes sqWithin
  have saved (off : Nat) (h : off ≤ 48) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 off) 64 = memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 := by
    have no := addr off (by omega)
    have upper := slot.low
    have a := writes.memLoad_eq (a := fr.rsp - BitVec.ofNat 64 off) (k := 64) (by
      refine ⟨by omega,fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> right <;> simp only [Activation.region,sqrtActivation] <;> omega)
    apply a.trans
    apply cube.frame.memLoad_eq
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right; change (workSP fr - 8).toNat + 192 ≤ _; omega
  have localRead (off width : Nat) (h : off + width/8 ≤ 304) :
      memLoad out.store (workSP fr + BitVec.ofNat 64 off) width =
      memLoad m (workSP fr + BitVec.ofNat 64 off) width := by
    have no := addN off (by omega)
    have upper := slot.low
    apply writes.memLoad_eq
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · right; simp only [Activation.region,sqrtActivation]; omega
    · left; change _ ≤ (workSP fr + 304).toNat; omega
  have outputAddr : workSP fr + 136 = fr.rsp - 352 := by unfold workSP; bv_omega
  have sdi := ((localRead 136 64 (by decide)).trans cube.output)
  change memLoad out.store (workSP fr + 136) 64 = memLoad mem (workSP fr + 136) 64 at sdi
  rw [outputAddr] at sdi
  have top := saved 0 (by decide)
  change memLoad out.store (fr.rsp-0) 64 = memLoad mem (fr.rsp-0) 64 at top
  rw [show fr.rsp - 0 = fr.rsp from BitVec.sub_zero _] at top
  refine ⟨⟨?_,entry.output.of_frame total,?_,(localRead 128 64 (by decide)).trans cube.flag,
    (localRead 108 8 (by decide)).trans (cube.parity.trans entry.parity)⟩,?_,total⟩
  · simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds]
    rw [show workSP fr - 8 + 8 = fr.rsp - 488 by unfold workSP; bv_omega] at sp
    exact ⟨sp,df,mx,ft,fc,sdi.trans di,(saved 48 (by decide)).trans bx,(saved 40 (by decide)).trans r12,
      (saved 32 (by decide)).trans r13,(saved 24 (by decide)).trans r14,(saved 16 (by decide)).trans r15,
      (saved 8 (by decide)).trans bp,slot.of_frame total,top.trans ret,low,stack.of_frame total,room,align,trivial⟩
  · rw [← cube.x]
    have h80 : memLoad out.store (workSP fr + 80) 64 = memLoad m (workSP fr + 80) 64 := localRead 80 64 (by decide)
    have h88 : memLoad out.store (workSP fr + 88) 64 = memLoad m (workSP fr + 88) 64 := localRead 88 64 (by decide)
    have h64 : memLoad out.store (workSP fr + 64) 64 = memLoad m (workSP fr + 64) 64 := localRead 64 64 (by decide)
    have h48 : memLoad out.store (workSP fr + 48) 64 = memLoad m (workSP fr + 48) 64 := localRead 48 64 (by decide)
    have h72 : memLoad out.store (workSP fr + 72) 64 = memLoad m (workSP fr + 72) 64 := localRead 72 64 (by decide)
    simp only [savedX,h80,h88,h64,h48,h72]
  · intro i hi
    have indices : i = 3 ∨ i = 5 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
    rcases indices with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rw [obx] | rw [obp] | rw [o12] | rw [o13] | rw [o14] | rw [o15]
    all_goals rfl

end K256.Proofs.Sec1.Affine.Compressed
