import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Shift.Entry
import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Shift.Masks
import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Shift.Finish

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

local macro "shift_addr" : tactic => `(tactic|
  (simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
   omega))

theorem DigestShift.Saved.of_scratch {base : BitVec 64} {a : Verify.Core.Registers} {p q : Ram}
    {returnTag : BitVec 64} (saved : DigestShift.Saved base a p returnTag) (before : base.toNat + 216 ≤ 2^32)
    (scratch : RamWriteFrame p q [⟨base.toNat, 24⟩]) : DigestShift.Saved base a q returnTag := by
  have slot (k : BitVec 64) (lo : 24 ≤ k.toNat) (hi : k.toNat ≤ 72) :
      memLoad q (base + k) 64 = memLoad p (base + k) 64 := by
    apply scratch.memLoad_eq
    refine ⟨?_, ?_⟩
    · simp only [BitVec.toNat_add, Nat.reducePow, Nat.reduceDiv]; omega
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      right
      simp only [BitVec.toNat_add, Nat.reducePow]; omega
  exact ⟨(slot 24 (by decide) (by decide)).trans saved.bx,
    (slot 32 (by decide) (by decide)).trans saved.r12,
    (slot 40 (by decide) (by decide)).trans saved.r13,
    (slot 48 (by decide) (by decide)).trans saved.r14,
    (slot 56 (by decide) (by decide)).trans saved.r15,
    (slot 64 (by decide) (by decide)).trans saved.bp,
    (slot 72 (by decide) (by decide)).trans saved.ret⟩

private theorem savedLoad {rsp offset : BitVec 64} {m n : Ram}
    (depth : 360 ≤ rsp.toNat) (limit : rsp.toNat + 8 ≤ 2^64)
    (wf : RamWriteFrame m n (DigestShift.footprint (rsp - 360))) (off : offset.toNat ≤ 112) :
    memLoad n (rsp - offset) 64 = memLoad m (rsp - offset) 64 := by
  apply wf.memLoad_eq
  simp only [Outside,DigestShift.footprint,List.mem_singleton,forall_eq,Nat.reduceDiv]
  shift_addr

private theorem imageLoad {rsp addr : BitVec 64} {m n : Ram}
    (depth : 360 ≤ rsp.toNat)
    (wf : RamWriteFrame m n (DigestShift.footprint (rsp - 360)))
    (apart : 0x2046c8 ≤ rsp.toNat ∨ rsp.toNat ≤ 0x203dc8)
    (range : 0x203dc8 ≤ addr.toNat ∧ addr.toNat ≤ 0x203e20) :
    memLoad n addr 64 = memLoad m addr 64 := by
  apply wf.memLoad_eq
  simp only [Outside,DigestShift.footprint,List.mem_singleton,forall_eq,Nat.reduceDiv]
  shift_addr

theorem shiftSeedDigest {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x : Nat}
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32) (filled : FilledDigest fr a m x) :
    ∃ b n, Verify.Core.Reaches .l101072 a m .l1010ae b n ∧ DigestLimbs fr b n x := by
  let base := fr.rsp - 360
  have atoms := filled.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp,df,r12,mx,ft,fc,s9,s2,s6,s7,s3,s12,s13,s14,s15,s5,rr,ret,retLow,
    stack,room,align,g0,v0,g1,v1,g2,v2,g3,v3,g4,v4,apart,_⟩ := atoms
  have area : Writable Extracted.programImage m base 216 := by
    apply stack.sub <;> dsimp only [base] <;> shift_addr
  have spEq : base + 80 = fr.rsp - 280 := by dsimp only [base]; bv_omega
  have inEq : base + 184 = fr.rsp - 176 := by dsimp only [base]; bv_omega
  have outEq : base + 88 = fr.rsp - 272 := by dsimp only [base]; bv_omega
  obtain ⟨b,n,c,p,call,firstStep,stage,saved,words,csp,src,dst,shift,flags₁⟩ :=
    DigestShift.enter area (spEq.symm ▸ congrArg (Value.get 64) sp) filled.shift
      (inEq.symm ▸ filled.words)
  obtain ⟨z,q,secondStep,masks,zsp,dest,flags₂,scratch⟩ :=
    DigestShift.computeMasks (area.of_frame stage) words csp src dst shift
  have saves := saved.of_scratch area.readable.low scratch
  obtain ⟨out,run,tag,finalWrites,result,osp,regs,flags₃,widths⟩ :=
    DigestShift.finish ((area.of_frame stage).of_frame scratch) zsp masks dest saves
  have reaches := Verify.reachesOfCall call (Program.Exec.of_sem ((firstStep.trans secondStep).exec run.sem)) tag
  have whole := (stage.trans scratch (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_,List.mem_singleton_self _,Nat.le_refl _,Nat.add_le_add_left (by decide : 24 ≤ 184) _⟩)).trans
    finalWrites (fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have within : RegionsWithin (DigestShift.footprint base) [fr.region] := by
    intro r hr
    simp only [DigestShift.footprint,List.mem_singleton] at hr
    subst r
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;>
      simp only [Activation.region,low,base] <;> shift_addr
  have big : fr.rsp.toNat + 8 ≤ 2^64 := by omega
  have room' : 360 ≤ fr.rsp.toNat := by omega
  have keep (off : BitVec 64) (h : off.toNat ≤ 112) :=
    savedLoad room' big whole h
  have keepImage (addr : BitVec 64) (d : 0x203dc8 ≤ addr.toNat ∧ addr.toNat ≤ 0x203e20) :=
    imageLoad room' whole apart d
  have flag (i : Fin Reg.count) (h : i.val ∈ [22,39,50,51]) :
      out.values[i] = a[i] := (flags₃ i h).trans ((flags₂ i h).trans (flags₁ i h))
  refine ⟨_,_,reaches,⟨⟨?_,filled.writes.trans whole within⟩,?_,outEq ▸ result,widths⟩⟩
  · simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds]
    refine ⟨spEq ▸ osp,(flag 22 (by decide)).trans df,?_,(flag 39 (by decide)).trans mx,
      (flag 50 (by decide)).trans ft,(flag 51 (by decide)).trans fc,
      ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rr.of_frame whole,?_,retLow,stack.of_frame whole,room,align,
      g0.of_frame whole,?_,g1.of_frame whole,?_,g2.of_frame whole,?_,g3.of_frame whole,?_,
      g4.of_frame whole,?_,apart,trivial⟩
    · rw [regs 12 (by decide), r12]; rfl
    · exact (keep 112 (by decide)).trans s9
    · exact (keep 104 (by decide)).trans s2
    · exact (keep 96 (by decide)).trans s6
    · exact (keep 88 (by decide)).trans s7
    · exact (keep 48 (by decide)).trans s3
    · exact (keep 40 (by decide)).trans s12
    · exact (keep 32 (by decide)).trans s13
    · exact (keep 24 (by decide)).trans s14
    · exact (keep 16 (by decide)).trans s15
    · exact (keep 8 (by decide)).trans s5
    · have h := keep 0 (by decide)
      rw [show fr.rsp - 0 = fr.rsp by bv_omega] at h
      exact h.trans ret
    all_goals apply (keepImage _ (by decide)).trans; assumption
  · obtain ⟨w0,w1,w2,w3⟩ := filled.toOrderRegisters
    constructor
    · exact (regs 15 (by decide)).trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) w0)
    · exact (regs 14 (by decide)).trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) w1)
    · exact (regs 13 (by decide)).trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) w2)
    · exact (regs 3 (by decide)).trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) w3)

end K256.Proofs.Signing.Nonce.Initialize
