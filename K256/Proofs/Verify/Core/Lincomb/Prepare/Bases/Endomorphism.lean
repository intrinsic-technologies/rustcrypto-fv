import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Endomorphism.Call
import K256.Proofs.Verify.Core.Lincomb.Prepare.TablePrefix
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Preserve

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

private theorem startEndomorphism {b : Registers} {m : Ram} {q src : BitVec 64}
    (rsp : b[4].get 64 = q) (source : b[10].get 64 = src) (push : Writable Extracted.programImage m (q-8) 8) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l10f69e,b,m⟩ =
      .call ⟨.l10e010,c,memStore m (q-8) (0x10f6ae : BitVec 64)⟩ (callResume .l10f6ae 0x10f6ae) ∧
      c[4] = ⟨64,q-8⟩ ∧ c[7] = ⟨64,q+0x100⟩ ∧ c[6] = ⟨64,src⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → c[i] = b[i] := by
  have guard : StoreOk Extracted.programImage m (q-8) 8 0x10f6a9 5 :=
    ParseSignature.storeOk_of_codeRange (off := 11) (len := 5) push
      (fun v hv => Common.fnCode_subset_programImage v (code_l10f69e v hv)) (by decide)
  refine ⟨?_, ?run, ?sp, ?di, ?si, ?keep⟩
  case run =>
    cfg_eval [rsp,source,guard]
    rfl
  case sp => rfl
  case di => rfl
  case si => rfl
  case keep =>
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

local macro "base_bounds" : tactic => `(tactic| (
  simp only [frameSp, scratch, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.reduceToNat, Nat.reduceDiv, Nat.reducePow] at *
  omega))

theorem applyEndomorphism {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {p : Projective} {k : Nat} (entry : RoutineEntry a m sp 0x558) (valid : p.valid)
    (point : p.Stored m src) (pointRead : Readable m src 120)
    (pointApart : Outside [scratch sp 0x558, ⟨digits.toNat, 544⟩] src 120)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (firstBase : FirstBase a m sp tables digits p.value k b n) (source : b[10].get 64 = src) :
    ∃ c o, Reaches .l10f69e b n .l10f6ae c o ∧ FirstBase a m sp tables digits p.value k c o ∧
      PointValueAt o (frameSp sp + 0x100) (endomorphism p.value) := by
  let q := frameSp sp
  let cs := q-8
  let push := memStore n cs (0x10f6ae : BitVec 64)
  have room := entry.room
  have high := entry.returnSlot.low
  have align := entry.aligned
  have stack := entry.stack.of_frame firstBase.frame
  have pushW : Writable Extracted.programImage n cs 8 := stack.sub
    (by dsimp only [cs,q]; base_bounds) (by dsimp only [cs,q]; base_bounds)
  obtain ⟨c,call,rsp,di,si,keep⟩ := startEndomorphism (q := q) (congrArg (Value.get 64) firstBase.rsp) source pushW
  let rs : List MemoryRegion := [scratch q 136,⟨(q+0x100).toNat,120⟩]
  have pf : RamWriteFrame n push rs := (RamWriteFrame.refl n rs).memStore _
    ⟨_,List.mem_cons_self .., by dsimp only [InRegion,cs,q]; base_bounds⟩
  have tag : memLoad push cs 64 = 0x10f6ae := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have cw : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64 := by
    intro i hi
    exact (congrArg Value.width (keep i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (firstBase.widths i hi)
  have control (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : c[i] = a[i] :=
    (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (firstBase.control i hi)
  have wide := stack.of_frame pf
  have ent : RoutineEntry c push cs 128 := by
    refine ⟨rsp,cw,(control 22 (by decide)).trans entry.df,
      (congrArg Value.width (control 39 (by decide))).trans entry.mxcsr,
      (congrArg Value.width (control 50 (by decide))).trans entry.ftw,
      (congrArg Value.width (control 51 (by decide))).trans entry.fcw,?_,?_,?_,
      pushW.readable.of_frame pf,by rw [tag]; decide,?_⟩
    · dsimp only [cs,q]; base_bounds
    · dsimp only [cs,q]; base_bounds
    · apply wide.sub <;> dsimp only [cs,q] <;> base_bounds
    · intro v hv
      have fw := firstBase.frame.trans pf (by
        intro r hr
        refine ⟨_,List.mem_cons_self ..,?_⟩
        simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> dsimp only [q] <;> base_bounds)
      refine (fw.outside v.1 ⟨by have := v.1.isLt; omega, fun r hr => ?_⟩).trans (entry.image v hv)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · have h := writableImage entry.stack v hv
        base_bounds
      · exact writableImage digitsWrite v hv
  have sourceHigh := pointRead.low
  have apart := pointApart.2 _ (List.mem_cons_self ..)
  change src.toNat + 120 ≤ sp.toNat - 1368 ∨ sp.toNat - 1368 + 1368 ≤ src.toNat at apart
  have srcSafe : Outside rs src 120 := by
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp only [q] <;> base_bounds
  obtain ⟨out,run,ret,value⟩ := endomorphismCall (src := src) (dst := q+0x100) ent di si ((pointRead.of_frame firstBase.frame).of_frame pf)
    (wide.sub (by dsimp only [q]; base_bounds) (by dsimp only [q]; base_bounds))
    (by dsimp only [cs,q]; base_bounds) (by dsimp only [cs,q]; base_bounds)
    (by dsimp only [cs,q]; base_bounds) valid ((point.of_frame firstBase.frame pointApart).of_frame pf srcSafe)
  have writes := pf.trans ret.frame (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,by dsimp only [q,cs]; base_bounds⟩
    · exact ⟨_,.tail _ (.head _),Nat.le_refl _,Nat.le_refl _⟩)
  have frame := signedFrameAfter entry firstBase.toSignedFrame digitsWrite digitsApart writes
    (by
      intro r hr
      simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> dsimp only [q] <;> base_bounds)
    (ret.rsp.trans (by dsimp only [cs]; rw [BitVec.sub_add_cancel]))
    ((ret.saved 3 (by decide)).trans (keep 3 (by decide)))
    (fun i hi => (congrArg Value.width (ret.saved i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (cw i hi))
    (fun i hi => (ret.saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
      (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)))
  have kept (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :=
    (ret.saved i hi).trans (keep i hi)
  obtain ⟨u,uv,ue,us⟩ := firstBase.point
  refine ⟨_,_,reachesCall call run (ret.tag.trans (congrArg (fun t => some (Value.mk 64 t)) tag)), ?_,value⟩
  refine ⟨frame,⟨u,uv,ue,us.of_frame writes ?_⟩,(writes.memLoad_eq ?_).trans firstBase.sign,
    (kept 5 (by decide)).trans firstBase.fold,(kept 12 (by decide)).trans firstBase.negTop,
    (kept 13 (by decide)).trans firstBase.negMiddle,(kept 14 (by decide)).trans firstBase.maskTop,
    (kept 15 (by decide)).trans firstBase.maskMiddle⟩
  all_goals
    refine ⟨by base_bounds, fun r hr => ?_⟩
    simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp only [q] <;> base_bounds

end K256.Proofs.Verify.Core.Lincomb.Prepare
