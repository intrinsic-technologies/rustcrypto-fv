import K256.Proofs.Verify.Core.Lincomb.Double
import K256.Proofs.Verify.Core.Lincomb.Prepare.TablePrefix
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Preserve

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

private theorem firstDoubleCall {b : Registers} {m : Ram} {q : BitVec 64}
    (rsp : b[4].get 64 = q) (push : Writable Extracted.programImage m (q-8) 8) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l10f812,b,m⟩ =
      .call ⟨.l110cd0,c,memStore m (q-8) (0x10f82a : BitVec 64)⟩ (callResume .l10f82a 0x10f82a) ∧
      c[4] = ⟨64,q-8⟩ ∧ c[7] = ⟨64,q+0x38⟩ ∧ c[6] = ⟨64,q+0x178⟩ ∧
      c[14] = ⟨64,q+0x178⟩ ∧ c[15] = ⟨64,q+0x38⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,22,39,50,51] → c[i] = b[i] := by
  have guard : StoreOk Extracted.programImage m (q-8) 8 0x10f825 5 := ParseSignature.storeOk_of_codeRange (off := 19) (len := 5) push
    (fun v hv => Common.fnCode_subset_programImage v (code_l10f812 v hv)) (by decide)
  refine ⟨?_, ?run, ?sp, ?di, ?si, ?acc, ?delta, ?keep⟩
  case run =>
    cfg_eval [rsp,guard]
    rfl
  case sp => rfl
  case di => rfl
  case si => rfl
  case acc => rfl
  case delta => rfl
  case keep =>
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

local macro "base_bounds" : tactic => `(tactic| (
  simp only [frameSp, scratch, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.reduceToNat, Nat.reduceDiv, Nat.reducePow] at *
  omega))

theorem doubleFirstBase {a b : Registers} {m n : Ram} {sp tables digits : BitVec 64}
    {p : Curve.Point} {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (pair : SignedPair a m sp tables digits p k b n) :
    ∃ c o, Reaches .l10f812 b n .l10f82a c o ∧ Bases a m sp tables digits p k c o := by
  let q := frameSp sp
  let cs := q-8
  let push := memStore n cs (0x10f82a : BitVec 64)
  have room := entry.room
  have high := entry.returnSlot.low
  have align := entry.aligned
  have stack := entry.stack.of_frame pair.frame
  have pushW : Writable Extracted.programImage n cs 8 := stack.sub
    (by dsimp only [cs,q]; base_bounds) (by dsimp only [cs,q]; base_bounds)
  obtain ⟨c,call,rsp,di,si,acc,delta,keep⟩ := firstDoubleCall (q := q) (congrArg (Value.get 64) pair.rsp) pushW
  let rs : List MemoryRegion := [scratch q 672,⟨(q+0x38).toNat,120⟩]
  have pf : RamWriteFrame n push rs := (RamWriteFrame.refl n rs).memStore _
    ⟨_,List.mem_cons_self .., by dsimp only [InRegion,cs,q]; base_bounds⟩
  have tag : memLoad push cs 64 = 0x10f82a := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have cw : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64 := by
    rintro ⟨i,ih⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact congrArg Value.width acc | exact congrArg Value.width delta |
      exact (congrArg Value.width (keep _ (by decide +revert))).trans (pair.widths _ (by decide +revert))
  have control (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : c[i] = a[i] :=
    (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (pair.control i hi)
  have wide := stack.of_frame pf
  have ent : RoutineEntry c push cs 0x298 := by
    refine ⟨rsp,cw,(control 22 (by decide)).trans entry.df,
      (congrArg Value.width (control 39 (by decide))).trans entry.mxcsr,
      (congrArg Value.width (control 50 (by decide))).trans entry.ftw,
      (congrArg Value.width (control 51 (by decide))).trans entry.fcw,?_,?_,?_,
      pushW.readable.of_frame pf,by rw [tag]; decide,?_⟩
    · dsimp only [cs,q]; base_bounds
    · dsimp only [cs,q]; base_bounds
    · apply wide.sub <;> dsimp only [cs,q] <;> base_bounds
    · intro v hv
      have fw := pair.frame.trans pf (by
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
  have safe {off : BitVec 64} (h₁ : 0xb0 ≤ off.toNat) (h₂ : off.toNat ≤ 0x1f0) :
      Outside rs (q+off) 120 := by
    refine ⟨by dsimp only [q]; base_bounds, fun r hr => ?_⟩
    simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp only [q] <;> base_bounds
  obtain ⟨p₁,v₁,e₁,s₁⟩ := pair.firstPoint
  obtain ⟨p₂,v₂,e₂,s₂⟩ := pair.secondPoint
  obtain ⟨out,run,ret,args,stored⟩ := Lincomb.doubleWithWidths (dst := q+0x38) (src := q+0x178) ent (congrArg (Value.get 64) di)
    (congrArg (Value.get 64) si) (wide.readable.sub (by dsimp only [q]; base_bounds) (by dsimp only [q]; base_bounds))
    (wide.sub (by dsimp only [q]; base_bounds) (by dsimp only [q]; base_bounds))
    (by
      refine ⟨by dsimp only [q]; base_bounds, fun r hr => ?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> dsimp only [cs,q] <;> base_bounds)
    (by
      refine ⟨by dsimp only [q]; base_bounds, fun r hr => ?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> dsimp only [cs,q] <;> base_bounds)
    (s₁.of_frame pf (safe (by decide) (by decide))) v₁
  have writes := pf.trans ret.frame (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,by dsimp only [q,cs]; base_bounds⟩
    · exact ⟨_,.tail _ (.head _),Nat.le_refl _,Nat.le_refl _⟩)
  have frame := signedFrameAfter entry pair.toSignedFrame digitsWrite digitsApart writes
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
  exact ⟨_,_,reachesCall call run (ret.tag.trans (congrArg (fun t => some (Value.mk 64 t)) tag)),
    frame.toSavedFrame,frame.frame,args,(ret.saved 14 (by decide)).trans acc,(ret.saved 15 (by decide)).trans delta,
    ⟨p₁,v₁,e₁,s₁.of_frame writes (safe (by decide) (by decide)),stored⟩,
    ⟨p₂,v₂,e₂,s₂.of_frame writes (safe (by decide) (by decide))⟩,
    frame.firstLength,frame.secondLength,frame.firstBytes,frame.secondBytes⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
