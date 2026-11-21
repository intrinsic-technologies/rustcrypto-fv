import K256.Proofs.Verify.Core.Affine.Equal
import K256.Proofs.Verify.Core.Affine.Serialize
import K256.Proofs.Verify.Core.Affine.Fill
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce
import K256.Proofs.Verify.Core.Scalars.Digest.Prepare

namespace K256.Proofs.Verify.Core.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 ParseSignature
open Generate.Generator.Multiply (scalarWords)

private def stageReduction (m : Ram) (sp : BitVec 64) : Ram :=
  let w := memStore m (sp + 32) (memLoad m (sp + 160) 64)
  let w := memStore w (sp + 24) (memLoad m (sp + 152) 64)
  let w := memStore w (sp + 16) (memLoad m (sp + 144) 64)
  let w := memStore w (sp + 8) (memLoad m (sp + 136) 64)
  memStore w (sp - 8) (0x105357 : BitVec 64)

private theorem stagedWords {m : Ram} {sp : BitVec 64} {v : Vector (BitVec 64) 4}
    (words : WordsAt m (sp + 136) 64 v) : WordsAt (stageReduction m sp) (sp + 8) 64 v := by
  intro i hi
  rw [← words i hi]
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals simp (disch := store_disch) only [stageReduction, wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    memLoad_memStore_same, memLoad_memStore_of_rangeApart]

set_option maxRecDepth 4096 in
private theorem prepareReduction {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (stack : Writable Extracted.programImage m (sp - 8) 176) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10530e,a,m⟩ =
        .call ⟨.l109f80,b,stageReduction m sp⟩ ⟨.l105357,#v[],rfl,some ⟨64,0x105357⟩⟩ ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[6] = ⟨64, sp + 8⟩ ∧ b[7] = ⟨64, sp + 136⟩ ∧
      b[14] = ⟨64, sp + 136⟩ ∧ b[1].width = 64 ∧
      ∀ i : Fin Reg.count, i.val ∈ [2,3,5,8,9,12,13,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?args, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using (fun x hx => coreText x (code_l10530e x hx)))
    simp (disch := store_disch) only [stageReduction, memLoad_memStore_of_rangeApart] <;> rfl
  case regs =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def reductionActivation (fr : Activation) (args : Registers) (m : Ram) : Activation :=
  { fr with
    original := stageReduction m (localSp fr), rsp := localSp fr - 8, low := localSp fr - 105,
    ret := 0x105357, rbx := fr.rdi, r12 := args[12].get 64, r13 := args[13].get 64,
    r14 := localSp fr + 136, r15 := localSp fr + 320, rdi := localSp fr + 136, rsi := localSp fr + 8,
    rdx := args[2].get 64, rcx := args[1].get 64, r8 := args[8].get 64, r9 := args[9].get 64 }

private def reductionWrites (fr : Activation) : List MemoryRegion :=
  [buffer (localSp fr - 105) 145, buffer (localSp fr + 136) 32]

private theorem width64 {v : Value} (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  obtain ⟨w,z⟩ := v
  change w = 64 at h
  subst w
  rfl

local macro "reduction_bounds" : tactic => `(tactic|
  (simp only [localSp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow] at *
   omega))

theorem reduceX {fr : Activation} {a b : Registers} {p : Curve.Point}
    {digest : ByteArray} {r s x : Nat} {m : Ram} (e : Entry fr a p digest r s)
    (h : Phase fr b m) (ptr : b[15] = ⟨64, localSp fr + 320⟩)
    (w12 : b[12].width = 64) (w13 : b[13].width = 64) (widths : ArgumentWidths b)
    (hx : WordsAt m (localSp fr + 136) 64 (scalarWords x)) (bound : x < 2^256)
    (hr : WordsAt m (localSp fr + 256) 64 (scalarWords r)) :
    ∃ c n, Reaches .l10530e b m .l105357 c n ∧ Phase fr c n ∧
      c[14] = ⟨64,localSp fr + 136⟩ ∧
      WordsAt n (localSp fr + 136) 64 (scalarWords (x % domain.n)) ∧
      WordsAt n (localSp fr + 256) 64 (scalarWords r) := by
  have room := e.stackRoom
  have upper := e.low
  have bottom := e.low_toNat
  have area := e.stack.of_frame h.frame
  have stack : Writable Extracted.programImage m (localSp fr - 8) 176 :=
    area.sub (by reduction_bounds) (by reduction_bounds)
  obtain ⟨args,call,sp,src,dst,r14,cx,keep⟩ := prepareReduction (congrArg (Value.get 64) h.sp) stack
  let ch := reductionActivation fr args m
  have staged : RamWriteFrame m ch.original (reductionWrites fr) := by
    have slot (d : BitVec 64) (offset : d.toNat ≤ 32) : InRegions (reductionWrites fr) (localSp fr + d) 8 := by
      refine ⟨_, List.mem_cons_self, ?_⟩
      change (localSp fr - 105).toNat ≤ _ ∧ _ + 8 ≤ (localSp fr - 105).toNat + 145 ∧ _
      reduction_bounds
    have push : InRegions (reductionWrites fr) (localSp fr - 8) 8 := by
      refine ⟨_, List.mem_cons_self, ?_⟩
      change (localSp fr - 105).toNat ≤ _ ∧ _ + 8 ≤ (localSp fr - 105).toNat + 145 ∧ _
      reduction_bounds
    change RamWriteFrame m (stageReduction m (localSp fr)) _
    unfold stageReduction
    apply RamWriteFrame.memStore _ _ push
    repeat' apply RamWriteFrame.memStore _ _ (slot _ (by decide))
    exact .refl _ _
  have stageArea := area.of_frame staged
  have ea := e.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at ea
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,align,_⟩ := ea
  have arg (i : Fin Reg.count) (hi : i.val ∈ [2,8,9]) : args[i] = ⟨64, args[i].get 64⟩ := by
    apply width64
    rw [keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
    apply widths
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  have entry : Atom.All Extracted.programImage args ch.original (Fn109f80.frameAt .l109f80 ch) := by
    simp only [Fn109f80.frameAt, Fn109f80.frameAtG11, Atom.All, Atom.Holds]
    refine ⟨sp,(keep 22 (by decide)).trans h.df,width64 cx,arg 2 (by decide),
      (keep 3 (by decide)).trans h.dst,(keep 5 (by decide)).trans h.rbp,src,dst,arg 8 (by decide),
      arg 9 (by decide),width64 ((congrArg Value.width (keep 12 (by decide))).trans w12),
      width64 ((congrArg Value.width (keep 13 (by decide))).trans w13),r14,
      (keep 15 (by decide)).trans ptr,(keep 39 (by decide)).trans h.mxcsr,
      (keep 50 (by decide)).trans h.ftw,(keep 51 (by decide)).trans h.fcw,?_,?_,
      (by change (0x105357 : Nat) < 2^32; decide),?_,?_,?_,trivial⟩
    · apply stageArea.readable.sub <;> dsimp only [ch,reductionActivation] <;> reduction_bounds
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · apply stageArea.sub <;> dsimp only [ch,reductionActivation] <;> reduction_bounds
    · dsimp only [ch,reductionActivation]; reduction_bounds
    · change fr.rsp.toNat % 16 = 8 at align
      dsimp only [ch,reductionActivation]; reduction_bounds
  have atSrc : Readable ch.original ch.rsi 32 := by
    apply stageArea.readable.sub <;> dsimp only [ch,reductionActivation] <;> reduction_bounds
  have atDst : Writable Extracted.programImage ch.original ch.rdi 32 := by
    apply stageArea.sub <;> dsimp only [ch,reductionActivation] <;> reduction_bounds
  have apart (off : BitVec 64) (offset : off.toNat ≤ 136) : Outside [callStack ch] (localSp fr + off) 32 := by
    refine ⟨by reduction_bounds, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only [callStack,ch,reductionActivation]
    reduction_bounds
  obtain ⟨out,run,tag,done,writes,reduced,_⟩ := reduceScalar entry atSrc atDst
    (apart 8 (by decide)) (apart 136 (by decide)) (stagedWords hx) bound
  have delta := staged.trans writes (by
    intro reg hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl
    · refine ⟨_, List.mem_cons_self, Nat.le_refl _, ?_⟩
      dsimp only [Activation.region,buffer,ch,reductionActivation]
      reduction_bounds
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
  have keepR : Outside (reductionWrites fr) (localSp fr + 256) 32 := by
    refine ⟨by reduction_bounds, fun reg hreg => ?_⟩
    simp only [reductionWrites,List.mem_cons,List.not_mem_nil,or_false] at hreg
    rcases hreg with rfl | rfl <;> right <;> dsimp only [buffer] <;> reduction_bounds
  have within : ∀ reg ∈ reductionWrites fr, fr.low.toNat ≤ reg.start ∧ reg.start + reg.size ≤ fr.rsp.toNat - 40 := by
    intro reg hreg
    simp only [reductionWrites,List.mem_cons,List.not_mem_nil,or_false] at hreg
    rcases hreg with rfl | rfl <;> dsimp only [buffer] <;> reduction_bounds
  simp only [Fn109f80.doneAt,Atom.All,Atom.Holds,ch,reductionActivation] at done
  obtain ⟨rsp,df,rbx,rbp,_,_,ptr,_,mxcsr,ftw,fcw,_⟩ := done
  rw [BitVec.sub_add_cancel] at rsp
  refine ⟨out.values,out.store,resumeCoreCall call run tag,
    phaseFrame e h rsp rbx rbp df mxcsr ftw fcw delta within,ptr,reduced,
    hr.of_frame delta (by decide) keepR⟩

end K256.Proofs.Verify.Core.Affine

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

theorem comparePath (e : Entry fr a p digest r s) {b m point} (h : PointResult fr b m point r) :
    ∃ c n, Reaches .l10526c b m (if Nat.mod (affineX point) domain.n = r then .l10536b else .l10536f) c n ∧
      Phase fr c n := by
  obtain ⟨c,n,converted,phase,ptr,xAt,rAt⟩ := Affine.affinePath e h
  have bound : affineX point < 2^256 := by
    obtain ⟨x,_,_,_,value⟩ := xAt
    rw [show affineX point = x.val from value.symm]
    exact Nat.lt_trans x.isLt (by decide +kernel)
  obtain ⟨d,o,serialized,phase,ptr,w9,w12,w13,w14,bytes,rAt⟩ :=
    serializeX e phase ptr xAt rAt
  have decoded : ParseSignature.scalarValue o (localSp fr + 320) = affineX point :=
    Affine.scalarValue_of_octets bytes bound
  obtain ⟨f,q,filled,phase,ptr,w12,w13,widths,limbs,rAt⟩ :=
    Affine.fillX e phase ptr w9 w12 w13 w14 decoded rAt
  obtain ⟨g,t,reduced,phase,ptr,limbs,rAt⟩ :=
    Affine.reduceX e phase ptr w12 w13 widths limbs bound rAt
  obtain ⟨k,u,compared,phase⟩ :=
    compareScalars e phase ptr limbs rAt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) bound)
  exact ⟨k,u,converted.trans (serialized.trans (filled.trans (reduced.trans compared))),phase⟩

end K256.Proofs.Verify.Core
