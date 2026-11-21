import K256.Proofs.Sec1.Affine.Uncompressed.Decode
import K256.Proofs.Ecdh.Decode.Repr

namespace K256.Proofs.Verify.Transfer.PublicKey

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR K256.Proofs.Sec1.Affine.Uncompressed


private theorem remainingExec {Op : Nat → Type} {Label Value Store : Type} {signature : Label → Nat} {r}
    {p : Program Op Label signature r} {d : Dialect Op Value Store} {a b out}
    (path : (p.sem d).Reaches a b) (run : p.Exec d a out) : p.Exec d b out := by
  induction path with
  | refl => exact run
  | step h _ ih =>
    change p.step d _ = .next _ at h
    cases run with
    | done e => simp only [h, reduceCtorEq] at e
    | next e tail => cases h.symm.trans e; exact ih tail

private theorem withoutGuard {code : CodeMap} {p : Prop} [Decidable p]
    {t : Transfer Value Ram Label signature Reg.count} {o : Outcome Value Ram Label signature Reg.count}
    (h : (if p then t else .stuck).next (dialect code) [] = o) (live : o ≠ .stuck) :
    t.next (dialect code) [] = o := by
  split at h
  · exact h
  · exact (live h.symm).elim

set_option maxRecDepth 2048 in
private theorem returnStore {code : CodeMap} {args : Values Value Reg.count} {mem dst out}
    (rbx : args[3].get 64 = dst)
    (run : program.Exec (dialect code) ⟨⟨.l120330,args,mem⟩,[]⟩ out) :
    out.store = memStore mem (dst+88) ((args[0].get 64).setWidth 8) := by
  cases run with
  | done h =>
    change (program.runBlock _ ⟨.l120330,args,mem⟩).next _ [] = .done out at h
    cfg_eval [rbx] at h
    repeat' replace h := withoutGuard h (by intro impossible; cases impossible)
    simp only [Transfer.next, Outcome.done.injEq] at h
    subst out
    rfl
  | next h _ =>
    change (program.runBlock _ ⟨.l120330,args,mem⟩).next _ [] = .next _ at h
    cfg_eval [rbx] at h
    repeat' replace h := withoutGuard h (by intro impossible; cases impossible)
    simp only [Transfer.next, reduceCtorEq] at h

private def scratch (base : Word) : Prelude.MemoryRegion := ⟨(base-9).toNat,9⟩

private theorem slotWithin {base : Word} (room : 9 ≤ base.toNat) :
    InRegions [scratch base] (base-8) 8 := by
  refine ⟨_,List.mem_cons_self,?_⟩
  change (base-9).toNat ≤ (base-8).toNat ∧ (base-8).toNat+8 ≤ (base-9).toNat+9 ∧ _
  bv_omega

private theorem pushChoice {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code)
    {caller : Location Value Ram Label signature} {target : Label} {ret base : Word}
    {args : Values Value Reg.count} {m : Ram}
    (step : program.runBlock (dialect code) caller =
      .call ⟨.l127d50,args,memStore m (base-8) ret⟩ (choiceResume target ret rfl))
    (rsp : args[4].get 64 = base-8) (win : Writable code m (base-9) 9)
    (room : 9 ≤ base.toNat) (low : ret.toNat < 2^32) :
    ∃ (regs : Values Value Reg.count) (after : Ram),
      (program.sem (dialect code)).Reaches ⟨caller,[]⟩ ⟨⟨target,regs,after⟩,[]⟩ ∧
      regs[4] = ⟨64,base⟩ ∧ regs[0] = ⟨64,((args[7].get 64).setWidth 8).setWidth 64⟩ ∧
      RamWriteFrame m after [scratch base] ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        regs[i] = args[i] := by
  obtain ⟨regs,after,exec,stack,rax,frame,kept⟩ :=
    resumeChoice cover step rsp (win.memStore _ ret)
      (memLoad_memStore_same _ _ _ (by decide) (by decide)) low
  have hf := (RamWriteFrame.refl m _).memStore ret (slotWithin room)
  refine ⟨regs,after,exec,stack,rax,hf.trans frame ?_,kept⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_cons_self, Nat.le_refl _, by change (base-9).toNat + 1 ≤ (base-9).toNat + 9; omega⟩

private theorem outputOutside {base dst : Word} (g : EmitGeometry base dst)
    (off n : Nat) (h : off+n ≤ 88) :
    Outside [scratch base] (dst+BitVec.ofNat 64 off) n := by
  have e : (dst+BitVec.ofNat 64 off).toNat = dst.toNat+off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := g.dstLow; omega
  have er : (base-9).toNat + 9 = base.toNat := by have := g.room; bv_omega
  refine ⟨by rw [e]; have := g.dstLow; omega, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  change _ ≤ (base-9).toNat ∨ (base-9).toNat + 9 ≤ _
  rw [e, er]
  have := g.apart
  omega

private theorem emittedPayload {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code)
    (args : Values Value Reg.count) (m : Ram) (base dst : Word)
    (g : EmitGeometry base dst) (rsp : args[4].get 64 = base)
    (pointer : memLoad m (base+208) 64 = dst)
    (stack : Writable code m (base-9) 225) (outW : Writable code m dst 89)
    {out} (run : program.Exec (dialect code) ⟨⟨.l120298,args,m⟩,[]⟩ out) :
    ∀ off width : Nat, off + width / 8 ≤ 88 →
      memLoad out.store (dst + BitVec.ofNat 64 off) width =
        memLoad (pointMemory base dst m) (dst + BitVec.ofNat 64 off) width := by
  have coverCopy := fun e he => cover e (code_l120298 e he)
  have win := stack.sub (n := 9) (Nat.le_refl _) (by omega)
  obtain ⟨r₁,step₁,rbx₁,rsp₁,arg₁,keep₁⟩ := copyPoint code args m base dst rsp pointer
    (stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) outW coverCopy
  obtain ⟨r₂,m₂,run₂,rsp₂,rax₂,f₂,k₂⟩ := pushChoice cover step₁ rsp₁ (win.of_frame (pointMemory_frame base dst m g.dstLow)) g.room (by decide)
  have stack₂ := (stack.of_frame (pointMemory_frame base dst m g.dstLow)).of_frame f₂
  have push : StoreOk code m₂ (base-8) 8 0x12032b 5 :=
    ParseSignature.storeOk_of_codeRange (off := 13)
      (stack₂.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (fun e he => cover e (code_l12031e e he)) (by decide +kernel)
  obtain ⟨r₃,step₃,rsp₃,arg₃,keep₃⟩ := finalChoice code r₂ m₂ base (by rw [rsp₂]; rfl)
    (LoadOk.of_offsets stack₂.readable rfl (addr_sub _ _) (by decide)) push
  obtain ⟨r₄,m₄,run₄,rsp₄,rax₄,f₄,k₄⟩ := pushChoice cover step₃ rsp₃ (stack₂.sub (Nat.le_refl _) (by omega)) g.room (by decide)
  have rbx₄ : r₄[3].get 64 = dst := by
    exact (congrArg (Value.get 64) ((k₄ 3 (by decide)).trans ((keep₃ 3 (by decide)).trans (k₂ 3 (by decide))))).trans rbx₁
  have memEq := returnStore rbx₄ (remainingExec (run₂.trans run₄) run)
  intro off width ho
  rw [memEq, memLoad_memStore_of_rangeApart]
  · exact f₄.memLoad_eq (outputOutside g off (width/8) ho) |>.trans
      (f₂.memLoad_eq (outputOutside g off (width/8) ho))
  · apply RangeApart.of_toNat
    · have := g.dstLow; bv_omega
    · have := g.dstLow; simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    · right
      have e : (dst+88).toNat = dst.toNat+88 := by have := g.dstLow; bv_omega
      rw [e]
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
      have := g.dstLow
      omega

private theorem localLimbs_afterChoice {m n : Ram} {base : Word}
    (frame : RamWriteFrame m n [⟨(base-9).toNat,1⟩])
    (room : 9 ≤ base.toNat) (top : base.toNat + 272 ≤ 2^32) (axis : Bool) :
    localLimbs n base axis = localLimbs m base axis := by
  apply Vector.ext
  intro i hi
  simp only [localLimbs, Vector.getElem_ofFn]
  have offBound : ∀ a : Bool, ∀ j : Fin 5, (limbOffset ((if a then 5 else 0) + j.val)).toNat+8 ≤ 200 := by
    decide +kernel
  have bound : (limbOffset ((if axis then 5 else 0) + i)).toNat+8 ≤ 200 := offBound axis ⟨i,hi⟩
  apply frame.memLoad_eq
  have e : (base+limbOffset ((if axis then 5 else 0)+i)).toNat =
      base.toNat + (limbOffset ((if axis then 5 else 0)+i)).toNat := by
    rw [BitVec.toNat_add]; omega
  refine ⟨by rw [e]; change _ + 8 ≤ _; omega, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  right
  change (base-9).toNat+1 ≤ _
  rw [e]; bv_omega

private theorem pointMemoryAffine (sp dst : Word) (mem : Ram) (x y : Fin modulus) (mag : Nat)
    (apart : RangeApart dst 81 sp 216)
    (coords : ∀ axis : Bool, FieldRepr (Vector.ofFn fun i : Fin 5 =>
      memLoad mem (sp + limbOffset ((if axis then 5 else 0) + i.val)) 64) (if axis then y else x) mag) :
    K256.Proofs.Sec1.Parser.AffineAt (pointMemory sp dst mem) dst x y mag := by
  refine ⟨_, _, ?_, ?_, memLoad_memStore_same _ _ _ (by decide) (by decide), coords false, coords true⟩
  · intro i hi
    rw [Vector.getElem_ofFn]
    simpa only [Bool.false_eq_true, ite_false, Nat.zero_add] using
      pointMemory_limb sp dst mem i (by omega : i < 10) apart
  · intro i hi
    rw [Vector.getElem_ofFn]
    have e : wordAddr (dst + 40) 64 i = wordAddr dst 64 (5 + i) := by
      simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, Nat.reduceMul, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [e]
    exact pointMemory_limb sp dst mem (5+i) (by omega) apart

set_option maxRecDepth 2048 in
theorem affineDecoder {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code) :
  ∀ args mem sp dst x y ret, EntryPre code args mem sp dst x y ret →
    let point := Standards.SECG.ECC.Curve.Point.affine (readCoordinate mem x).nat (readCoordinate mem y).nat
    let ok := Standards.SECG.ECC.Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain point
    ∃ out, program.Exec (dialect code) ⟨⟨.l11f780,args,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,sp+8⟩ ∧ out.values[0] = ⟨64,dst⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame mem out.store [⟨(sp-273).toNat,273⟩, ⟨dst.toNat,89⟩] ∧
      memLoad out.store (dst + 88) 8 = BitVec.ofNat 8 ok.toNat ∧
      (ok = true → Ecdh.Decode.AffinePointAt out.store dst point) := by
  intro args mem sp dst px py ret pre
  obtain ⟨out, run, tag, rsp, rax, kept, frame, flag, _⟩ := decoderCall cover args mem sp dst px py ret pre
  refine ⟨out, run, tag, rsp, rax, kept, frame, flag, ?_⟩
  intro ok
  let base := sp-264
  let x := readCoordinate mem px
  let y := readCoordinate mem py
  have room := pre.room
  have high := pre.slot.low
  have low := pre.output.readable.low
  have sep := pre.apartDst
  have baseNat : base.toNat + 264 = sp.toNat := by dsimp only [base]; bv_omega
  have bottom : base - 9 = sp-273 := by dsimp only [base]; bv_omega
  have g : EmitGeometry base dst := ⟨by omega,by omega,low,by omega⟩
  obtain ⟨r₁,m₁,path₁,p⟩ := startCall cover args mem sp dst px py ret pre
  have w₁ : Writable code m₁ (base-9) 273 := bottom ▸ pre.stack.of_frame p.frame
  obtain ⟨r₂,m₂,step₂,a⟩ := arithmeticCall cover r₁ m₁ base y.a y.b y.c y.d y.valid
    p.stack p.bit p.r15 p.r13 p.r12 p.rbx p.r14 p.rbp
    (w₁.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
  change ArithmeticPost r₁ r₂ m₁ m₂ base (localLimbs m₁ base false) y.masked y.valid at a
  have xl : localLimbs m₁ base false = x.masked := p.xLimbs
  rw [xl] at a
  obtain ⟨r₃,m₃,path₃,rs₃,ra₃,f₃,k₃⟩ := resumeChoice cover step₂ a.stack
    ((w₁.of_frame a.frame).sub (Nat.le_refl _) (by omega)) a.returnSlot (by decide)
  have f₁₃ : RamWriteFrame m₁ m₃ [⟨(base-9).toNat,209⟩] := by
    apply ((RamWriteFrame.refl m₁ _).trans a.frame ?_).trans f₃
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_self,Nat.le_refl _,by change (base-9).toNat+1 ≤ (base-9).toNat+209; omega⟩
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      refine ⟨_,List.mem_cons_self, ?_, ?_⟩
      · change (base-9).toNat ≤ (base-8).toNat; have := g.room; bv_omega
      · change (base-8).toNat+208 ≤ (base-9).toNat+209; have := g.room; bv_omega
  have highLoad (off : Word) (h : 200 ≤ off.toNat ∧ off.toNat+8 ≤ 272) :
      memLoad m₃ (base+off) 64 = memLoad m₁ (base+off) 64 := by
    apply f₁₃.memLoad_eq
    have e : (base+off).toNat = base.toNat+off.toNat := by rw [BitVec.toNat_add]; omega
    refine ⟨by rw [e]; change _ + 8 ≤ _; omega, ?_⟩
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    right; change (base-9).toNat+209 ≤ _; rw [e]; have := g.room; bv_omega
  have ptr := (highLoad 208 (by decide)).trans p.output
  have copy := emittedPayload cover r₃ m₃ base dst g (by rw [rs₃]; rfl) ptr
    ((w₁.of_frame f₁₃).sub (Nat.le_refl _) (by omega))
    ((pre.output.of_frame p.frame).of_frame f₁₃)
    (remainingExec (path₁.trans path₃) run)
  have pair : x.nat < modulus ∧ y.nat < modulus := by
    change Standards.SECG.ECC.Curve.onCurve _ (.affine x.nat y.nat) = true at ok
    simp only [Standards.SECG.ECC.Curve.onCurve,
      show Standards.SECG.DomainParameters.Secp256k1.domain.p = modulus from rfl,
      Bool.and_eq_true,decide_eq_true_eq] at ok
    exact ok.1
  obtain ⟨hx,hy⟩ := pair
  refine ⟨⟨x.nat,hx⟩, ⟨y.nat,hy⟩, rfl, rfl, ?_⟩
  apply K256.Proofs.Sec1.Parser.AffineAt.of_copy (m := pointMemory base dst m₃) (p := dst) (copy := copy)
  apply pointMemoryAffine base dst m₃ _ _ 1 g.stackDstApart
  intro axis
  change FieldRepr (localLimbs m₃ base axis) _ 1
  rw [localLimbs_afterChoice f₃ g.room g.top]
  cases axis
  · rw [a.coordinatesX]
    simp only [CoordinateWords.masked,CoordinateWords.valid,hx,decide_true,ite_true,Bool.false_eq_true,ite_false]
    exact unpack_repr x.a x.b x.c x.d ⟨x.nat,hx⟩ rfl (by decide)
  · rw [a.coordinatesY]
    simp only [CoordinateWords.masked,CoordinateWords.valid,hy,decide_true,ite_true]
    exact unpack_repr y.a y.b y.c y.d ⟨y.nat,hy⟩ rfl (by decide)

end K256.Proofs.Verify.Transfer.PublicKey
