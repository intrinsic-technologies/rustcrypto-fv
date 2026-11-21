import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec
import K256.Proofs.Sec1.Affine.Uncompressed.Emit
import K256.Proofs.Sec1.Affine.Uncompressed.Start
import K256.Proofs.Sec1.Affine.Uncompressed.Squares
import K256.Proofs.Sec1.Affine.Uncompressed.Product

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

private theorem savedReadable {code : CodeMap} {args : Values Value Reg.count} {m : Ram}
    {sp dst x y ret : Word} (pre : EntryPre code args m sp dst x y ret) :
    Readable m (sp-264+216) 56 := by
  have room := pre.room
  have low := pre.slot.low
  refine ⟨by bv_omega, fun i hi => ?_⟩
  by_cases h : i < 48
  · have e : sp-264+216+BitVec.ofNat 64 i = (sp-273)+BitVec.ofNat 64 (225+i) := by
      rw [BitVec.ofNat_add]; bv_omega
    rw [e]
    exact pre.stack.readable.present _ (by omega)
  · have e : sp-264+216+BitVec.ofNat 64 i = sp+BitVec.ofNat 64 (i-48) := by
      have h' : i = 48+(i-48) := by omega
      conv => lhs; rw [h', BitVec.ofNat_add]
      bv_omega
    rw [e]
    exact pre.slot.present _ (by omega)

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

private theorem curveEquation {xx yy : Limbs} (a b : Fin modulus)
    (hc : FieldRepr xx ((a*a)*a) 1) (hs : FieldRepr yy (b*b) 1) :
    equation xx yy =
      Standards.SECG.ECC.Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain (.affine a.val b.val) := by
  rw [equation_eq hc hs]
  simp only [Standards.SECG.ECC.Curve.onCurve, show Standards.SECG.DomainParameters.Secp256k1.domain.p = modulus from rfl,
    a.isLt, b.isLt, decide_true, Bool.true_and, Fin.val_mul,
    show Standards.SECG.DomainParameters.Secp256k1.domain.a = 0 from rfl,
    show Standards.SECG.DomainParameters.Secp256k1.domain.b = 7 from rfl,
    Nat.zero_mul, Nat.add_zero, Nat.mod_mul_mod, Nat.mod_add_mod]
  exact Bool.eq_iff_iff.mpr (by simp)

private theorem equationForCanonical (x y : CoordinateWords)
    (hx : x.nat < modulus) (hy : y.nat < modulus) :
    equation (cubeProduct x.masked (squareX x.masked)) (squareY y.masked) =
      Standards.SECG.ECC.Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain
        (.affine x.nat y.nat) := by
  let a : Fin modulus := ⟨x.nat,hx⟩
  let b : Fin modulus := ⟨y.nat,hy⟩
  have repr (v : CoordinateWords) (lt : v.nat < modulus) :
      FieldRepr v.masked ⟨v.nat,lt⟩ 8 := by
    simp only [CoordinateWords.masked,CoordinateWords.valid,lt,decide_true,ite_true]
    exact unpack_repr v.a v.b v.c v.d ⟨v.nat,lt⟩ rfl (by decide)
  have xs := squareX_repr x.masked a (repr x hx)
  have ys := squareY_repr y.masked b (repr y hy)
  have xc := cubeProduct_repr x.masked (squareX x.masked) a (a*a) (repr x hx) xs
  exact curveEquation a b xc ys

private theorem gatedEquation (x y : CoordinateWords)
    (equationCanonical : x.nat < modulus → y.nat < modulus →
      equation (cubeProduct x.masked (squareX x.masked)) (squareY y.masked) =
        Standards.SECG.ECC.Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain (.affine x.nat y.nat)) :
    BitVec.ofNat 8 x.valid.toNat &&& (BitVec.ofNat 8 y.valid.toNat &&&
      BitVec.ofNat 8 (equation (cubeProduct x.masked (squareX x.masked)) (squareY y.masked)).toNat) =
        BitVec.ofNat 8 (Standards.SECG.ECC.Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain
          (.affine x.nat y.nat)).toNat := by
  by_cases hx : x.nat < modulus
  · by_cases hy : y.nat < modulus
    · rw [equationCanonical hx hy]
      simp only [CoordinateWords.valid,hx,hy,decide_true,Bool.toNat_true]
      cases Standards.SECG.ECC.Curve.onCurve _ (.affine x.nat y.nat) <;> rfl
    · simp [CoordinateWords.valid,Standards.SECG.ECC.Curve.onCurve,
        show Standards.SECG.DomainParameters.Secp256k1.domain.p = modulus from rfl,hy]
  · simp [CoordinateWords.valid,Standards.SECG.ECC.Curve.onCurve,
      show Standards.SECG.DomainParameters.Secp256k1.domain.p = modulus from rfl,hx]


set_option maxRecDepth 2048 in
theorem decoderCall {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code) :
    DecoderCall code := by
  intro args mem sp dst px py ret pre
  dsimp only
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
  have retAddr : base+264 = sp := by dsimp only [base]; bv_omega
  have retLoad : memLoad m₃ (base+264) 64 = ret := by
    rw [highLoad 264 (by decide),retAddr]
    apply Eq.trans (p.frame.memLoad_eq ?_) pre.retWord
    refine ⟨by change sp.toNat+8 ≤ _; omega, ?_⟩
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    right; change (sp-273).toNat+273 ≤ sp.toNat; bv_omega
  have p₃ : memLoad m₃ (base+208) 64 = dst := (highLoad 208 (by decide)).trans p.output
  obtain ⟨out,run,e⟩ := emitPoint cover r₃ m₃ base dst g (by rw [rs₃]; rfl) p₃
    ((w₁.of_frame f₁₃).sub (Nat.le_refl _) (by omega))
    ((pre.output.of_frame p.frame).of_frame f₁₃)
    (((savedReadable pre).of_frame p.frame).of_frame f₁₃)
    (by rw [retLoad]; exact pre.retLow)
  have qframe : RamWriteFrame mem out.store [⟨(sp-273).toNat,273⟩,⟨dst.toNat,89⟩] := by
    have within (n : Nat) (hn : n ≤ 273) :
        RegionsWithin [⟨(base-9).toNat,n⟩] [⟨(sp-273).toNat,273⟩,⟨dst.toNat,89⟩] := by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      rw [bottom]
      refine ⟨_, List.mem_cons_self, Nat.le_refl _, ?_⟩
      change (sp-273).toNat+n ≤ (sp-273).toNat+273; omega
    have first := (RamWriteFrame.refl mem _).trans p.frame (bottom ▸ within 273 (by decide))
    apply (first.trans f₁₃ (within 209 (by decide))).trans e.frame
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact within 9 (by decide) _ List.mem_cons_self
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  have back (off save : Word) (h : 200 ≤ off.toNat ∧ off.toNat+8 ≤ 272)
      (addr : base+off = sp-save) : memLoad m₃ (base+off) 64 = memLoad m₁ (sp-save) 64 := by
    rw [highLoad off h,addr]
  obtain ⟨save3,save12,save13,save14,save15,save5⟩ := p.saved
  refine ⟨out, Program.Exec.of_sem ((path₁.trans path₃).exec run.sem),
    retLoad ▸ e.tag, ?_, e.rax, ?_, qframe, ?_, ?_⟩
  · rw [e.rsp]; congr 1; dsimp only [base]; bv_omega
  · intro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact e.rbx.trans ((congrArg (fun w => (⟨64,w⟩ : Value))
        ((back 216 48 (by decide) (by dsimp only [base]; bv_omega)).trans save3)).trans
        (pre.savedWidth 3 (by decide)).symm)
    · exact e.rbp.trans ((congrArg (fun w => (⟨64,w⟩ : Value))
        ((back 256 8 (by decide) (by dsimp only [base]; bv_omega)).trans save5)).trans
        (pre.savedWidth 5 (by decide)).symm)
    · exact e.r12.trans ((congrArg (fun w => (⟨64,w⟩ : Value))
        ((back 224 40 (by decide) (by dsimp only [base]; bv_omega)).trans save12)).trans
        (pre.savedWidth 12 (by decide)).symm)
    · exact e.r13.trans ((congrArg (fun w => (⟨64,w⟩ : Value))
        ((back 232 32 (by decide) (by dsimp only [base]; bv_omega)).trans save13)).trans
        (pre.savedWidth 13 (by decide)).symm)
    · exact e.r14.trans ((congrArg (fun w => (⟨64,w⟩ : Value))
        ((back 240 24 (by decide) (by dsimp only [base]; bv_omega)).trans save14)).trans
        (pre.savedWidth 14 (by decide)).symm)
    · exact e.r15.trans ((congrArg (fun w => (⟨64,w⟩ : Value))
        ((back 248 16 (by decide) (by dsimp only [base]; bv_omega)).trans save15)).trans
        (pre.savedWidth 15 (by decide)).symm)
    · exact (e.kept 22 (by decide)).trans ((k₃ 22 (by decide)).trans
        ((a.kept 22 (by decide)).trans (p.kept 22 (by decide))))
    · exact (e.kept 39 (by decide)).trans ((k₃ 39 (by decide)).trans
        ((a.kept 39 (by decide)).trans (p.kept 39 (by decide))))
    · exact (e.kept 50 (by decide)).trans ((k₃ 50 (by decide)).trans
        ((a.kept 50 (by decide)).trans (p.kept 50 (by decide))))
    · exact (e.kept 51 (by decide)).trans ((k₃ 51 (by decide)).trans
        ((a.kept 51 (by decide)).trans (p.kept 51 (by decide))))
  · have yflag : memLoad m₃ (base+192) 64 = BitVec.ofNat 64 y.valid.toNat := by
      refine (f₃.memLoad_eq ?_).trans a.flag
      have es : (base+192).toNat = base.toNat+192 := by have := g.top; bv_omega
      refine ⟨by rw [es]; change _+8 ≤ _; omega, ?_⟩
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      right; change (base-9).toNat+1 ≤ _; rw [es]; have := g.room; bv_omega
    have xf : memLoad m₃ (base+200) 64 = BitVec.ofNat 64 x.valid.toNat := (highLoad 200 (by decide)).trans p.xFlag
    rw [e.flag,validityByte, xf, yflag,ra₃,a.argument]
    change _ = BitVec.ofNat 8 (Standards.SECG.ECC.Curve.onCurve _ (.affine x.nat y.nat)).toNat
    simpa [Value.get] using gatedEquation x y (equationForCanonical x y)
  · intro ok
    have pair : x.nat < modulus ∧ y.nat < modulus := by
      change Standards.SECG.ECC.Curve.onCurve _ (.affine x.nat y.nat) = true at ok
      simp only [Standards.SECG.ECC.Curve.onCurve,
        show Standards.SECG.DomainParameters.Secp256k1.domain.p = modulus from rfl,
        Bool.and_eq_true,decide_eq_true_eq] at ok
      exact ok.1
    obtain ⟨hx,hy⟩ := pair
    refine ⟨⟨x.nat,hx⟩, ⟨y.nat,hy⟩, rfl, e.affine _ _ ?_⟩
    apply pointMemory_affine base dst m₃ _ _ g.stackDstApart
    intro axis
    change FieldRepr (localLimbs m₃ base axis) _ 8
    rw [localLimbs_afterChoice f₃ g.room g.top]
    cases axis
    · rw [a.coordinatesX]
      simp only [CoordinateWords.masked,CoordinateWords.valid,hx,decide_true,ite_true,Bool.false_eq_true,ite_false]
      exact unpack_repr x.a x.b x.c x.d ⟨x.nat,hx⟩ rfl (by decide)
    · rw [a.coordinatesY]
      simp only [CoordinateWords.masked,CoordinateWords.valid,hy,decide_true,ite_true]
      exact unpack_repr y.a y.b y.c y.d ⟨y.nat,hy⟩ rfl (by decide)

end K256.Proofs.Sec1.Affine.Uncompressed
