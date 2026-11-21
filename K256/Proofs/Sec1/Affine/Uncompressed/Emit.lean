import K256.Proofs.Sec1.Affine.Uncompressed.Choice
import K256.Proofs.Sec1.Affine.Uncompressed.Return
import K256.Proofs.Sec1.Affine.Uncompressed.Contract

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

private def scratch (base : Word) : Prelude.MemoryRegion := ⟨(base-9).toNat,9⟩
private def outputRegion (dst : Word) : Prelude.MemoryRegion := ⟨dst.toNat,89⟩

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

structure EmitGeometry (base dst : Word) : Prop where
  room : 9 ≤ base.toNat
  top : base.toNat+272 ≤ 2^32
  dstLow : dst.toNat+89 ≤ 2^32
  apart : dst.toNat+89 ≤ base.toNat-9 ∨ base.toNat+272 ≤ dst.toNat

private theorem EmitGeometry.stackOutside {base dst : Word} (g : EmitGeometry base dst)
    (off : Word) (width : Nat) (h : off.toNat + width ≤ 272) :
    Outside [scratch base,outputRegion dst] (base + off) width := by
  have e : (base+off).toNat = base.toNat+off.toNat := by rw [BitVec.toNat_add]; have := g.top; omega
  have er : (base-9).toNat + 9 = base.toNat := by have := g.room; bv_omega
  refine ⟨by rw [e]; have := g.top; omega, ?_⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · right; change (base-9).toNat+9 ≤ _; rw [e, er]; omega
  · obtain rfl := List.mem_singleton.mp hr
    change (base+off).toNat + width ≤ dst.toNat ∨ dst.toNat+89 ≤ (base+off).toNat
    rw [e]
    have := g.apart
    omega

theorem EmitGeometry.stackDstApart {base dst : Word} (g : EmitGeometry base dst) :
    RangeApart dst 81 base 216 := by
  apply RangeApart.of_toNat <;> first | (have := g.top; have := g.dstLow; have := g.apart; omega)

private theorem scratchWithin {base dst : Word} :
    RegionsWithin [scratch base] [scratch base,outputRegion dst] := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩

private theorem sameRegion {rs : List Prelude.MemoryRegion} : RegionsWithin rs rs :=
  fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩

private theorem EmitGeometry.outputOutside {base dst : Word} (g : EmitGeometry base dst)
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

private theorem EmitGeometry.flagIn {base dst : Word} (g : EmitGeometry base dst) :
    InRegions [scratch base,outputRegion dst] (dst+88) 1 := by
  refine ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
  change dst.toNat ≤ (dst+88).toNat ∧ (dst+88).toNat + 1 ≤ dst.toNat+89 ∧ _
  have e : (dst+88).toNat = dst.toNat+88 := by have := g.dstLow; bv_omega
  rw [e]; have := g.dstLow; omega

def validityByte (m : Ram) (base : Word) (curve : BitVec 8) :=
  (memLoad m (base+200) 64).setWidth 8 &&& ((memLoad m (base+192) 64).setWidth 8 &&& curve)

structure EmitPost (args : Values Value Reg.count) (m : Ram) (base dst : Word)
    (out : Output Value Ram Reg.count) : Prop where
  frame : RamWriteFrame m out.store [⟨(base-9).toNat,9⟩,⟨dst.toNat,89⟩]
  tag : out.tag = some ⟨64,memLoad m (base+264) 64⟩
  rsp : out.values[4] = ⟨64,base+272⟩
  rax : out.values[0] = ⟨64,dst⟩
  rbx : out.values[3] = ⟨64,memLoad m (base+216) 64⟩
  r12 : out.values[12] = ⟨64,memLoad m (base+224) 64⟩
  r13 : out.values[13] = ⟨64,memLoad m (base+232) 64⟩
  r14 : out.values[14] = ⟨64,memLoad m (base+240) 64⟩
  r15 : out.values[15] = ⟨64,memLoad m (base+248) 64⟩
  rbp : out.values[5] = ⟨64,memLoad m (base+256) 64⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out.values[i] = args[i]
  flag : memLoad out.store (dst+88) 8 = validityByte m base ((args[0].get 64).setWidth 8)
  affine : ∀ x y : Fin modulus, Parser.AffineAt (pointMemory base dst m) dst x y →
    Parser.AffineAt out.store dst x y

set_option maxRecDepth 2048 in
theorem emitPoint {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code)
    (args : Values Value Reg.count) (m : Ram) (base dst : Word)
    (g : EmitGeometry base dst) (rsp : args[4].get 64 = base)
    (pointer : memLoad m (base+208) 64 = dst)
    (stack : Writable code m (base-9) 225) (outW : Writable code m dst 89)
    (saved : Readable m (base+216) 56) (target : (memLoad m (base+264) 64).toNat < 2^32) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l120298,args,m⟩,[]⟩ out ∧ EmitPost args m base dst out := by
  let pm := pointMemory base dst m
  have pf : RamWriteFrame m pm [scratch base,outputRegion dst] :=
    (RamWriteFrame.refl m _).trans (pointMemory_frame base dst m g.dstLow) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,Nat.le_refl _,by
        change dst.toNat + 81 ≤ dst.toNat + 89; omega⟩)
  have coverCopy := fun e he => cover e (code_l120298 e he)
  have win := stack.sub (n := 9) (Nat.le_refl _) (by omega)
  obtain ⟨r₁,step₁,rbx₁,rsp₁,arg₁,keep₁⟩ := copyPoint code args m base dst rsp pointer
    (stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) outW coverCopy
  obtain ⟨r₂,m₂,run₂,rsp₂,rax₂,f₂,k₂⟩ := pushChoice cover step₁ rsp₁ (win.of_frame pf) g.room (by decide)
  have f₀₂ := pf.trans f₂ scratchWithin
  have eq₂ (off : Word) (h : off.toNat+8 ≤ 272) :
      memLoad m₂ (base+off) 64 = memLoad m (base+off) 64 :=
    f₀₂.memLoad_eq (g.stackOutside off 8 h)
  have eq₁ := pf.memLoad_eq (k := 64) (g.stackOutside 192 8 (by decide))
  have push : StoreOk code m₂ (base-8) 8 0x12032b 5 :=
    ParseSignature.storeOk_of_codeRange (off := 13)
      ((stack.of_frame f₀₂).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (fun e he => cover e (code_l12031e e he)) (by decide +kernel)
  obtain ⟨r₃,step₃,rsp₃,arg₃,keep₃⟩ := finalChoice code r₂ m₂ base (by rw [rsp₂]; rfl)
    (LoadOk.of_offsets (stack.readable.of_frame f₀₂) rfl (addr_sub _ _) (by decide)) push
  obtain ⟨r₄,m₄,run₄,rsp₄,rax₄,f₄,k₄⟩ := pushChoice cover step₃ rsp₃ (win.of_frame f₀₂) g.room (by decide)
  have f₀₄ := f₀₂.trans f₄ scratchWithin
  have rbx₄ : r₄[3].get 64 = dst := by
    exact (congrArg (Value.get 64) ((k₄ 3 (by decide)).trans ((keep₃ 3 (by decide)).trans (k₂ 3 (by decide))))).trans rbx₁
  let flag := validityByte m base ((args[0].get 64).setWidth 8)
  have flagEq : (r₄[0].get 64).setWidth 8 = flag := by
    rw [rax₄, arg₃, rax₂, arg₁, eq₂ 200 (by decide)]
    change _ = (memLoad m (base+200) 64).setWidth 8 &&& _
    change memLoad pm (base+192) 64 = _ at eq₁
    dsimp only [pm] at eq₁
    rw [eq₁]
    simp [Value.get]
  let finish := memStore m₄ (dst+88) flag
  have ff : RamWriteFrame m finish [scratch base,outputRegion dst] := f₀₄.memStore flag g.flagIn
  have load (off : Word) (h : off.toNat+8 ≤ 272) :
      memLoad finish (base+off) 64 = memLoad m (base+off) 64 :=
    ff.memLoad_eq (g.stackOutside off 8 h)
  obtain ⟨out,step,memEq,tag,rax,spr,rbx,r12,r13,r14,r15,rbp,r22,r39,r50,r51⟩ :=
    returnPoint code r₄ m₄ base dst (by rw [rsp₄]; rfl) rbx₄ flag flagEq
      (ParseSignature.storeOk_of_codeRange (off := 0)
        ((outW.of_frame f₀₄).of_offsets rfl (BitVec.add_zero dst).symm (by decide))
        (fun e he => cover e (code_l120330 e he)) (by decide +kernel))
      (saved.of_frame f₀₄) (by change (memLoad finish _ 64).toNat < _; rw [load 264 (by decide)]; exact target)
  have result : program.Exec (dialect code) ⟨⟨.l120330,r₄,m₄⟩,[]⟩ out :=
    .done (by simp only [Program.step,step,Transfer.next])
  refine ⟨out,Program.Exec.of_sem ((run₂.trans run₄).exec result.sem), ?_⟩
  refine ⟨memEq ▸ ff, ?_, spr, rax, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tag]; exact congrArg (fun w => some (⟨64,w⟩ : Value)) (load 264 (by decide))
  · rw [rbx]; exact congrArg (fun w => (⟨64,w⟩ : Value)) (load 216 (by decide))
  · rw [r12]; exact congrArg (fun w => (⟨64,w⟩ : Value)) (load 224 (by decide))
  · rw [r13]; exact congrArg (fun w => (⟨64,w⟩ : Value)) (load 232 (by decide))
  · rw [r14]; exact congrArg (fun w => (⟨64,w⟩ : Value)) (load 240 (by decide))
  · rw [r15]; exact congrArg (fun w => (⟨64,w⟩ : Value)) (load 248 (by decide))
  · rw [rbp]; exact congrArg (fun w => (⟨64,w⟩ : Value)) (load 256 (by decide))
  · intro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact r22.trans ((k₄ 22 (by decide)).trans ((keep₃ 22 (by decide)).trans ((k₂ 22 (by decide)).trans (keep₁ 22 (by decide)))))
    · exact r39.trans ((k₄ 39 (by decide)).trans ((keep₃ 39 (by decide)).trans ((k₂ 39 (by decide)).trans (keep₁ 39 (by decide)))))
    · exact r50.trans ((k₄ 50 (by decide)).trans ((keep₃ 50 (by decide)).trans ((k₂ 50 (by decide)).trans (keep₁ 50 (by decide)))))
    · exact r51.trans ((k₄ 51 (by decide)).trans ((keep₃ 51 (by decide)).trans ((k₂ 51 (by decide)).trans (keep₁ 51 (by decide)))))
  · rw [memEq]; exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · intro x y h
    apply h.of_copy
    intro off width ho
    rw [memEq, memLoad_memStore_of_rangeApart]
    · exact (f₂.trans f₄ sameRegion).memLoad_eq (g.outputOutside off (width/8) ho)
    · apply RangeApart.of_toNat
      · have := g.dstLow; bv_omega
      · have := g.dstLow; simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
      · right
        have e : (dst+88).toNat = dst.toNat+88 := by have := g.dstLow; bv_omega
        rw [e]
        simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
        have := g.dstLow
        omega

end K256.Proofs.Sec1.Affine.Uncompressed
