import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.Prologue
import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.Fill
import K256.Proofs.Verify.Core.Lincomb.CopyCall

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC

private theorem preparesPreserved {fr : Activation} {x y : Registers}
    (regs : PreparesGenerator fr x) (keep : PreservedByFill y x) : PreparesGenerator fr y := by
  obtain ⟨bx,bp,r12,r13,r14,r15⟩ := regs
  exact ⟨(keep 3 (by decide)).trans bx,(keep 5 (by decide)).trans bp,
    (keep 12 (by decide)).trans r12,(keep 13 (by decide)).trans r13,
    (keep 14 (by decide)).trans r14,(keep 15 (by decide)).trans r15⟩

private theorem secondFillCall {fr : Activation} {x : Registers} {n : Ram}
    (sp : x[4].get 64 = workSp fr) (regs : PreparesGenerator fr x)
    (df : x[22].get 1 = 0)
    (guard : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fb89 2) :
    ∃ y, program.runBlock (dialect Extracted.programImage) ⟨.l10fb7f,x,n⟩ =
      .call ⟨.l12a700,y,memStore n (workSp fr - 8) (0x10fb8b : BitVec 64)⟩
        (callResume .l10fb8b 0x10fb8b) ∧ FillArguments fr y (slot fr 0x338) ∧ PreservedByFill y x := by
  have bx := congrArg (Value.get 64) regs.1
  have bp := congrArg (Value.get 64) regs.2.1
  change x[3].get 64 = 0x12a700 at bx
  change x[5].get 64 = slot fr 0x338 at bp
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [sp, bx, bp, guard]
    rfl
  case post =>
    refine ⟨⟨rfl,rfl,rfl,rfl,df⟩,?_⟩
    intro ⟨i, hi⟩ live
    simp only [List.mem_cons,List.not_mem_nil,or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem fillExec {b : Registers} {m : Ram} {out : Output Value Ram Reg.count}
    (run : program.runBlock (dialect Extracted.programImage) ⟨.l12a700,b,m⟩ = .returned out) :
    program.Exec (dialect Extracted.programImage) ⟨⟨.l12a700,b,m⟩,[]⟩ out := by
  exact Program.Exec.of_sem (.ret (by simp only [Program.sem, Program.step, run, Transfer.next]))

set_option maxRecDepth 1600 in
theorem zeroGeneratorDigits {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram} (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) :
    ∃ x n, Reaches .l10fb20 c (push m fr) .l10fb8b x n ∧ CallerFrame fr c x m n ∧
      PreparesGenerator fr x ∧ DigitBytes n (slot fr 0x228 + 8) [] ∧ DigitBytes n (slot fr 0x228 + 0x118) [] := by
  obtain ⟨y,z,call,fill,regs,f,word⟩ := generatorPrologue e h args
  have whole := h.frame.trans f.frame (frameBounds e).1
  obtain ⟨o,run,tag,sp,keep,written,zeros⟩ := fillDigits e whole fill (by decide) (by decide) word
  have first := reachesCall call (fillExec run) tag
  have frame₁ : RamWriteFrame z o.store (workWrites fr 0 0x228 265) :=
    (RamWriteFrame.refl _ _).trans written (by
      intro reg hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩)
  have fixed (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      o.values[i] = (y.set 4 ⟨64,workSp fr⟩)[i] := by
    have neq : 4 ≠ i.val := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
    simpa only [Fin.getElem_fin,Vector.getElem_set_ne _ _ neq] using keep i hi
  have f₁ := CallerFrame.next e f (by decide : 0 ≤ 1504) (by decide : 8 ≤ 0x228) (by decide) frame₁ sp
    (by intro i hi; rw [fixed i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
        exact f.widths i hi)
    (by intro i hi; apply fixed; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)
  have whole₁ := h.frame.trans f₁.frame (frameBounds e).1
  have guard := ParseSignature.storeOk_of_codeRange (off := 10)
    (belowWrite e whole₁ (depth := 8) (by decide))
    (fun x hx => Common.fnCode_subset_programImage x (code_l10fb7f x hx)) (by decide : 10 + 2 ≤ _)
  have df := (congrArg (Value.get 1) (keep 22 (by decide))).trans fill.df
  have reg₁ := preparesPreserved regs keep
  obtain ⟨w,call₂,fill₂,keep₂⟩ := secondFillCall (congrArg (Value.get 64) sp) reg₁ df guard
  let pushed := memStore o.store (workSp fr - 8) (0x10fb8b : BitVec 64)
  have room := e.stackRoom
  have high := e.low
  have base := workNat e
  have before := belowWorkNat e (depth := 8) (by decide)
  change (workSp fr - 8).toNat = _ at before
  have pushFrame : RamWriteFrame o.store pushed (workWrites fr 8 0x338 265) :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_,List.mem_cons_self ..,by dsimp [InRegion,scratch]; omega⟩
  have whole₂ := h.frame.trans (f₁.frame.trans pushFrame (workWithin e (by decide) (by decide))) (frameBounds e).1
  have ret : memLoad pushed (workSp fr - 8) 64 = 0x10fb8b := memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨t,run₂,tag₂,sp₂,keep₃,written₂,zeros₂⟩ := fillDigits e whole₂ fill₂ (by decide) (by decide) ret
  have frame₂ := pushFrame.trans written₂ (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩)
  have fixed₂ (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :=
    (keep₃ i hi).trans (keep₂ i hi)
  have f₂ := CallerFrame.next e f₁ (by decide : 8 ≤ 1504) (by decide : 8 ≤ 0x338) (by decide) frame₂ sp₂
    (by intro i hi; rw [fixed₂ i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
        exact f₁.widths i hi)
    (by intro i hi; apply fixed₂; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)
  refine ⟨_,_,first.trans (reachesCall call₂ (fillExec run₂) tag₂),f₂,
    preparesPreserved reg₁ fixed₂,?_,?_⟩
  · intro i
    have hi := i.isLt
    have same := frame₂.memLoad_eq (k := 8)
      (workOutside e (k := 0x230 + i.val) (by decide) (by omega) (by decide) (Or.inl (by omega)))
    have addr : slot fr (0x230 + i.val) = slot fr 0x228 + 8 + BitVec.ofNat 64 i.val := by
      simp only [slot, BitVec.ofNat_add, ← BitVec.add_assoc]; congr 1; bv_omega
    rw [addr] at same
    exact same.trans (zeros i)
  · have addr : slot fr 0x228 + 0x118 = slot fr 0x338 + 8 := by unfold slot; bv_omega
    rw [addr]
    exact zeros₂

end K256.Proofs.Verify.Core.Lincomb
