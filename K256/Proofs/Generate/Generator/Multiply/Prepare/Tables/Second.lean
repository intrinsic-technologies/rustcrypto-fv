import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Transport
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.FinishBranch
import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem buildSecond (add : type_of% @addCall) {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {p : Projective}
    (e : CoreEntry fr initial d) (s : State .l11d2e1 fr a m) (pv : p.valid) (pb : p.Stored m (sp fr+3088))
    (first : TableAt m (sp fr+2128) (firstBase d))
    (r3 : a[3] = ⟨64,sp fr+3088⟩) (r12 : a[12] = ⟨64,sp fr+296⟩)
    (r14 : a[14] = ⟨64,0⟩) (r15 : a[15] = ⟨64,sp fr+464⟩)
    (limit : memLoad m (sp fr+104) 64 = 152) :
    ∃ b n, Reaches .l11d2e1 a m .l11d514 b n ∧ State .l11d514 fr b n ∧
      TableAt n (sp fr+2128) (firstBase d) ∧ TableAt n (sp fr+1168) p.value ∧
      b[12] = ⟨64,sp fr+296⟩ ∧ b[13] = ⟨64,sp fr+1168⟩ ∧ b[14] = ⟨64,0⟩ ∧
      b[15] = ⟨64,sp fr+464⟩ ∧ RamWriteFrame m n (Bases.writes fr scratchSpans) := by
  obtain ⟨sp',df,_⟩ := Accumulator.currentStack s rfl
  have inputs : Inputs false 0 (sp fr) a :=
    ⟨congrArg (Value.get 64) sp',congrArg (Value.get 1) df,congrArg (Value.get 64) r3,
      congrArg (Value.get 64) r15,fun _ => congrArg (Value.get 64) r12,by omega⟩
  obtain ⟨b,n,run,sb,args,part,f,save⟩ := buildTable add false e s inputs pv pb 7 (by decide)
  have high : (sp fr).toNat + 3256 < 2^32 := by acc_bounds using e
  obtain ⟨t,cf⟩ := finished false (Nat.le_of_lt high) part
  obtain ⟨_,_,stack⟩ := Accumulator.currentStack sb rfl
  have wide : RamWriteFrame m n (Bases.writes fr scratchSpans) :=
    (RamWriteFrame.refl _ _).trans f (inductionWithin false fr)
  have b14 : b[14] = ⟨64,0⟩ := (save 14 (by decide)).trans r14
  have num := (wide.memLoad_eq (Bases.outside e scratchSpans (i := 104) (by decide) (by decide))).trans limit
  obtain ⟨c,back,w,sv,keep⟩ := finishBranch (q := sp fr)
    (stack.sub (by acc_bounds using e) (by acc_bounds using e)) high args.rsp args.df (args.temp (by decide))
    args.work (congrArg (Value.get 64) b14) num sb.widths sb.savedWidths
  have small : RamWriteFrame n (finishCopy false (sp fr) n) (Bases.writes fr scratchSpans) :=
    (RamWriteFrame.refl _ _).trans cf (finishWithin false fr)
  have first' := first.of_frame f
    (Bases.outside e [(1048,120),(1168,960),(296,120),(464,120)] (i := 2128) (by decide) (by decide))
  refine ⟨c,finishCopy false (sp fr) n,run.trans back,
    scratchState e sb rfl rfl small w sv (fun j h => keep j (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)),first'.of_frame cf ?_,t,
    (keep 12 (by decide)).trans ((save 12 (by decide)).trans r12),
    (keep 13 (by decide)).trans (save 13 (by decide)),(keep 14 (by decide)).trans b14,
    (keep 15 (by decide)).trans ((save 15 (by decide)).trans r15),wide.trans cf (finishWithin false fr)⟩
  dsimp only [entryOff,Bool.false_eq_true,ite_false,Nat.reduceMul,Nat.reduceAdd]
  acc_bounds using e

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
