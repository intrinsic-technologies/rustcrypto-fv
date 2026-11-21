import K256.Proofs.Sec1.SqrtChainExecution.ProductResume
import K256.Proofs.Sec1.SqrtChainExecution.Counted
import K256.Proofs.Sec1.Sqrt.LiftedStreaks

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field Sqrt

def streakStage : SquareStreak → Fin 13
  | .at16293 => 1
  | .at1673c => 2
  | .at16bcd => 3
  | .at17034 => 4
  | .at176e7 => 5
  | .at18d97 => 9
  | .at1924d => 10
  | .at19b89 => 11
  | .at1a105 => 12

theorem streakSquares (s : SquareStreak) {code : CodeMap} {fr : Activation} {a : Limbs}
    (g : Geometry code fr) : SquareStage code fr a (streakStage s) := by
  intro args mem h
  let i := streakStage s
  let base := fr.rsp - 440
  let p := words a (2 * (i.val + 1))
  let loc : LIR.lifted.Location := ⟨squarePC[i],args,mem⟩
  have notCounted : counted i = false := by cases s <;> rfl
  have hi : i.val ≠ 0 := by cases s <;> decide
  have frame : SqrtCounted.LoopFrame code args mem fr := by have f := h.frame; rwa [squarePC_frame] at f
  obtain ⟨room,bound,apart⟩ := roundBounds g frame
  obtain ⟨sp,df,mx,ftw,fcw,writable,lo,align⟩ := SqrtCounted.loopGeometry (rfl : base = fr.rsp-440) frame
  have win : WordsAt mem (base+40) 64 (squareWords p) := by
    have hh := h.operand
    change (if counted i then WordsAt mem base 64 p else WordsAt mem (base+40) 64 (squareWords p)) at hh
    simpa only [notCounted,Bool.false_eq_true, ite_false] using hh
  have widths (r : Fin Reg.count) (hr : r.val ∈ (LiftedSquare.volatile ++ [3,5,12,13,14,15,39,50,51] : List Nat)) :
      args[r.val].width = (Reg.ofIndex r.val).width := by
    obtain ⟨r,hlt⟩ := r
    simp only [LiftedSquare.volatile,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.volatile hi 1 (by decide)
    · exact h.volatile hi 2 (by decide)
    · exact h.volatile hi 8 (by decide)
    · exact h.volatile hi 9 (by decide)
    · exact h.widths 3 (by decide)
    · exact h.widths 5 (by decide)
    · exact h.widths 12 (by decide)
    · exact h.widths 13 (by decide)
    · exact h.widths 14 (by decide)
    · exact h.widths 15 (by decide)
    · exact mx
    · exact ftw
    · exact fcw
  have hsr := h.src hi
  have hds := h.dst hi
  have sr : srcReg i = 14 := by cases s <;> rfl
  have ds : dstReg i = LiftedCopy.dstReg s.useRbp := by cases s <;> rfl
  change args[srcReg i].get 64 = base at hsr
  change args[dstReg i].get 64 = base + 40 at hds
  simp only [sr] at hsr
  simp only [ds] at hds
  have ready : LiftedCopy.Ready code s.useRbp base (squareWords p) loc :=
    ⟨sp,hsr,hds,df,widths,writable,win⟩
  have startPC : loc.label = s.firstReturn := by cases s <;> rfl
  obtain ⟨⟨target,b,n⟩,reach,pc,done,write,keep⟩ :=
    s.executeLifted code [] startPC lo align apart ready
  have endPC : s.lastReturn = productPC[i.succ] := by cases s <;> rfl
  change target = s.lastReturn at pc
  have pc' : target = productPC[i.succ] := pc.trans endPC
  clear pc
  subst target
  have regs (r : Fin Reg.count) (hr : savedReg i.succ r = true) : b[r] = args[r] := by
    apply keep r
    simp only [savedReg,Bool.and_eq_true,decide_eq_true_eq] at hr
    simp only [LiftedSquare.preserved,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    omega
  have ctrl (r : Fin Reg.count) (hr : r.val ∈ [4,22,39,50,51]) : b[r] = args[r] := by
    by_cases he : r = 4
    · subst r
      exact done.rsp.trans sp.symm
    · have hne : r.val ≠ 4 := fun eq => he (Fin.ext eq)
      exact keep r (by simp only [LiftedSquare.preserved,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega)
  obtain ⟨slots,rhs,wr⟩ := localData_of_round g room bound h.source h.sourceRead h.writes write
  have desired := (chainWord_step squareWords mulWords a i).2
  have countEq : squareCount[i] = (s.count-1)+1 := by cases s <;> rfl
  rw [countEq] at desired
  have final : WordsAt n (fr.rsp - 400) 64 (words a (2*i.succ.val+1)) := by
    change WordsAt n (fr.rsp - 400) 64 (chainWord squareWords mulWords a (2*(i.val+1)+1))
    rw [desired,show fr.rsp-400 = base+40 by dsimp only [base]; bv_omega]
    exact done.output
  have headEq : LIR.Fn115950.frameAt productPC[i.succ] fr = LIR.Fn115950.frameAt .l118040 fr := by
    cases s <;> rfl
  refine ⟨b,n,reach,⟨?_,savedAtoms_of_eq i.succ base a regs slots h.saved,final,?_,rhs,
    h.sourceRead.of_frame write,h.destWrite.of_frame write,?_,wr⟩⟩
  · rw [headEq]
    exact SqrtCounted.loopFrame_of_frame (rfl : base=fr.rsp-440) frame ctrl write
  · intro impossible
    exact False.elim ((show i.succ.val ∉ [7,8,9] by cases s <;> decide) impossible)
  · intro r hr
    exact (congrArg Value.width (keep r (by simp only [LiftedSquare.preserved,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega))).trans (h.widths r hr)

private theorem secondSquareWord {α : Type} (sq : α → α) (mul : α → α → α) (v : α) :
    chainWord sq mul v 3 = sq (chainWord sq mul v 2) :=
  (chainWord_step sq mul v 0).2

private theorem firstSquareReturned {code fr a} : SquareStage code fr a 0 := by
  intro args mem h
  let p := words a 2
  have eq := secondSquareWord squareWords mulWords a
  have operand : WordsAt mem (fr.rsp - 440 + 40) 64 (squareWords p) := h.operand
  have addr : fr.rsp - 440 + 40 = fr.rsp - 400 := by bv_omega
  have final : WordsAt mem (fr.rsp-400) 64 (words a 3) :=
    Eq.mp ((congrArg (fun z => WordsAt mem z 64 (squareWords p)) addr).trans
      (congrArg (WordsAt mem (fr.rsp - 400) 64) eq.symm)) operand
  refine ⟨args,mem,.refl _,⟨h.frame,h.saved,final,?_,h.source,h.sourceRead,h.destWrite,h.widths,h.writes⟩⟩
  intro bad
  exact False.elim ((by decide : ¬ (1 : Nat) ∈ [7,8,9]) bad)

theorem squareStages {code fr a} (g : Geometry code fr) (i : Fin 13) : SquareStage code fr a i := by
  obtain ⟨i,hi⟩ := i
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact @firstSquareReturned code fr a
  · exact @streakSquares .at16293 code fr a g
  · exact @streakSquares .at1673c code fr a g
  · exact @streakSquares .at16bcd code fr a g
  · exact @streakSquares .at17034 code fr a g
  · exact @streakSquares .at176e7 code fr a g
  · exact @countedSquares .first44 code fr a g
  · exact @countedSquares .middle88 code fr a g
  · exact @countedSquares .last44 code fr a g
  · exact @streakSquares .at18d97 code fr a g
  · exact @streakSquares .at1924d code fr a g
  · exact @streakSquares .at19b89 code fr a g
  · exact @streakSquares .at1a105 code fr a g

end K256.Proofs.Sec1.SqrtChainExecution
