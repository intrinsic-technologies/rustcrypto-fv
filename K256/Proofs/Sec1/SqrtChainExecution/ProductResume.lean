import K256.Proofs.Sec1.SqrtChainExecution.ProductCall
import K256.Proofs.Sec1.SqrtChainExecution.Preservation
import K256.Proofs.Sec1.Sqrt.LiftedStreaks.Widths
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field Sqrt

theorem squarePC_frame (i : Fin 13) (fr : Activation) :
    LIR.Fn115950.frameAt squarePC[i] fr = LIR.Fn115950.frameAt .l118040 fr := by
  obtain ⟨i,hi⟩ := i
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem productResume {code : CodeMap} {fr : Activation} {a : Limbs} {i : Fin 13}
    {lab : LIR.Label} {args : Values Value Reg.count} {mem : Ram}
    {child : LIR.lifted.Location} {ret : Word} (g : Geometry code fr) (hn : counted i = false)
    (call : LIR.program.runBlock (dialect code) ⟨lab,args,mem⟩ =
      .call child (Wrapper.callFrame squarePC[i] ret))
    (h : ProductCall code fr a i child ret) :
    ∃ b m, Parser.Reaches code lab args mem squarePC[i] b m ∧ SquareState code fr a i b m := by
  let base := fr.rsp - 440
  obtain ⟨o,run,exit⟩ := LiftedSquare.execute code h.entry
  have frame : SqrtCounted.LoopFrame code (callerArgs child base) child.store fr := by
    have f := h.frame
    rwa [squarePC_frame] at f
  obtain ⟨room,bound,_⟩ := roundBounds g frame
  obtain ⟨slots,rhs,writes⟩ := localData_of_round g room bound h.source h.sourceRead h.writes exit.frame
  have regs (r : Fin Reg.count) (hr : savedReg i.succ r = true) : o.values[r] = child.arguments[r] := by
    apply exit.saved
    simp only [savedReg, Bool.and_eq_true, decide_eq_true_eq] at hr
    simp only [LiftedSquare.preserved,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    omega
  have ctrl (r : Fin Reg.count) (hr : r.val ∈ [4,22,39,50,51]) :
      o.values[r] = (callerArgs child base)[r] := by
    change o.values[r.val] = (callerArgs child base)[r.val]
    simp only [callerArgs, Vector.getElem_set]
    by_cases he : 4 = r.val
    · obtain ⟨r,hr'⟩ := r
      change 4 = r at he
      subst r
      exact exit.rsp
    · simp only [he, reduceIte]
      exact exit.saved r (by simp only [LiftedSquare.preserved,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega)
  have nextFrame := SqrtCounted.loopFrame_of_frame (rfl : base = fr.rsp-440) frame ctrl exit.frame
  refine ⟨o.values,o.store,Serialize.Coordinates.reaches_call call run exit.tag,⟨?_,
    savedAtoms_of_eq i.succ base a regs slots h.saved,?_,?_,?_,?_,rhs,
    h.sourceRead.of_frame exit.frame,h.destWrite.of_frame exit.frame,?_,
    fun _ => LiftedSquare.volatileWidths code child h.entry.label o run,writes⟩⟩
  · rwa [squarePC_frame]
  · simp only [hn, Bool.false_eq_true, ite_false]
    exact exit.output
  · intro hi
    exact (congrArg (Value.get 64) (exit.saved (srcReg i) (by
      unfold srcReg; split <;> decide))).trans (h.src hi)
  · intro hi
    exact (congrArg (Value.get 64) (exit.saved (dstReg i) (by
      unfold dstReg; split <;> first | decide | split <;> decide))).trans (h.dst hi)
  · intro impossible
    simp only [hn, Bool.false_eq_true] at impossible
  · intro r hr
    change o.values[r.val].width = 64
    rw [exit.saved r (by simp only [LiftedSquare.preserved,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega)]
    have hw := h.entry.widths r (by
      simp only [LiftedSquare.volatile,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      omega)
    refine hw.trans ?_
    obtain ⟨r,hr'⟩ := r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.SqrtChainExecution
