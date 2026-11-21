import K256.Proofs.Sec1.SqrtChainExecution.Preservation
import K256.Proofs.Sec1.SqrtCounted.Execution

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field Sqrt

def loopStage : SquareLoop → Fin 13
  | .first44 => 6
  | .middle88 => 7
  | .last44 => 8

theorem countedSquares (site : SquareLoop) {code : CodeMap} {fr : Activation} {a : Limbs}
    (g : Geometry code fr) : SquareStage code fr a (loopStage site) := by
  intro args m h
  let i := loopStage site
  let base := fr.rsp - 440
  have hi : i.val ≠ 0 := by cases site <;> decide
  have countedAt : counted i = true := by cases site <;> decide
  have pc : squarePC[i] = site.head := by cases site <;> rfl
  have target : productPC[i.succ] = site.exit := by cases site <;> rfl
  have cnt : squareCount[i] = site.roundCount := by cases site <;> rfl
  have source : srcReg i = site.srcReg := by cases site <;> rfl
  have dest : dstReg i = site.dstReg := by cases site <;> rfl
  have counter : countReg i = site.countReg := by cases site <;> rfl
  have sqFrame : Atom.All code args m (LIR.Fn115950.frameAt site.head fr) := pc ▸ h.frame
  have fr0 := (SqrtCounted.headFrame site fr) ▸ sqFrame
  obtain ⟨room,bound,apart⟩ := roundBounds g fr0
  change base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112 at apart
  let p := words a (2 * (i.val+1))
  have win : WordsAt m base 64 p := by
    have o := h.operand
    change (if counted i then WordsAt m base 64 p else WordsAt m (base+40) 64 (squareWords p)) at o
    simpa only [countedAt,ite_true] using o
  have src := h.src hi
  have dst := h.dst hi
  have ctr := h.counter countedAt
  change args[srcReg i].get 64 = base at src
  change args[dstReg i].get 64 = base + 40 at dst
  change args[countReg i] = ⟨64, BitVec.ofNat 64 squareCount[i]⟩ at ctr
  simp only [source] at src
  simp only [dest] at dst
  simp only [counter, cnt] at ctr
  obtain ⟨b,n,reach,post,zero,kept,win,wout,_,writes⟩ := SqrtCounted.executeRounds site g.cover
    (rfl : base = fr.rsp-440) (by change base.toNat + 80 ≤ 0x1145f0 ∨ 0x1148c4 ≤ base.toNat - 112; omega)
    sqFrame src dst ctr h.widths win (h.volatile hi)
  obtain ⟨slots,rhs,wr⟩ := localData_of_round g room bound h.source h.sourceRead h.writes writes
  have saved (r : Fin Reg.count) (hr : savedReg i.succ r = true) : b[r] = args[r] := by
    apply kept
    · simp only [savedReg, Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      omega
    · intro eq
      subst r
      cases site <;> contradiction
  have desired : words a (2 * i.succ.val + 1) = SqrtChain.iter squareWords site.roundCount p := by
    rw [← cnt]
    exact (chainWord_step squareWords mulWords a i).2
  have ptr : fr.rsp - 400 = base + 40 := by dsimp only [base]; bv_omega
  refine ⟨b,n,?_,⟨?_,savedAtoms_of_eq i.succ base a saved slots h.saved,?_,fun _ => ?_,
    rhs,h.sourceRead.of_frame writes,h.destWrite.of_frame writes,?_,wr⟩⟩
  · change Parser.Reaches code squarePC[i] args m productPC[i.succ] b n
    rwa [pc,target]
  · change Atom.All code b n (LIR.Fn115950.frameAt productPC[i.succ] fr)
    rwa [target]
  · change WordsAt n (fr.rsp - 400) 64 (words a (2*i.succ.val+1))
    rw [ptr,desired]
    exact wout
  · change WordsAt n base 64 (words a (2*i.succ.val+1))
    rw [desired]
    exact win
  · intro r hr
    by_cases he : r = site.countReg
    · subst r
      exact congrArg Value.width zero
    · rw [kept r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega) he]
      exact h.widths r hr

end K256.Proofs.Sec1.SqrtChainExecution
