import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.Segments
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.ChoiceCall
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

private theorem localLimbs_of_slots {code : CodeMap} {orig m : Ram}
    {sp : Word} {s : ArithmeticState} (stack : SlotState code orig m sp s.slots) :
    localLimbs m sp false = s.xWords ∧ localLimbs m sp true = s.yWords := by
  constructor
  · apply Vector.ext
    intro i hi
    have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases indices with rfl | rfl | rfl | rfl | rfl
    · exact stack.load 10 (by decide)
    · exact stack.load 6 (by decide)
    · exact stack.load 11 (by decide)
    · exact stack.load 7 (by decide)
    · exact stack.load 4 (by decide)
  · apply Vector.ext
    intro i hi
    have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases indices with rfl | rfl | rfl | rfl | rfl
    · exact stack.load 23 (by decide)
    · exact stack.load 21 (by decide)
    · exact stack.load 18 (by decide)
    · exact stack.load 20 (by decide)
    · exact stack.load 22 (by decide)

theorem arithmeticCall {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    ArithmeticCall code := by
  intro orig mem sp a b c d ok rsp flag r15 r13 r12 r3 r14 r5 writable
  let s0 : ArithmeticState :=
    { regs := fun i => if h : i < Reg.count then orig[i].get 64 else 0
      slots := fun i => memLoad mem (slotAddr sp i) 64 }
  have live : registersMatch orig s0.regs inputs0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
  have stack : SlotState code mem mem sp s0.slots := SlotState.start writable
  have kept : preservedAt orig orig := fun _ _ _ _ => rfl
  have xWords : localLimbs mem sp false = s0.xWords := (localLimbs_of_slots stack).1
  have entry : program.runBlock (dialect code) ⟨.l11f8f6, orig, mem⟩ =
      b_l11f8f6.eval (dialect code) orig mem := rfl
  let state := s0
  let args := orig
  let current := mem
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix0 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep0 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix1 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep1 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix2 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep2 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix3 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep3 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix4 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep4 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix5 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep5 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix6 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep6 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix7 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep7 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix8 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep8 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix9 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep9 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix10 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep10 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix11 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep11 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix12 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep12 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix13 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep13 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix14 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep14 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix15 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep15 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix16 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep16 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix17 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep17 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix18 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep18 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix19 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep19 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix20 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep20 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix21 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep21 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix22 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep22 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix23 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep23 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix24 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep24 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix25 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep25 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix26 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep26 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix27 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep27 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix28 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep28 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix29 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep29 state
  obtain ⟨args, current, step, live, stack, kept⟩ :=
    arithmeticPrefix30 cover orig mem current sp args state (by exact rsp) stack live kept
  have entry := entry.trans step
  let state := arithmeticStep30 state
  obtain ⟨next, out, eval, nextRsp, nextRdi, ret, outStack, preserved⟩ :=
    arithmeticChoiceCall (s := state) live kept (by exact rsp) stack cover
  obtain ⟨wordOk, xOk, yOk, flagOk⟩ :=
    arithmeticRun_words s0 a b c d ok flag r15 r13 r12 r3 r14 r5
  have runStep : arithmeticRun s0 = arithmeticStep31 state := rfl
  have finalStack : SlotState code mem out sp (arithmeticRun s0).slots := by
    rw [runStep]
    exact outStack
  obtain ⟨finalX, finalY⟩ := localLimbs_of_slots finalStack
  refine ⟨next, out, entry.trans eval, nextRsp, ?argument, ret, ?x, ?y, ?flag, finalStack.frame, ?kept⟩
  case argument =>
    rw [nextRdi, ← runStep, wordOk, xWords]
  case x => exact finalX.trans (xOk.trans xWords.symm)
  case y => exact finalY.trans yOk
  case flag => exact (finalStack.load 24 (by decide)).trans flagOk
  case kept =>
    intro i hi
    exact preserved i.val i.isLt i.isLt hi

end K256.Proofs.Sec1.Affine.Uncompressed
