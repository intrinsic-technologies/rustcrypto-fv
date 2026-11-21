import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.FirstRound.Normalize
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Return
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply.Split.Caller (Site)

def roundFrame (a : Registers) (m : Ram) (sp src digits : BitVec 64) : Ram :=
  let m₁ := memStore m (sp-8) (a[5].get 64)
  let m₂ := memStore m₁ (sp-16) (a[15].get 64)
  let m₃ := memStore m₂ (sp-24) (a[14].get 64)
  let m₄ := memStore m₃ (sp-32) (a[13].get 64)
  let m₅ := memStore m₄ (sp-40) (a[12].get 64)
  let m₆ := memStore m₅ (sp-48) (a[3].get 64)
  let m₇ := memStore m₆ (sp-480) digits
  memStore m₇ (sp-656) src

private theorem roundFrameWrites {a : Registers} {m : Ram} {sp src digits : BitVec 64}
    (e : RoutineEntry a m sp 0x558) :
    RamWriteFrame m (roundFrame a m sp src digits) [scratch sp 0x558] := by
  have within (off : BitVec 64) (lo : 8 ≤ off.toNat) (hi : off.toNat ≤ 0x558) :
      InRegions [scratch sp 0x558] (sp-off) 8 :=
    ⟨_,.head _,Recode.inScratch e.room hi lo⟩
  unfold roundFrame
  repeat' apply RamWriteFrame.memStore _ _ (within _ (by decide) (by decide))
  exact .refl _ _

theorem roundSavedFrame {a c : Registers} {m : Ram} {sp src scalar tables digits : BitVec 64}
    (e : RoutineEntry a m sp 0x558) (regs : ChildRegs .roundFirst a sp scalar tables c) :
    ∃ b, SplitFrame a m sp src tables digits b (roundFrame a m sp src digits) := by
  have same (i : Fin Reg.count) (ne : 4 ≠ i.val) :
      (c.set 4 ⟨64,frameSp sp⟩)[i] = c[i] :=
    Vector.getElem_set_ne (by decide) i.isLt ne
  refine ⟨c.set 4 ⟨64,frameSp sp⟩,⟨⟨by simp,?_,?_,?_ ,?_,?_,?_,?_,?_,?_⟩,
    roundFrameWrites e,?point,?digit,?args⟩⟩
  · simpa only [Vector.getElem_set, ite_eq_right (by decide : (4 : Nat) ≠ 3)] using regs.bx
  · intro i hi
    have ne : 4 ≠ i.val := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
    simpa only [same i ne] using regs.savedWidths i hi
  · intro i hi
    have ne : 4 ≠ i.val := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
    simpa only [same i ne] using regs.ctrl i hi
  case' point =>
    change memLoad _ (sp-696+40) 64 = src
    rw [show sp-696+40 = sp-656 by bv_omega]
  case' digit =>
    change memLoad _ (sp-696+216) 64 = digits
    rw [show sp-696+216 = sp-480 by bv_omega]
  case args =>
    intro i hi
    have ne : 4 ≠ i.val := by simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi; omega
    simpa only [same i ne] using regs.args i hi
  all_goals simp (disch := store_disch) only [roundFrame,memLoad_memStore_same,memLoad_memStore_of_rangeApart]

set_option maxHeartbeats 1500000 in
theorem roundBlock {a : Registers} {m : Ram} {sp src scalar tables digits : BitVec 64}
    (e : RoutineEntry a m sp 0x558)
    (di : a[7] = ⟨64,src⟩) (si : a[6] = ⟨64,scalar⟩)
    (dx : a[2] = ⟨64,tables⟩) (cx : a[1] = ⟨64,digits⟩) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l10f150,a,m⟩ =
      .call ⟨.l11b8f0,c,memStore (roundFrame a m sp src digits) (frameSp sp-8) (ret .roundFirst)⟩
        (callResume .l10f188 (ret .roundFirst)) ∧
      ChildRegs .roundFirst a sp scalar tables (roundArgs c) := by
  have g4 : a[4].get 64 = sp := congrArg (Value.get 64) e.rsp
  have g1 : a[1].get 64 = digits := congrArg (Value.get 64) cx
  have g2 : a[2].get 64 = tables := congrArg (Value.get 64) dx
  have g6 : a[6].get 64 = scalar := congrArg (Value.get 64) si
  have g7 : a[7].get 64 = src := congrArg (Value.get 64) di
  have stack := e.stack
  have room := e.room
  have low := e.returnSlot.low
  refine ⟨?_,?step,?props⟩
  case step =>
    simp only [ret]
    rw [show frameSp sp-8 = sp-704 by unfold frameSp; bv_omega]
    unfold roundFrame
    cfg_eval [g4,g1,g2,g6,g7,
      Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,
      BitVec.reduceAdd,BitVec.reduceSub]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10f150)
    rfl
  case props =>
    refine ⟨?_,?_,?_,?_,by simp,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · apply congrArg (Value.mk 64)
      unfold frameSp
      bv_omega
    · apply congrArg (Value.mk 64)
      dsimp only [frameSp,slot,destination]
      bv_omega
    · exact si
    · rfl
    · rintro ⟨i,hi⟩ h
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first | rfl | exact congrArg Value.width si | exact congrArg Value.width cx
    · rfl
    · exact (Recode.saveValue e (i := 5) (by decide)).symm
    · rfl
    · apply congrArg (Value.mk 64)
      dsimp only [frameSp,slot,r13]
      bv_omega
    · exact e.saved 14 (by decide)
    · exact (Recode.saveValue e (i := 15) (by decide)).symm
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
