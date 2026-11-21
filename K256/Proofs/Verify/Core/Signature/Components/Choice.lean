import K256.Proofs.Verify.Choice
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Verify.Core.Components

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR

inductive Component where
  | r | s

def Component.compareReturn : Component → Label
  | .r => .l104fa4 | .s => .l105051
def Component.compareTag : Component → BitVec 64
  | .r => 0x104fa4 | .s => 0x105051
def Component.choiceReturn : Component → Label
  | .r => .l104fb0 | .s => .l10505d
def Component.choiceTag : Component → BitVec 64
  | .r => 0x104fb0 | .s => 0x10505d
def Component.passed : Component → Label
  | .r => .l104fbc | .s => .l105069

abbrev keptRegs := [2,3,5,8,9,12,13,14,15,22,39,50,51]
def Kept (a b : Registers) := ∀ i : Fin Reg.count, i.val ∈ keptRegs → b[i] = a[i]

private theorem choiceCall (k : Component) {a : Registers} {m : Ram} {sp : BitVec 64}
    (rs : a[4].get 64 = sp) (zero : a[0].get 8 = 0)
    (win : Writable Extracted.programImage m (sp - 24) 40) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨k.compareReturn,a,m⟩ =
      .call ⟨.l127d50,b,memStore m (sp - 8) k.choiceTag⟩ (resumeAt k.choiceReturn k.choiceTag) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = 1 ∧ Kept a b := by
  have low : (a[0].get 64).setWidth 8 = a[0].get 8 := BitVec.setWidth_setWidth_of_le _ (by decide)
  cases k <;> refine ⟨?_,?_,?_⟩
  all_goals first
    | (cfg_eval [Component.compareReturn,rs]; refine Eq.trans (ite_eq_left ?_) ?_
       · first | slot_guard using code_l104fa4 | slot_guard using code_l105051
       · rfl)
    | skip
  all_goals
    refine ⟨rfl,?_,?_⟩
    · change ((mergeGPR 8 _ _).setWidth 8).setWidth 64 = 1
      simp only [setWidth_mergeGPR8,low,zero]
      rfl
    · intro ⟨i,hi⟩ mem
      simp only [keptRegs,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl


private theorem passedStep (k : Component) {a : Registers} {m : Ram} {sp : BitVec 64}
    (rs : a[4].get 64 = sp) (one : a[0].get 64 = 1)
    (win : Writable Extracted.programImage m (sp - 24) 40) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨k.choiceReturn,a,m⟩ =
      .jump ⟨k.passed,b,memStore m (sp + 8) (1 : BitVec 8)⟩ ∧
      b[4] = a[4] ∧ Kept a b := by
  cases k <;> refine ⟨?_,?_,?_⟩
  all_goals first
    | (cfg_eval [Component.choiceReturn,rs,one]; refine Eq.trans (ite_eq_left ?_) ?_
       · first | slot_guard using code_l104fb0 | slot_guard using code_l10505d
       · rfl)
    | skip
  all_goals
    refine ⟨rfl,?_⟩
    intro ⟨i,hi⟩ mem
    simp only [keptRegs,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem choicePass (k : Component) {a : Registers} {m : Ram} {sp : BitVec 64}
    (rs : a[4].get 64 = sp) (zero : a[0].get 8 = 0)
    (win : Writable Extracted.programImage m (sp - 24) 40) :
    ∃ b n, Reaches k.compareReturn a m k.passed b n ∧ b[4] = ⟨64,sp⟩ ∧ Kept a b ∧
      RamWriteFrame m n [⟨(sp - 24).toNat,40⟩] := by
  obtain ⟨b,call,bs,flag,bk⟩ := choiceCall k rs zero win
  have low := win.readable.low
  have work : Writable Extracted.programImage m (sp-8-1) 1 :=
    win.of_offsets (show sp-8-1 = sp+(0-9) by bv_omega) (addr_sub sp 24) (by decide)
  have ret := win.readable.of_offsets (n := 8) (addr_sub sp 8) (addr_sub sp 24) (by decide)
  obtain ⟨c,n,run,cs,cf,frame,ck⟩ := resumeChoice call bs work ret (by cases k <;> decide)
  have cf' : c[0].get 64 = 1 := by rw [cf,flag]; rfl
  have pushed : RamWriteFrame m (memStore m (sp-8) k.choiceTag) [⟨(sp-24).toNat,40⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    exact ⟨_,List.mem_cons_self,by
      change (sp-24).toNat ≤ (sp-8).toNat ∧ (sp-8).toNat+8 ≤ _ ∧ (sp-8).toNat+8 ≤ _
      bv_omega⟩
  have total := pushed.trans frame (by
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨_,List.mem_cons_self,by change (sp-24).toNat ≤ _; bv_omega,
      by change (sp-8-1).toNat+1 ≤ (sp-24).toNat+40; bv_omega⟩)
  obtain ⟨d,step,ds,dk⟩ := passedStep k (congrArg (Value.get 64) cs) cf' (win.of_frame total)
  have reached : Reaches k.choiceReturn c n k.passed d _ :=
    .step (by change (program.runBlock _ _).next _ _ = _; rw [step]; rfl) (.refl _)
  refine ⟨d,_,run.trans reached,ds.trans cs,?_,total.memStore _ ?_⟩
  · intro i hi
    exact (dk i hi).trans ((ck i (by simp only [keptRegs,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (bk i hi))
  · refine ⟨_,List.mem_cons_self,?_⟩
    change (sp-24).toNat ≤ (sp+8).toNat ∧ (sp+8).toNat+1 ≤ _ ∧ (sp+8).toNat+1 ≤ _
    bv_omega

end K256.Proofs.Verify.Core.Components
