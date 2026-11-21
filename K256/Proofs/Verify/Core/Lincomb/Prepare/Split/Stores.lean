import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Negate.Machine
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply.Prepare.Bases.Negate (storeFour)

abbrev KeptForMagnitude (a b : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]

structure SecondRegisters (a : Registers) (m : Ram) (base : BitVec 64)
    (w : Vector (BitVec 64) 4) : Prop where
  stack : a[4].get 64 = base
  low : memLoad m (base + 0x30) 64 = w[0]
  midLow : a[12].get 64 = w[1]
  midHigh : a[5].get 64 = w[2]
  high : a[13].get 64 = w[3]

local macro "keep_magnitude" : tactic => `(tactic| (
  rintro ⟨i, hi⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h <;> subst i <;> rfl))

set_option maxRecDepth 4096 in
theorem copySecond {a : Registers} {m : Ram} {base : BitVec 64} {w : Vector (BitVec 64) 4}
    (s : SecondRegisters a m base w)
    (win : Writable Extracted.programImage m base 0x100) :
    ∃ b, Reaches .l10f48a a m .l10f4af b (storeFour m (base + 0xb0) w) ∧
      b[4] = a[4] ∧ KeptForMagnitude a b := by
  obtain ⟨rsp,lo,x,y,z⟩ := s
  have low := win.readable.low
  refine ⟨?b,Semantics.Reaches.single ?run,?r4,?keep⟩
  case run =>
    change (program.runBlock _ _).next _ [] = _
    simp only [storeFour,BitVec.add_assoc,BitVec.reduceAdd]
    cfg_eval [rsp,lo,x,y,z]
    segment_words [lo,x,y,z]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l10f48a)
    rfl
  case keep => keep_magnitude
  case r4 => rfl

set_option maxRecDepth 4096 in
theorem stageSecond {a : Registers} {m : Ram} {base : BitVec 64} {w : Vector (BitVec 64) 4}
    (s : SecondRegisters a m base w) (widths : ParseSignature.ArgumentWidths a)
    (win : Writable Extracted.programImage m base 0x100)
    (below : Writable Extracted.programImage m (base - 8) 8) :
    let n := memStore (storeFour m (base + 0x38) w) (base - 8) (0x10f44a : BitVec 64)
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10f418,a,m⟩ =
      .call ⟨.l110b80,b,n⟩ (callResume .l10f44a 0x10f44a) ∧
      b[4] = ⟨64,base - 8⟩ ∧ b[7].get 64 = base + 0xb0 ∧
      b[6].get 64 = base + 0x38 ∧ b[2].get 64 = 0x2021a0 ∧
      ParseSignature.ArgumentWidths b ∧ KeptForMagnitude a b := by
  obtain ⟨rsp,lo,x,y,z⟩ := s
  have low := win.readable.low
  dsimp only
  refine ⟨?b,?run,?r4,?r7,?r6,?r2,?widths,?keep⟩
  case run =>
    simp only [storeFour,BitVec.add_assoc,BitVec.reduceAdd]
    cfg_eval [rsp,lo,x,y,z]
    segment_words [lo,x,y,z]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10f418)
    rfl
  case keep => keep_magnitude
  case widths =>
    intro ⟨i,hi⟩ h
    have old := widths ⟨i,hi⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact old
  all_goals rfl

theorem magnitudeJoin (a : Registers) (m : Ram) : Reaches .l10f44a a m .l10f4af a m := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ [] = _
  cfg_eval
  simp only [Transfer.next]
  congr 3
  apply Vector.ext
  intro i hi
  have h : ∃ j : Fin 53, i = j.val := ⟨⟨i,hi⟩,rfl⟩
  obtain ⟨j,rfl⟩ := h
  finite_cases j <;> intro hi <;> rfl

end K256.Proofs.Verify.Core.Lincomb.Prepare
