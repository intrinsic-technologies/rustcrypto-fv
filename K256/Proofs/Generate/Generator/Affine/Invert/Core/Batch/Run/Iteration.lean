import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Run.Arithmetic
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open SafeGcd.Batch (Words)

variable {b : Registers} {p : Ram} {sp : Word}

private theorem setgByte (s : Words) :
    (if ¬s.delta = 0 ∧ s.delta.msb = false then 1 else 0 : BitVec 8) = positiveByte s := by
  simp only [positiveByte, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]

private theorem oddByteTruncate (s : Words) :
    (s.g.setWidth 32).setWidth 8 &&& 1 = oddByte s := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  rfl

private theorem countDown (n : Nat) :
    (BitVec.ofNat 64 (n + 1)).setWidth 32 - 1 = BitVec.ofNat 32 n := by
  rw [BitVec.setWidth_ofNat_of_le (by decide),
    show (1 : BitVec 32) = BitVec.ofNat 32 1 by rfl,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), Nat.add_sub_cancel]

private theorem countZero {n : Nat} (limit : n < 62) :
    BitVec.ofNat 32 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hc := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
    exact hc
  · rintro rfl
    rfl

private theorem countWide {n : Nat} (limit : n < 62) :
    (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n :=
  BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)

private theorem iterationBranch (n : Nat) (c : Registers) (q : Ram) :
    (if ¬n = 0 then (Transfer.jump ⟨.l1092a0, c, q⟩ : Transfer Value Ram Label signature Reg.count)
      else .jump ⟨.l1093f9, c, q⟩) =
    .jump ⟨(if n = 0 then .l1093f9 else .l1092a0), c, q⟩ := by
  by_cases h : n = 0
  · rw [ite_eq_right (not_not_intro h)]
    exact congrArg (fun l => Transfer.jump ⟨l, c, q⟩) (ite_eq_left h).symm
  · rw [ite_eq_left h]
    exact congrArg (fun l => Transfer.jump ⟨l, c, q⟩) (ite_eq_right h).symm

private theorem controls_of_eq {c : Registers}
    (h22 : c[22] = b[22]) (h39 : c[39] = b[39])
    (h50 : c[50] = b[50]) (h51 : c[51] = b[51]) : Controls b c := by
  intro ⟨i, hi⟩ h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact h22
  · exact h39
  · exact h50
  · exact h51

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem iterationBlock {s : Words} {n : Nat} (limit : n < 62)
    (inner : Inner b p sp s (n + 1))
    (stack : Writable Extracted.programImage p (base sp + 8) 104) :
    ∃ c q, program.runBlock (dialect Extracted.programImage) ⟨.l1092a0, b, p⟩ =
      .jump ⟨(if n = 0 then .l1093f9 else .l1092a0), c, q⟩ ∧
      Controls b c ∧ RamWriteFrame p q (work sp) ∧
      Inner c q sp (iterationWords s) n ∧ Rows c q sp (iterationWords s) := by
  have rsp := inner.rsp
  have delta := inner.delta
  have f := inner.f
  have g := inner.g
  have u := inner.u
  have v := inner.v
  have qWord := inner.q
  have r := inner.r
  have counter := inner.counter
  refine ⟨?_, ?_, ?run, ?kept, ?frame, ?post⟩
  case run =>
    arithmetic_segment using code_l1092a0 [rsp, delta, f, g, u, v, qWord, r, counter,
      setWidth_mergeGPR8]
    simp only [countDown, countZero limit, countWide limit, setgByte s, oddByteTruncate s]
    rw [iterationBranch]
  case kept => exact controls_of_eq rfl rfl rfl rfl
  case frame =>
    have stackLow := stack.readable.low
    unfold work
    slot_state region
  case post =>
    suffices next : Inner _ _ _ _ _ from
      ⟨next, ⟨next.rsp, rfl, next.delta, next.u, next.v, next.q, next.r⟩⟩
    refine ⟨rfl, ?delta, ?f, ?g, ?u, ?v, ?qOut, ?r, rfl⟩
    case qOut => segment_words [iterationWords, selectWord]
    all_goals
      apply congrArg (Value.mk 64)
      simp only [iterationWords, selectWord, swapByte, maskedF]
      all_goals lifted_word_eq []

set_option linter.unusedVariables false in
theorem iteration {s : Words} {n : Nat} (limit : n < 62)
    (inner : Inner b p sp s (n + 1)) (low : 736 ≤ sp.toNat) (high : sp.toNat + 129 ≤ 2^32)
    (stack : Writable Extracted.programImage p (base sp + 8) 104) :
    ∃ c q, Reaches .l1092a0 b p (if n = 0 then .l1093f9 else .l1092a0) c q ∧
      Controls b c ∧ RamWriteFrame p q (work sp) ∧
      Inner c q sp (SafeGcd.Batch.next s) n ∧ Rows c q sp (SafeGcd.Batch.next s) := by
  obtain ⟨c, q, run, kept, frame, next, rows⟩ := iterationBlock limit inner stack
  rw [iterationWords_eq] at next rows
  refine ⟨c, q, Semantics.Reaches.single ?_, kept, frame, next, rows⟩
  simp only [Program.sem, Program.step, run, Transfer.next]

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
