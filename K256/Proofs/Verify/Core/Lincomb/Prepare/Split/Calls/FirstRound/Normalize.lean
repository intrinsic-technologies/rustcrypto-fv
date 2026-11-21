import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Sites

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def roundArgs (a : Registers) : Registers :=
  (a.set 8 (Value.mk 64 0)).set 9 (Value.mk 64 0)

private def terminatorOperands {n : Nat} :
    Terminator Label signature Reg.count n → List (Fin n)
  | .br e => e.arguments.toList
  | .condBr i e f => i :: (e.arguments.toList ++ f.arguments.toList)
  | .call e k => e.arguments.toList ++ k.kept.toList ++ k.guard.toList
  | .ret v t => v.toList ++ t.toList

private def blockUsesOnly (allowed : Nat → Bool) {n : Nat} :
    Block Op Label signature Reg.count n → Bool
  | .letOp _ args next => (args.toList.all fun i => allowed i.val) && blockUsesOnly allowed next
  | .terminate t => (terminatorOperands t).all fun i => allowed i.val

private theorem select_eq_on_operands {n k : Nat} {a b : Values Value n}
    {args : Vector (Fin n) k} (h : ∀ i ∈ args.toList, a[i] = b[i]) :
    a.select args = b.select args := by
  apply Vector.ext
  intro i hi
  rw [Values.getElem_select, Values.getElem_select]
  exact h _ (List.mem_iff_getElem.mpr ⟨i, by simpa using hi, by simp⟩)

private theorem map_eq_on_operand {n : Nat} {a b : Values Value n} {arg : Option (Fin n)}
    (h : ∀ i ∈ arg.toList, a[i] = b[i]) : arg.map (a[·]) = arg.map (b[·]) := by
  cases arg with
  | none => rfl
  | some i => exact congrArg some (h i (List.mem_cons_self ..))

private theorem evalTerm_eq_on_operands {n : Nat} {d : Dialect Op Value Ram}
    {t : Terminator Label signature Reg.count n} {a b : Values Value n} {m : Ram}
    (h : ∀ i ∈ terminatorOperands t, a[i] = b[i]) : t.eval d a m = t.eval d b m := by
  cases t with
  | br e =>
    simp only [Terminator.eval, Edge.eval, select_eq_on_operands h]
  | condBr i e f =>
    simp only [terminatorOperands, List.mem_cons, List.mem_append] at h
    simp only [Terminator.eval, Edge.eval, h i (.inl rfl),
      select_eq_on_operands (fun j hj => h j (.inr (.inl hj))),
      select_eq_on_operands (fun j hj => h j (.inr (.inr hj)))]
  | call e k =>
    simp only [terminatorOperands, List.mem_append] at h
    simp only [Terminator.eval, Edge.eval, Cont.eval,
      select_eq_on_operands (fun j hj => h j (.inl (.inl hj))),
      select_eq_on_operands (fun j hj => h j (.inl (.inr hj))),
      map_eq_on_operand (fun j hj => h j (.inr hj))]
  | ret v t =>
    simp only [terminatorOperands, List.mem_append] at h
    simp only [Terminator.eval, select_eq_on_operands (fun j hj => h j (.inl hj)),
      map_eq_on_operand (fun j hj => h j (.inr hj))]

private theorem evalBlock_eq_on_operands {n : Nat} {d : Dialect Op Value Ram}
    {allowed : Nat → Bool} {block : Block Op Label signature Reg.count n}
    (uses : blockUsesOnly allowed block = true)
    {a b : Values Value n} (same : ∀ i : Fin n, allowed i.val = true → a[i] = b[i])
    (m : Ram) : block.eval d a m = block.eval d b m := by
  induction block generalizing m with
  | @letOp n' arity op args next ih =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp uses
    have argsEq := select_eq_on_operands (a := a) (b := b)
      (fun i hi => same i (List.all_eq_true.mp head i hi))
    simp only [Block.eval, argsEq]
    split
    · refine ih tail ?_ _
      intro i hi
      by_cases old : i.val < n'
      · simpa only [Fin.getElem_fin, Vector.getElem_push_lt old] using same ⟨i.val, old⟩ hi
      · have last : i.val = n' := by omega
        simp only [Fin.getElem_fin, last, Vector.getElem_push_last]
    · rfl
  | terminate t =>
    exact evalTerm_eq_on_operands fun i hi => same i (List.all_eq_true.mp uses i hi)

private def roundOperand (i : Nat) : Bool := i != 8 && i != 9

private theorem roundOperands : blockUsesOnly roundOperand b_l11b8f0 = true := by
  decide +kernel

theorem execRoundArgs {a : Registers} {m : Ram} {out : Output Value Ram Reg.count}
    (h : program.Exec (dialect Extracted.programImage) ⟨⟨.l11b8f0,roundArgs a,m⟩,[]⟩ out) :
    program.Exec (dialect Extracted.programImage) ⟨⟨.l11b8f0,a,m⟩,[]⟩ out := by
  have same : ∀ i : Fin Reg.count, roundOperand i.val = true → a[i] = (roundArgs a)[i] := by
    intro i hi
    have ⟨h8, h9⟩ : i.val ≠ 8 ∧ i.val ≠ 9 := by
      simpa only [roundOperand, Bool.and_eq_true, bne_iff_ne] using hi
    simp only [roundArgs, Fin.getElem_fin,
      Vector.getElem_set_ne (by decide : 9 < Reg.count) i.isLt (Ne.symm h9),
      Vector.getElem_set_ne (by decide : 8 < Reg.count) i.isLt (Ne.symm h8)]
  have step :
      program.step (dialect Extracted.programImage) ⟨⟨.l11b8f0,a,m⟩,[]⟩ =
      program.step (dialect Extracted.programImage) ⟨⟨.l11b8f0,roundArgs a,m⟩,[]⟩ := by
    change (b_l11b8f0.eval _ a m).next _ [] = (b_l11b8f0.eval _ (roundArgs a) m).next _ []
    rw [evalBlock_eq_on_operands roundOperands same m]
  cases h with
  | done stop => exact .done (step.trans stop)
  | next move tail => exact .next (step.trans move) tail

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
