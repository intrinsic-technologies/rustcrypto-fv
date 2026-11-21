import K256.Proofs.Verify.LIR.Fn109f60.Frame
import K256.Proofs.Common.CFG.Lemma.IR

namespace K256.Proofs.Verify.Core.ScalarProduct

open CFG Lift Verify.LIR X86.Machine X86.UserProcess

private def used {n : Nat} (i : Fin n) := i.val != 8 && i.val != 9

private def independent {n : Nat} : Block Op Label signature Reg.count n → Bool
  | .letOp _ args next => args.all used && independent next
  | .terminate (.call edge cont) =>
    edge.arguments.all used && cont.kept.all used && cont.guard.all used
  | .terminate _ => false

private def Agree {n : Nat} (a b : Values Value n) : Prop :=
  ∀ i : Fin n, used i = true → a[i] = b[i]

private theorem select_eq {n k : Nat} {a b : Values Value n} (h : Agree a b)
    {v : Vector (Fin n) k} (hv : v.all used = true) : a.select v = b.select v := by
  apply Vector.ext
  intro i hi
  simp only [Values.getElem_select]
  exact h _ (Vector.all_eq_true.mp hv i hi)

private theorem eval_eq {n : Nat} (block : Block Op Label signature Reg.count n)
    (d : Dialect Op Value Ram) (ok : independent block = true)
    {a b : Values Value n} (h : Agree a b) (m : Ram) : block.eval d a m = block.eval d b m := by
  induction block generalizing m with
  | letOp op args next ih =>
    rename_i n arity
    obtain ⟨read, rest⟩ := Bool.and_eq_true_iff.mp ok
    simp only [Block.eval, select_eq h read]
    split
    · apply ih rest
      intro i hi
      by_cases old : i.val < n
      · change (_ : Vector _ _)[i.val] = (_ : Vector _ _)[i.val]
        rw [Vector.getElem_push_lt old, Vector.getElem_push_lt old]
        exact h ⟨i.val,old⟩ hi
      · have last : i = Fin.last _ := Fin.ext (by change i.val = n; have := i.isLt; omega)
        subst i
        simp
    · rfl
  | terminate t =>
    cases t with
    | call edge cont =>
      obtain ⟨usedArgs, guard⟩ := Bool.and_eq_true_iff.mp ok
      obtain ⟨args, kept⟩ := Bool.and_eq_true_iff.mp usedArgs
      simp only [Block.eval, Terminator.eval, Edge.eval, Cont.eval, select_eq h args,
        select_eq h kept]
      cases e : cont.guard with
      | none => rfl
      | some i =>
        rw [e] at guard
        simp only [Option.map_some]
        rw [h i guard]
    | _ => contradiction

def entryInputs (a : Values Value 53) : Values Value 53 :=
  (a.set 8 a[4]).set 9 a[4]

theorem entryInputs_step (a : Values Value Reg.count) (m : Ram) (code : CodeMap) :
    program.step (dialect code) ⟨⟨.l1099c0, a, m⟩, []⟩ =
      program.step (dialect code) ⟨⟨.l1099c0, entryInputs a, m⟩, []⟩ := by
  unfold Program.step Program.runBlock
  rw [eval_eq (program.blocks .l1099c0) _ (by decide +kernel) (b := entryInputs a) ?_ m]
  intro i hi
  have h := Bool.and_eq_true_iff.mp hi
  simp only [bne_iff_ne] at h
  simp [entryInputs, Ne.symm h.1, Ne.symm h.2]

end K256.Proofs.Verify.Core.ScalarProduct
