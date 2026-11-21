import K256.Proofs.Sec1.LIR

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt.LiftedSquare

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift

private theorem writtenValue_width (r : Reg) (ws : List Write) :
    (writtenValue r ws).width = r.width := by
  let lookup (w : Write) : Option Value :=
    match Reg.ofWrite? w with
    | some (r', v) => if r' = r then some v else none
    | none => none
  change ((ws.findSome? lookup).getD ⟨r.width, 0⟩).width = r.width
  cases he : ws.findSome? lookup with
  | none => rfl
  | some v =>
    obtain ⟨w, _, hw⟩ := List.exists_of_findSome?_eq_some he
    cases hw' : Reg.ofWrite? w with
    | none => simp [lookup, hw'] at hw
    | some p =>
      obtain ⟨r', v'⟩ := p
      by_cases h : r' = r
      · simp only [lookup, hw', h, ↓reduceIte, Option.some.injEq] at hw
        subst r' v'
        rcases w with ⟨dst, word⟩
        cases dst <;> simp [Reg.ofWrite?] at hw' <;> rcases hw' with ⟨rfl, rfl⟩ <;> rfl
      · simp [lookup, hw', h] at hw

private def knownWidth {n : Nat} : Op n → Option Nat
  | .const v => some v.width
  | .pure _ => none
  | .out _ _ _ (.reg r) => some r.width
  | .out _ _ _ (.flag _) => some 1
  | .out _ _ _ .target => some 64
  | .exec .. | .expect _ => some 1
  | .cut _ => none

private theorem knownWidth_sound {n : Nat} (code : CodeMap) (op : Op n) (args : Values Value n)
    (mem mem' : Ram) (v : Value) (w : Nat)
    (h : knownWidth op = some w) (he : op.eval code args mem = some (v, mem')) :
    v.width = w := by
  cases op with
  | const value =>
    simp only [knownWidth, Option.some.injEq] at h
    simp only [Op.eval, Option.some.injEq, Prod.mk.injEq] at he
    exact he.1 ▸ h
  | pure _ => contradiction
  | cut _ => contradiction
  | out p e reads o =>
    simp only [Op.eval, Option.some.injEq, Prod.mk.injEq] at he
    rw [← he.1]
    cases o <;> simp only [knownWidth, Option.some.injEq] at h <;>
      rw [← h] <;> first | rfl | exact writtenValue_width _ _
  | exec p pre e reads =>
    simp only [Op.eval] at he
    split at he
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      exact he.1 ▸ Option.some.inj h
    · contradiction
  | expect val =>
    simp only [Op.eval] at he
    split at he
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      exact he.1 ▸ Option.some.inj h
    · contradiction

private def retWidths {n : Nat} :
    Block Op LIR.Label signature Reg.count n → Vector (Option Nat) n →
      Option (Vector (Option Nat) Reg.count)
  | .letOp op _ next, widths => retWidths next (widths.push (knownWidth op))
  | .terminate (.ret indices _), widths => some (Values.select widths indices)
  | .terminate _, _ => none

private def WidthsHold {n : Nat} (widths : Vector (Option Nat) n) (args : Values Value n) : Prop :=
  ∀ (i : Fin n) (w : Nat), widths[i.val] = some w → args[i.val].width = w

private theorem retWidths_sound {n : Nat} (code : CodeMap)
    (block : Block Op LIR.Label signature Reg.count n) (widths : Vector (Option Nat) n)
    (args : Values Value n) (mem : Ram) (outWidths : Vector (Option Nat) Reg.count)
    (hargs : WidthsHold widths args) (h : retWidths block widths = some outWidths) :
    block.eval (Lift.dialect code) args mem = .stuck ∨
      ∃ out, block.eval (Lift.dialect code) args mem = .returned out ∧
        WidthsHold outWidths out.values := by
  induction block generalizing mem with
  | @letOp k arity op indices next ih =>
    simp only [retWidths] at h
    rw [Block.eval]
    cases he : (Lift.dialect code).eval op (args.select indices) mem with
    | none => exact .inl rfl
    | some res =>
      obtain ⟨v, mem'⟩ := res
      apply ih _ _ _ _ h
      intro i w hw
      by_cases hi : i.val < k
      · rw [Vector.getElem_push_lt hi] at hw ⊢
        exact hargs ⟨i.val, hi⟩ w hw
      · have heq : i.val = k := by have := i.isLt; omega
        obtain ⟨i, hil⟩ := i
        change i = k at heq
        subst i
        rw [Vector.getElem_push_eq] at hw ⊢
        exact knownWidth_sound code op _ mem mem' v w hw he
  | terminate term =>
    cases term <;> try contradiction
    next indices tag =>
      have he := Option.some.inj h
      subst outWidths
      refine .inr ⟨_, rfl, ?_⟩
      intro i w hw
      simp only [Values.getElem_select] at hw ⊢
      exact hargs _ _ hw

private theorem outputWidths {code : CodeMap} {child : LIR.lifted.Location}
    {out : CFG.Output Value Ram Reg.count} {w : Vector (Option Nat) Reg.count}
    (hc : LIR.lifted.program.runBlock (Lift.dialect code) child = .stuck ∨
      ∃ result, LIR.lifted.program.runBlock (Lift.dialect code) child = .returned result ∧
        WidthsHold w result.values)
    (hExec : LIR.lifted.program.Exec (Lift.dialect code) ⟨child, []⟩ out) :
    WidthsHold w out.values := by
  cases hExec with
  | done h =>
    rcases hc with hstuck | ⟨result, hret, hwidth⟩
    · simp only [Program.step, hstuck, Transfer.next] at h
      contradiction
    · simp only [Program.step, hret, Transfer.next, Outcome.done.injEq] at h
      exact h ▸ hwidth
  | next h =>
    rcases hc with hstuck | ⟨result, hret, _⟩
    · simp only [Program.step, hstuck, Transfer.next] at h
      contradiction
    · simp only [Program.step, hret, Transfer.next] at h
      contradiction

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1200 in
theorem volatileWidths (code : CodeMap) (child : LIR.lifted.Location)
    (hlabel : child.label = .l1145f0) (out : CFG.Output Value Ram Reg.count)
    (hExec : LIR.lifted.program.Exec (Lift.dialect code) ⟨child, []⟩ out) :
    ∀ i : Fin Reg.count, i.val ∈ [1, 2, 8, 9] → out.values[i.val].width = 64 := by
  let w := (retWidths LIR.b_l1145f0 (Vector.replicate _ none)).getD (Vector.replicate _ none)
  have hw : retWidths LIR.b_l1145f0 (Vector.replicate _ none) = some w := by decide +kernel
  have h1 : w[1] = some 64 := by decide +kernel
  have h2 : w[2] = some 64 := by decide +kernel
  have h8 : w[8] = some 64 := by decide +kernel
  have h9 : w[9] = some 64 := by decide +kernel
  have hc := retWidths_sound code LIR.b_l1145f0 _ child.arguments child.store w
    (by simp [WidthsHold]) hw
  have hs : LIR.lifted.program.runBlock (Lift.dialect code) child =
      LIR.b_l1145f0.eval (Lift.dialect code) child.arguments child.store := by
    unfold Program.runBlock
    rw [hlabel]
    rfl
  rw [← hs] at hc
  have hwidth := outputWidths hc hExec
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨i, hil⟩ := i
  rcases hi with rfl | rfl | rfl | rfl
  · exact hwidth 1 64 h1
  · exact hwidth 2 64 h2
  · exact hwidth 8 64 h8
  · exact hwidth 9 64 h9

end K256.Proofs.Sec1.Sqrt.LiftedSquare
