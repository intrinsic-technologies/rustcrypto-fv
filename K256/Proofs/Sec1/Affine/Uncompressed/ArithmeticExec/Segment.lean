import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.Prefix
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.Registers
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.SlotEval
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Schedule

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

theorem SlotState.withSlots {code : CodeMap} {orig mem : Ram} {sp : Word} {a b : Nat → Word}
    (h : SlotState code orig mem sp a) (same : ∀ i < 25, a i = b i) :
    SlotState code orig mem sp b :=
  ⟨h.writable, h.frame, fun i hi => (h.load i hi).trans (same i hi)⟩

private theorem slotsSucc {P : Nat → Prop} {n : Nat} (last : P n)
    (prev : ∀ i < n, P i) : ∀ i < n.succ, P i := by
  intro i hi
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
  · exact prev i h
  · exact last

private theorem slotsZero {P : Nat → Prop} : ∀ i < 0, P i := fun _ h => (Nat.not_lt_zero _ h).elim

syntax "arithmetic_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| arithmetic_simp [$ls,*]) =>
    `(tactic| simp only [↓arithmeticRead, slotRead, cfg_eval, ↓reduceIte, ↓reduceDIte,
      Nat.reduceEqDiff, BitVec.reduceSetWidth, BitVec.reduceEq, BitVec.add_zero,
      BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.setWidth_and, $ls,*])

def PrefixRuns {n n' : Nat} (code : CodeMap) (block : Block Op Label signature Reg.count n)
    (tail : Block Op Label signature Reg.count n') (before : List (Fin n × Nat))
    (after : List (Fin n' × Nat)) (step : ArithmeticState → ArithmeticState) : Prop :=
  ∀ (orig : Values Value Reg.count) (initial mem : Ram) (sp : Word)
    (args : Values Value n) (s : ArithmeticState),
    s.regs 4 = sp → SlotState code initial mem sp s.slots →
    registersMatch args s.regs before → preservedAt args orig →
    ∃ (next : Values Value n') (m : Ram),
      block.eval (dialect code) args mem = tail.eval (dialect code) next m ∧
      registersMatch next (step s).regs after ∧ SlotState code initial m sp (step s).slots ∧
      preservedAt next orig

open Lean Meta in
dsimproc_decl arithmeticIndex (Fin.val _) := fun e => do
  let some i ← (Lean.Meta.evalNat (← withTransparency .all (whnf e))).run | return .continue
  return .done (mkNatLit i)

open Lean Elab Tactic in
elab "arithmetic_segment " cover:ident inputs:ident count:num " [" defs:ident,* "]" : tactic => do
  let _ ← getFVarId cover
  let defs := defs.getElems
  let hs := (List.range count.getNat).toArray.map fun i => mkIdent (.mkSimple s!"hr{i}")
  let live := mkIdent `live
  let stack := mkIdent `stack
  let saved := mkIdent `saved
  let rsp := mkIdent `rsp
  let pre ← (hs.push rsp).mapM fun x => `(Lean.Parser.Tactic.simpLemma| $x:ident)
  let post ← ((defs ++ hs).push rsp).mapM fun x => `(Lean.Parser.Tactic.simpLemma| $x:ident)
  evalTactic (← `(tactic| intro orig initial mem sp args s $rsp $stack $live $saved))
  evalTactic (← `(tactic| simp only [$inputs:ident, registersMatch, Nat.reduceEqDiff, ↓reduceIte, arithmeticIndex] at $live:ident))
  for h in hs do
    evalTactic (← `(tactic| obtain ⟨$h, $live⟩ := $live))
  evalTactic (← `(tactic|
    (refine ⟨?_, ?_, ?ev, ?reg, ?stackOut, ?savedOut⟩
     case ev =>
       arithmetic_prefix [slotRead, BitVec.add_zero, $pre,*]
       repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard)
       rfl
     case reg =>
       repeat' apply And.intro
       all_goals first | exact True.intro | (arithmetic_simp [$post,*] <;> rfl)
     case stackOut =>
       refine SlotState.withSlots (by slot_state) ?_
       repeat' first | exact slotsZero | apply slotsSucc
       all_goals arithmetic_simp [$post,*] <;> rfl
     case savedOut =>
       intro i hi ho membership
       simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
       rcases membership with hx | hx | hx | hx <;> subst i <;>
         (try simp only [↓arithmeticRead]) <;> exact $saved _ (by decide) (by decide) (by decide))))
end K256.Proofs.Sec1.Affine.Uncompressed
