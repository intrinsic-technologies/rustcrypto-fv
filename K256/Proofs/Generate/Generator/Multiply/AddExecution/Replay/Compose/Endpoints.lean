import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Layout

namespace K256.Proofs.Generate.Generator.Multiply

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point

def PointWordsAt (m : Ram) (base : BitVec 64) (w : PointWords) : Prop :=
  WordsAt m base 64 w.x ∧ WordsAt m (base + 40) 64 w.y ∧ WordsAt m (base + 80) 64 w.z

namespace AddReplay

open Lean in
local macro "word_indices " i:ident " below " n:num : tactic => do
  let j := mkIdent `j
  let mut literals ← `(term| False)
  let mut cases ← `(term| False)
  for k in (List.range n.getNat).reverse do
    literals ← `(term| $i = $(quote k) ∨ $literals)
    cases ← `(term| Fin.val $j = $(quote k) ∨ $cases)
  `(tactic| (have allIndices : ∀ $j : Fin $n, $cases := by decide +kernel
             have choices : $literals := allIndices ⟨$i, by omega⟩
             repeat' first | obtain selected | choices := choices | contradiction
             all_goals subst $i))

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1900000 in
private theorem entryStack (s : Inputs) (ret : memLoad s.original s.fr.rsp 64 = s.fr.ret)
    (j : Fin 68) :
    memLoad s.original (Slot.address s.fr (.stack j)) 64 = decode s (heap0 (.stack j)) := by
  obtain ⟨i, hi⟩ := j
  word_indices i below 68
  all_goals first | rfl | (change memLoad _ ((s.fr.rsp - 536) + 536) 64 = s.fr.ret
                           simpa only [BitVec.sub_add_cancel] using ret)

private theorem loadAt {m : Ram} {x y w : BitVec 64}
    (h : memLoad m x 64 = w) (eq : x = y) : memLoad m y 64 = w :=
  eq ▸ h

open Lean Elab Tactic in
local elab "input_limbs " lhs:ident rhs:ident : tactic => do
  for k in [:15] do
    let i := quote (k % 5)
    let coordinate (x : Ident) : TacticM Term := do
      match k / 5 with
      | 0 => `(term| $x.1)
      | 1 => `(term| $x.2.1)
      | _ => `(term| $x.2.2)
    let a ← coordinate lhs
    let b ← coordinate rhs
    focus <| evalTactic (← `(tactic| (
      refine ⟨loadAt ($a $i (by decide)) ?_, loadAt ($b $i (by decide)) ?_⟩
      all_goals simp only [wordAddr, Slot.address] <;> bv_omega)))

private theorem entryPoint (s : Inputs) (lhs : PointWordsAt s.original s.fr.rdi s.p)
    (rhs : PointWordsAt s.original s.fr.rsi s.q) (j : Fin 15) :
    memLoad s.original (Slot.address s.fr (.left j)) 64 = decode s (heap0 (.left j)) ∧
    memLoad s.original (Slot.address s.fr (.right j)) 64 = decode s (heap0 (.right j)) := by
  obtain ⟨i, hi⟩ := j
  word_indices i below 15
  input_limbs lhs rhs

theorem entry {code : CodeMap} (s : Inputs)
    (atoms : Atom.All code s.seed s.original (Fn10a410.frameAt .l10a410 s.fr))
    (src : Readable s.original s.fr.rsi 120) (dst : Writable code s.original s.fr.rdi 120)
    (srcAbove : s.fr.rsp.toNat + 8 ≤ s.fr.rsi.toNat) (dstAbove : s.fr.rsp.toNat + 8 ≤ s.fr.rdi.toNat)
    (apart : s.fr.rdi.toNat + 120 ≤ s.fr.rsi.toNat ∨ s.fr.rsi.toNat + 120 ≤ s.fr.rdi.toNat)
    (lhs : PointWordsAt s.original s.fr.rdi s.p) (rhs : PointWordsAt s.original s.fr.rsi s.q) :
    Ready s ∧ ValuesMatch (values s) s.seed ∧ memory code s 53 s.original := by
  simp only [Fn10a410.frameAt, Fn10a410.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, _, _, _, bx, bp, si, di, _, _, r12, r13, r14, r15, _, _, _, rr, ret, _,
    stack, depth, _, _⟩ := atoms
  refine ⟨⟨bx, sp, bp, si, di, r12, r13, r14, r15, by omega, srcAbove, dstAbove, apart⟩,
    ?_, stack, dst, src, rr, ?_⟩
  · intro i
    simp only [values, i.isLt, dite_true, Fin.getElem_fin]
  · intro slot
    cases slot with
    | stack i => exact entryStack s ret i
    | left i => exact (entryPoint s lhs rhs i).1
    | right i => exact (entryPoint s lhs rhs i).2

open Lean Elab Tactic in
local elab "output_limbs " h:ident : tactic => do
  for k in [:15] do
    focus <| evalTactic (← `(tactic| (
      apply loadAt ($h (.left $(quote k)))
      simp only [Slot.address, wordAddr] <;> bv_omega)))

set_option maxRecDepth 1500 in
theorem storedOutput {code : CodeMap} (s : Inputs) {m : Ram} (state : memory code s 7260 m) :
    PointWordsAt m s.fr.rdi (AddGraph.output s.p s.q) := by
  have h : Models s.fr (decode s) m heap171 := state.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro i hi
    word_indices i below 5
  output_limbs h

end AddReplay
end K256.Proofs.Generate.Generator.Multiply
