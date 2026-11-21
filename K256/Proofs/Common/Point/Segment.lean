import K256.Proofs.Common.Tactic

namespace K256.Proofs.Common.Point

open Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Generate.LIR

def ValuesMatch (graph : Nat → Value) {n : Nat} (a : Values Value n) : Prop :=
  ∀ i : Fin n, a[i] = graph i.val

def BodySegment {n k : Nat} (code : CodeMap) (graph : Nat → Value)
    (memory : Nat → Ram → Prop) (regions : List MemoryRegion)
    (block : Block Op Label signature Reg.count n) (tail : Block Op Label signature Reg.count k) : Prop :=
  ∀ {a : Values Value n} {m : Ram}, ValuesMatch graph a → memory n m →
    ∃ b m', block.eval (dialect code) a m = tail.eval (dialect code) b m' ∧
      ValuesMatch graph b ∧ memory k m' ∧ RamWriteFrame m m' regions

theorem BodySegment.trans {n k j : Nat} {code : CodeMap} {graph : Nat → Value}
    {memory : Nat → Ram → Prop} {regions : List MemoryRegion}
    {a : Block Op Label signature Reg.count n} {b : Block Op Label signature Reg.count k}
    {c : Block Op Label signature Reg.count j}
    (ab : BodySegment code graph memory regions a b) (bc : BodySegment code graph memory regions b c) :
    BodySegment code graph memory regions a c := by
  intro vals m hv hm
  obtain ⟨vb, mb, s, h, t, fr⟩ := ab hv hm
  obtain ⟨vc, mc, s', h', t', fr'⟩ := bc h t
  exact ⟨vc, mc, s.trans s', h', t', fr.trans fr' (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)⟩

theorem ValuesMatch.push {n : Nat} {a : Values Value n} {graph : Nat → Value}
    (h : ValuesMatch graph a) {v : Value} (hv : v = graph n) : ValuesMatch graph (a.push v) := by
  intro i
  by_cases hi : i.val < n
  · simpa only [Fin.getElem_fin, Vector.getElem_push, hi, dite_true] using h ⟨i.val, hi⟩
  · have he : i.val = n := by omega
    simpa only [Fin.getElem_fin, Vector.getElem_push, hi, dite_false, he, Nat.lt_irrefl] using hv

end K256.Proofs.Common.Point
