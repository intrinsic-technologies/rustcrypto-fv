import Lean.Elab.Tactic.Omega

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

def magnitude (b : BitVec 8) := (b ^^^ b.sshiftRight 7) - b.sshiftRight 7

theorem digitBytes (d : Int) (lo : -8 ≤ d) (hi : d ≤ 8) :
    magnitude (BitVec.ofInt 8 d) = BitVec.ofNat 8 d.natAbs ∧
    (BitVec.ofInt 8 d >>> 7) = (if d < 0 then 1 else 0) := by
  obtain ⟨i, e⟩ : ∃ i : Fin 17, d = (i.val : Int) - 8 := by
    refine ⟨⟨(d + 8).toNat, by omega⟩, by simp only; omega⟩
  subst d
  exact (show ∀ i : Fin 17,
    let d := (i.val : Int) - 8
    magnitude (BitVec.ofInt 8 d) = BitVec.ofNat 8 d.natAbs ∧
      (BitVec.ofInt 8 d >>> 7) = (if d < 0 then 1 else 0) by decide +kernel) i

end K256.Proofs.Generate.Generator.Multiply.Lookup
