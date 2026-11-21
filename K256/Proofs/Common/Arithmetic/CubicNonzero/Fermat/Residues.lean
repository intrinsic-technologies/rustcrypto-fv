import K256.Proofs.Common.Arithmetic.CubicNonzero.Prime
import Init.Data.List.Perm
import Init.Data.List.Nat.Range

set_option autoImplicit false

namespace K256.Proofs.Common.Arithmetic.CubicNonzero

theorem mul_mod_cancel (p x a b : Nat) (hx : Nat.Coprime p x)
    (h : x * a % p = x * b % p) : a % p = b % p := by
  by_cases hp : p = 0
  · subst p
    have hx1 : x = 1 := (Nat.coprime_zero_left x).mp hx
    simpa only [hx1, Nat.one_mul] using h
  · apply coprime_mul_mod_injective hx.symm (Nat.mod_lt _ (by omega))
      (Nat.mod_lt _ (by omega))
    simpa only [Nat.mul_mod_mod] using h

theorem residues_perm (p x : Nat) (hp : 0 < p) (hx : Nat.Coprime p x) :
    ((List.range' 1 (p - 1)).map (fun a => x * a % p)).Perm
      (List.range' 1 (p - 1)) := by
  let residues := List.range' 1 (p - 1)
  have mem_residues (a : Nat) : a ∈ residues ↔ 0 < a ∧ a < p := by
    dsimp only [residues]
    rw [List.mem_range'_1]
    omega
  have hnd : (residues.map (fun a => x * a % p)).Nodup := by
    change (residues.map (fun a => x * a % p)).Pairwise (· ≠ ·)
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := List.nodup_range')
    intro a b ha hb hne heq
    exact hne (coprime_mul_mod_injective hx.symm
      ((mem_residues a).mp ha).2 ((mem_residues b).mp hb).2 heq)
  have hsub : residues.map (fun a => x * a % p) ⊆ residues := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hbpos, hblt⟩ := (mem_residues b).mp hb
    apply (mem_residues _).mpr
    refine ⟨?_, Nat.mod_lt _ hp⟩
    have hnz : x * b % p ≠ 0 := by
      intro hz
      have hbzero : b = 0 := coprime_mul_mod_injective hx.symm hblt hp
        (by simpa only [Nat.mul_zero, Nat.zero_mod] using hz)
      omega
    omega
  apply (List.perm_ext_iff_of_nodup hnd List.nodup_range').mpr
  intro a
  refine ⟨fun ha => hsub ha, fun ha => ?_⟩
  classical
  apply Classical.byContradiction
  intro hnot
  have hcons : (a :: residues.map (fun a => x * a % p)).Nodup :=
    List.nodup_cons.mpr ⟨hnot, hnd⟩
  have hcons_sub : a :: residues.map (fun a => x * a % p) ⊆ residues := by
    intro b hb
    rcases List.mem_cons.mp hb with hba | hb
    · exact hba ▸ ha
    · exact hsub hb
  have hlength := hcons.length_le_of_subset hcons_sub
  simp only [List.length_cons, List.length_map] at hlength
  omega

end K256.Proofs.Common.Arithmetic.CubicNonzero
