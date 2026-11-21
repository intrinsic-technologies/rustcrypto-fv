import Sha3.Proofs.Wrapper.Loop.Preservation

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {keccak fullState : Bool}

def position (kind : Kind) (v : Variant) (i stop : Nat) (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  if i < stop then kind.start v (keccak := keccak) (fullState := fullState) else kind.exit v (keccak := keccak) (fullState := fullState)

theorem iterate_range [Bindings] {boundary : ReturnBoundary}
    {initial : RamState} {v : Variant} {kind : Kind} {inputs : Array Input}
    {start stop : Nat}
    (body : ∀ i, start ≤ i → i < stop → ∀ s,
      State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i s → s.RIP = kind.start v (keccak := keccak) (fullState := fullState) →
      ∃ fuel t, Advances boundary fuel s t ∧
        State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop (i + 1) t ∧
        t.RIP = position kind v (keccak := keccak) (fullState := fullState) (i + 1) stop ∧
        AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s t)
    {i : Nat} (hstart : start ≤ i) (hstop : i ≤ stop) {s : RamState}
    (h : State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i s)
    (hip : s.RIP = position kind v (keccak := keccak) (fullState := fullState) i stop) :
    ∃ fuel t, Advances boundary fuel s t ∧ State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop stop t ∧
      t.RIP = kind.exit v (keccak := keccak) (fullState := fullState) ∧ AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s t := by
  have loop : ∀ count i, i + count = stop → start ≤ i → ∀ s,
      State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i s → s.RIP = position kind v (keccak := keccak) (fullState := fullState) i stop →
      ∃ fuel t, Advances boundary fuel s t ∧ State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop stop t ∧
        t.RIP = kind.exit v (keccak := keccak) (fullState := fullState) ∧ AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s t := by
    intro count
    induction count with
    | zero =>
      intro i he _ s hs hp
      have hi : i = stop := by omega
      subst i
      exact ⟨0, s, (advances_zero boundary s s).mpr rfl, hs,
        by simpa only [position, Nat.lt_irrefl, ↓reduceIte] using hp,
        AgreesExcept.refl _ _⟩
    | succ count ih =>
      intro i he hl s hs hp
      have hlt : i < stop := by omega
      obtain ⟨fuel, t, hrun, ht, htip, hframe⟩ := body i hl hlt s hs
        (by simpa only [position, hlt, ↓reduceIte] using hp)
      obtain ⟨more, u, hrun', hu, huip, hframe'⟩ :=
        ih (i + 1) (by omega) (by omega) t ht htip
      exact ⟨fuel + more, u, hrun.trans hrun', hu, huip, clobbers_trans hframe hframe'⟩
  exact loop (stop - i) i (by omega) hstart s h hip

end Sha3.Proofs.Wrapper.Loop
