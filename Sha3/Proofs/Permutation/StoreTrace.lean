import Sha3.Proofs.Permutation.StoreTrace.Trace
import Sha3.Proofs.Permutation.StoreTrace.Certificates

namespace Sha3.Proofs.Permutation.StoreTrace

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem moves_advance [Bindings] (copy : Copy) (boundary : ReturnBoundary) (sp pointer : BitVec 64)
    (hb : ∀ p : BitVec 64, (storeAddress copy).toNat ≤ p.toNat →
      p.toNat ≤ (Store.restoreAddress copy).toNat → p ≠ boundary.rip) :
    AdvanceTriple boundary 41 (Store.Pre copy sp pointer)
      (codeRange (storeAddress copy) Store.bytes)
      (Effect.post (Store.effect copy sp pointer)) := by
  intro s hready hcode hp
  obtain ⟨t, hrun, hready', hcode', hi⟩ :=
    prefix_advance hp hb (dataSteps copy) ⟨41, by decide⟩ s hready hcode
      (prefixInvariant_initial hp)
  exact ⟨t, hrun, hready', hcode', effect_holds hp hi.model (prefixInvariant_final_rip hi) hi.frame⟩

end Sha3.Proofs.Permutation.StoreTrace
