import Sha3.Proofs.Permutation.LoadStore.Store.Finish
import Sha3.Proofs.Permutation.LoadStore.Rmw
import Sha3.Proofs.Permutation.StoreTrace
import Sha3.Proofs.Permutation.Safety
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program Keccak

theorem store_advance [Bindings] (copy : Copy) {boundary : ReturnBoundary} {initial : RamState}
    (hpre : CallPre copy initial) (hb : ¬ InProgram boundary.rip) (a : Lanes) :
    AdvanceTriple boundary 49 (RoundInvariant copy initial 24 a) Extracted.programImage
      (fun _ t ↦ CallResult initial t a) := by
  have hmoves := StoreTrace.moves_advance copy boundary (frameBase initial) (initial.regValue .rdi)
    (Store.store_boundary copy hb)
  exact (Store.advance_of_moves copy boundary initial a hb hpre.targetLow
    (.inl (hpre.return_ne_boundary hb))
    (fun i hi hp ↦ hpre.dataAvoid i hi (.inl hp)) hmoves).conseq
    (fun _ hi ↦ ⟨hpre.storePre hi, hi⟩) (fun _ _ _ ht ↦ ht)

end Sha3.Proofs.Permutation
