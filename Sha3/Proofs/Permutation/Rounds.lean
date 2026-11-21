import Sha3.Proofs.Permutation.Safety
import Sha3.Proofs.Permutation.RoundMachine

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program Keccak

theorem rounds_advance [Bindings] (copy : Copy) {boundary : ReturnBoundary} {initial : RamState}
    (hpre : CallPre copy initial) (hb : ¬ InProgram boundary.rip) (a : Lanes) :
    AdvanceTriple boundary 6240 (RoundInvariant copy initial 0 a) Extracted.programImage
      (fun _ t ↦ RoundInvariant copy initial 24 (keccakLanes a) t) := by
  apply rounds_advance_of_step copy boundary Extracted.programImage initial a 260
  intro n hn state
  exact (RoundMachine.round_advance copy hn hb).conseq
    (fun _ hi ↦ ⟨hi, hpre.roundMemory hi.frame⟩) (fun _ _ _ ht ↦ ht.1)

end Sha3.Proofs.Permutation
