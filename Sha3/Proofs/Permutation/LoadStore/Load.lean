import Sha3.Proofs.Permutation.LoadStore.Load.Start
import Sha3.Proofs.Permutation.LoadStore.Load.Trace
import Sha3.Proofs.Permutation.Precondition

namespace Sha3.Proofs.Permutation.Load

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem pre_of_callPre {copy : Copy} {initial : RamState} (hp : CallPre copy initial) :
    Pre copy initial := by
  refine ⟨⟨hp.rip, hp.stack, hp.stackAvoid⟩, hp.dataRead, ?_⟩
  intro i hi j hj he
  exact hp.apart j hj i (by change i < 264 at hi; omega) he.symm

theorem load_advance (copy : Copy) [Bindings] (boundary : ReturnBoundary)
    (hboundary : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 50 (CallPre copy) Extracted.programImage
      (fun initial t ↦ RoundInvariant copy initial 0
        (memoryLanes (initial.regValue .rdi) initial) t) := by
  intro initial hready hcode hp
  obtain ⟨s, hstart, hs, hcode', hprogress⟩ :=
    entry_advance copy boundary hboundary initial hready hcode ⟨hp.rip, hp.stack, hp.stackAvoid⟩
  obtain ⟨t, hlanes, ht, hcode'', hprogress'⟩ :=
    lanes_advance (pre_of_callPre hp) hboundary s hs hcode' hprogress
  exact ⟨t, hstart.trans hlanes, ht, hcode'', final_round hprogress'⟩

end Sha3.Proofs.Permutation.Load
