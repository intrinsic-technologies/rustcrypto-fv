import Sha3.Proofs.Permutation.LoadStore
import Sha3.Proofs.Permutation.LoadStore.Load
import Sha3.Proofs.Permutation.Rounds

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program Keccak

theorem load_rounds_advance [Bindings] (copy : Copy) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 6290 (CallPre copy) Extracted.programImage
      (fun initial t ↦ RoundInvariant copy initial 24
        (keccakLanes (memoryLanes (initial.regValue .rdi) initial)) t) := by
  intro initial hready hcode hpre
  obtain ⟨s, hload, hs, hcode', hlanes⟩ :=
    Load.load_advance copy boundary hb initial hready hcode hpre
  obtain ⟨t, hrounds, ht, hcode'', hresult⟩ :=
    rounds_advance copy hpre hb (memoryLanes (initial.regValue .rdi) initial) s hs hcode' hlanes
  exact ⟨t, hload.trans hrounds, ht, hcode'', hresult⟩

theorem call_advance [Bindings] (copy : Copy) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 6339 (CallPre copy) Extracted.programImage
      (fun initial t ↦ CallResult initial t
        (keccakLanes (memoryLanes (initial.regValue .rdi) initial))) := by
  intro initial hready hcode hpre
  obtain ⟨s, hprefix, hs, hcode', hinv⟩ :=
    load_rounds_advance copy boundary hb initial hready hcode hpre
  obtain ⟨t, hstore, ht, hcode'', hresult⟩ :=
    store_advance copy hpre hb (keccakLanes (memoryLanes (initial.regValue .rdi) initial))
      s hs hcode' hinv
  exact ⟨t, hprefix.trans hstore, ht, hcode'', hresult⟩

end Sha3.Proofs.Permutation
