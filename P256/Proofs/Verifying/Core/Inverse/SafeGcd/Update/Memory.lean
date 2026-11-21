import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Frame
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.Defs

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open P256.Proofs.Field.Inverse.SafeGcd.Core.Support (MemoryStable atom_of_frame atoms_of_frame)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def updateRegions (fr : Activation) : List MemoryRegion :=
  [⟨(fr.rsp - 0x2c0).toNat, 0x138⟩, ⟨(fr.rsp - 0xd8).toNat, 0x50⟩]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem memory_stable {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {fr : Activation} {p : Inputs} {s : LoopState}
    (h : Atom.All code args mem (memoryAtoms fr p s)) :
    ∀ a ∈ memoryAtoms fr p s, MemoryStable (updateRegions fr) a := by
  simp only [memoryAtoms, commonAtoms, outputAtoms, inputAtoms, savedInputAtoms,
    stateAtoms, signedAtoms, Atom.all_append, Atom.All, Atom.Holds] at h
  obtain ⟨⟨⟨⟨⟨_, _, _, _, _, _, _, hret, _, hw, hroom, _, _, _, _, _⟩,
    ⟨_, _, _⟩, _, _, _, hr1, hr2, hr3, hs1, hs2, hs3, _, _⟩, _⟩, _⟩, _⟩ := h
  have hl := hret.low
  have hl1 := hr1.low
  have hl2 := hr2.low
  have hl3 := hr3.low
  simp only [memoryAtoms, commonAtoms, outputAtoms, inputAtoms, savedInputAtoms,
    stateAtoms, signedAtoms, List.forall_mem_append,
    List.not_mem_nil, MemoryStable, and_true,
    Vector.size, Nat.reduceDiv, Nat.reduceMul, Nat.reduceLT, true_and,
    Outside, updateRegions, List.mem_cons, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals first | omega | bv_omega

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update
