import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Memory
import P256.Proofs.Field.Inverse.SafeGcd.Core.Batch.Routine

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude
open Shared (batchCount batchInput batchResult)

@[refine_layout] def afterBatchAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  Signed.residentAtoms fr controls p s ++
  [.gpr 13 (fr.rsp - 0x180), .gpr 5 (batchResult s).delta,
   .gpr 15 (batchResult s).u, .gpr 3 (batchResult s).v,
   .gpr 14 (batchResult s).q, .gpr 12 (batchResult s).r]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem batch_advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111fc0)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ s.remaining)
    (hcore : Atom.All code (Machine.lifted.locationOf .l117aa0 initial).arguments
      initial.external (Signed.finishAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x111cd1 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l1177b1 final).arguments final.external
        (afterBatchAtoms fr controls p s) := by
  rw [Signed.finishAtoms, Atom.all_append, Atom.all_append] at hcore
  have hresident := hcore.1.1
  have hsplit := resident_split.mp hresident
  have hstable := memory_stable hresident
  have hrsp := hresident
  simp only [Signed.residentAtoms, Core.residentAtoms, Atom.all_append] at hrsp
  have hf := hrsp.1.1.1.1
  simp only [frameAtoms, Atom.All, Atom.Holds] at hf
  obtain ⟨_,_,_,_,_,_,_,_,_,hret,_,hw,hroom,_,_,_,_,_⟩ := hf
  have hl := hret.low
  let bf := batchFrame fr initial.external
  have ha : Atom.All code (Machine.lifted.locationOf .l117aa0 initial).arguments
      initial.external (Batch.loopAtoms bf controls (batchInput s) (batchCount s)) := by
    rw [Batch.loopAtoms, Atom.all_append]
    refine ⟨⟨hsplit.1, hcore.1.2.1, hsplit.2.1, ?_, ?_, hsplit.2.2.1, hsplit.2.2.2.1, trivial⟩, hcore.2⟩
    · change Writable code initial.external (fr.rsp - 0x188 + 8) 1
      exact hw.sub (by bv_omega) (by bv_omega)
    · change (fr.rsp - 0x188).toNat + 9 < 2^64
      bv_omega
  obtain ⟨fuel,final,he,ready,rip,frame,atoms⟩ := Batch.advances hcode hready hrip
    (fr := bf) (RamWriteFrame.refl _ _) hout (by simp only [batchCount]; omega)
    (by simp only [batchCount]; omega) ha
  have hmem := Support.atoms_of_frame
    (args' := (Machine.lifted.locationOf .l1177b1 final).arguments)
    frame (memoryAtoms fr p s) hstable hsplit.2.2.2.2
  change Atom.All code _ _ (Batch.frameAtoms bf controls ++ _) at atoms
  rw [Atom.all_append] at atoms
  have hresident' : Atom.All code (Machine.lifted.locationOf .l1177b1 final).arguments
      final.external (Signed.residentAtoms fr controls p s) :=
    resident_split.mpr ⟨atoms.1.1, atoms.1.2.2.1, atoms.1.2.2.2.2.2.1, atoms.1.2.2.2.2.2.2.1, hmem⟩
  have hwithin : RegionsWithin [Batch.scratchRegion bf] [fr.region, outputRegion fr] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    refine ⟨fr.region, by simp, ?_, ?_⟩
    all_goals simp only [Batch.scratchRegion, bf, batchFrame, Activation.region]
    all_goals bv_omega
  refine ⟨fuel,final,he,ready,rip,hframe.trans frame hwithin,?_⟩
  rw [afterBatchAtoms, Atom.all_append]
  exact ⟨hresident', atoms.1.2.1, atoms.2⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare
