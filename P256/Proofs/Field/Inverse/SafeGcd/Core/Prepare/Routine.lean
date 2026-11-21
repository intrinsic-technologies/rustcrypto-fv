import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Signed

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare


open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem signed_live (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) :
    ∀ a ∈ Signed.finishAtoms fr controls p s, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live .l117aa0) r
      | _ => True := by
  simp only [Signed.finishAtoms, Signed.residentAtoms, Batch.wordAtoms, frameAtoms,
    commonAtoms, outputAtoms, inputAtoms, savedInputAtoms, stateAtoms, signedAtoms, Core.residentAtoms,
    List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  decide +kernel

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111f1a)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ s.remaining) (hbound : s.remaining ≤ 591)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1179fa initial).arguments
      initial.external (loopAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x111fc0 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l117aa0 final).arguments final.external
        (Signed.finishAtoms fr controls p s) := by
  have hi : (Selector.layout fr controls p).Rel code () ⟨.entry, #v[], s⟩
      (Machine.lifted.locationOf .l1179fa initial) := by
    refine ⟨rfl, ⟨s, rfl, rfl, ?_⟩, hframe⟩
    change Atom.All code _ initial.external (loopAtoms fr controls p s ++
      [.fact (1 ≤ s.remaining), .fact (s.remaining ≤ 591)])
    rw [Atom.all_append]
    exact ⟨hcore, hpos, hbound, trivial⟩
  obtain ⟨l1, e1, h1⟩ := Selector.block code hcode fr controls p () #v[] s _ hi
  have hs : (Signed.layout fr controls p).Rel code () ⟨.entry, #v[], s⟩ l1 := by
    obtain ⟨s', _, hs, ha⟩ := h1.params
    change s = s' at hs
    subst s'
    exact ⟨h1.label, ⟨s, rfl, rfl, ha⟩, h1.frame⟩
  obtain ⟨l2, e2, h2⟩ := Signed.block code hcode fr controls p () #v[] s _ hs
  obtain ⟨s', _, hs, ha⟩ := h2.params
  change s = s' at hs
  subst s'
  exact advance_to (entry := .l1179fa) (exit := .l117aa0) hcode hready hrip hout
    ((e1.reaches []).trans (e2.reaches [])) h2.label ha h2.frame (signed_live fr controls p s)

end P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare
