import P256.Proofs.Field.Inverse.SafeGcd.Core.Batch.Blocks
import P256.Proofs.Field.Inverse.SafeGcd.Core.Advance

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Batch

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem reaches (last : Bool) (code : CodeMap) (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) (loc : Machine.lifted.Location)
    (hi : (layout last fr controls).Rel code () ⟨.entry, #v[], (p, remaining)⟩ loc) :
    ∃ final, (Machine.lifted.program.sem (Lift.dialect code)).Reaches
      ⟨loc, []⟩ ⟨final, []⟩ ∧
      (layout last fr controls).Rel code () ⟨.finish, #v[], (p, remaining)⟩ final := by
  obtain ⟨l1, e1, h1⟩ := entry_block last code hcode fr controls () #v[] (p, remaining) _ hi
  obtain ⟨l2, e2, h2⟩ := selectedDelta_block last code hcode fr controls () #v[] (p, remaining) _ h1
  obtain ⟨l3, e3, h3⟩ := selectedFG_block last code hcode fr controls () #v[] (p, remaining) _ h2
  obtain ⟨l4, e4, h4⟩ := selectedUV_block last code hcode fr controls () #v[] (p, remaining) _ h3
  obtain ⟨l5, e5, h5⟩ := selectedQR_block last code hcode fr controls () #v[] (p, remaining) _ h4
  obtain ⟨l6, e6, h6⟩ := shift_block last code fr controls () #v[] (p, remaining) _ h5
  exact ⟨l6, ((((((e1.reaches []).trans (e2.reaches [])).trans (e3.reaches [])).trans (e4.reaches [])).trans (e5.reaches [])).trans (e6.reaches [])), h6⟩

theorem finish_live (last : Bool) (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) :
    ∀ a ∈ finishAtoms last fr controls p remaining, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live (exitLabel last)) r
      | _ => True := by
  cases last <;> simp only [finishAtoms, loopAtoms, frameAtoms, wordAtoms,
    List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  all_goals decide +kernel

theorem step [Bindings] (last : Bool) {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Words} {remaining : Nat}
    {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111fc0)
    (hframe : RamWriteFrame fr.original initial.external [scratchRegion fr])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ remaining) (hbound : remaining ≤ 62)
    (hlast : if last then remaining = 1 else 1 < remaining)
    (hcore : Atom.All code (Machine.lifted.locationOf .l117aa0 initial).arguments
      initial.external (loopAtoms fr controls p remaining)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = Machine.lifted.address (exitLabel last) ∧
      RamWriteFrame fr.original final.external [scratchRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf (exitLabel last) final).arguments final.external
        (finishAtoms last fr controls (next p) (remaining - 1)) := by
  have ha : Atom.All code (Machine.lifted.locationOf .l117aa0 initial).arguments
      initial.external (atoms last .entry fr controls p remaining) := by
    rw [loopAtoms, Atom.all_append] at hcore
    simp only [atoms, stageAtoms, Atom.all_append]
    exact ⟨⟨hcore.1, hpos, hbound, hlast, trivial⟩, hcore.2⟩
  have hi : (layout last fr controls).Rel code () ⟨.entry, #v[], (p, remaining)⟩
      (Machine.lifted.locationOf .l117aa0 initial) :=
    ⟨rfl, ⟨(p, remaining), rfl, rfl, ha⟩, hframe⟩
  obtain ⟨loc, e, h⟩ := reaches last code hcode fr controls p remaining _ hi
  obtain ⟨p', _, hp, ha⟩ := h.params
  change (p, remaining) = p' at hp
  subst p'
  exact advance_to (entry := .l117aa0) (exit := exitLabel last)
    hcode hready hrip hout e h.label ha h.frame (finish_live last fr controls (next p) (remaining - 1))

end P256.Proofs.Field.Inverse.SafeGcd.Core.Batch
