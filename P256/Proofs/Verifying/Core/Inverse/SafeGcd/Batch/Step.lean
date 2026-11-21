import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch.Blocks
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Advance

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem path_reaches (path : Path) (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState)
    (p : Words) (remaining : Nat) (loc : Machine.lifted.Location)
    (hi : (layout path last fr controls).Rel code () ⟨.entry, #v[], (p, remaining)⟩ loc) :
    ∃ final, (Machine.lifted.program.sem (Lift.dialect code)).Reaches
      ⟨loc, []⟩ ⟨final, []⟩ ∧
      (layout path last fr controls).Rel code () ⟨.finish, #v[], (p, remaining)⟩ final := by
  cases path with
  | even =>
    obtain ⟨l1, e1, h1⟩ := entry_block .even last code fr controls () #v[] (p, remaining) _ hi
    obtain ⟨l2, e2, h2⟩ := even_block last code fr controls () #v[] (p, remaining) _ h1
    obtain ⟨l3, e3, h3⟩ := join_even_block last code fr controls () #v[] (p, remaining) _ h2
    obtain ⟨l4, e4, h4⟩ := shift_block .even last code fr controls () #v[] (p, remaining) _ h3
    exact ⟨l4, ((((e1.reaches []).trans (e2.reaches [])).trans (e3.reaches [])).trans (e4.reaches [])), h4⟩
  | swap =>
    obtain ⟨l1, e1, h1⟩ := entry_block .swap last code fr controls () #v[] (p, remaining) _ hi
    obtain ⟨l2, e2, h2⟩ := odd_swap_block last code fr controls () #v[] (p, remaining) _ h1
    obtain ⟨l3, e3, h3⟩ := swap_block last code fr controls () #v[] (p, remaining) _ h2
    obtain ⟨l4, e4, h4⟩ := shift_block .swap last code fr controls () #v[] (p, remaining) _ h3
    exact ⟨l4, ((((e1.reaches []).trans (e2.reaches [])).trans (e3.reaches [])).trans (e4.reaches [])), h4⟩
  | add =>
    obtain ⟨l1, e1, h1⟩ := entry_block .add last code fr controls () #v[] (p, remaining) _ hi
    obtain ⟨l2, e2, h2⟩ := odd_add_block last code fr controls () #v[] (p, remaining) _ h1
    obtain ⟨l3, e3, h3⟩ := add_block last code fr controls () #v[] (p, remaining) _ h2
    obtain ⟨l4, e4, h4⟩ := join_add_block last code fr controls () #v[] (p, remaining) _ h3
    obtain ⟨l5, e5, h5⟩ := shift_block .add last code fr controls () #v[] (p, remaining) _ h4
    exact ⟨l5, (((((e1.reaches []).trans (e2.reaches [])).trans (e3.reaches [])).trans (e4.reaches [])).trans (e5.reaches [])), h5⟩

theorem finish_live (last : Bool) (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) :
    ∀ a ∈ finishAtoms last fr controls p remaining, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live (exitLabel last)) r
      | _ => True := by
  cases last <;> simp only [finishAtoms, loopAtoms, frameAtoms, wordAtoms,
    List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  all_goals decide +kernel

theorem path_advances [Bindings] (path : Path) (last : Bool) {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Words} {remaining : Nat}
    {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112625)
    (hframe : RamWriteFrame fr.original initial.external [])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l114675 initial).arguments
      initial.external (atoms path last .entry fr controls p remaining)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = Machine.lifted.address (exitLabel last) ∧
      RamWriteFrame fr.original final.external [] ∧
      Atom.All code (Machine.lifted.locationOf (exitLabel last) final).arguments final.external
        (finishAtoms last fr controls (next p) (remaining - 1)) := by
  have hi : (layout path last fr controls).Rel code () ⟨.entry, #v[], (p, remaining)⟩
      (Machine.lifted.locationOf .l114675 initial) :=
    ⟨rfl, ⟨(p, remaining), rfl, rfl, hcore⟩, hframe⟩
  obtain ⟨loc, e, h⟩ := path_reaches path last code fr controls p remaining _ hi
  obtain ⟨p', _, hp, ha⟩ := h.params
  change (p, remaining) = p' at hp
  subst p'
  exact advance_to (entry := .l114675) (exit := exitLabel last)
    hcode hready hrip hout e h.label ha h.frame (finish_live last fr controls (next p) (remaining - 1))

def choose (p : Words) : Path :=
  if even p then .even else if positive p then .swap else .add

theorem choose_facts (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) (p : Words) :
    Atom.All code args mem (pathFacts (choose p) p) := by
  cases he : even p <;> cases hp : positive p <;>
    simp [choose, pathFacts, he, hp, Atom.All, Atom.Holds]

theorem step [Bindings] (last : Bool) {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Words} {remaining : Nat}
    {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112625)
    (hframe : RamWriteFrame fr.original initial.external [])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ remaining) (hbound : remaining ≤ 62)
    (hlast : if last then remaining = 1 else 1 < remaining)
    (hcore : Atom.All code (Machine.lifted.locationOf .l114675 initial).arguments
      initial.external (loopAtoms fr controls p remaining)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = Machine.lifted.address (exitLabel last) ∧
      RamWriteFrame fr.original final.external [] ∧
      Atom.All code (Machine.lifted.locationOf (exitLabel last) final).arguments final.external
        (finishAtoms last fr controls (next p) (remaining - 1)) := by
  apply path_advances (choose p) last hcode hready hrip hframe hout
  rw [loopAtoms, Atom.all_append] at hcore
  simp only [atoms, Atom.all_append]
  exact ⟨⟨⟨hcore.1, choose_facts code _ _ p⟩, hpos, hbound, hlast, trivial⟩, hcore.2⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch
