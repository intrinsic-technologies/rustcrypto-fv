import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prefix.Blocks
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Advance

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prefix

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem loop_live (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) :
    ∀ a ∈ loopAtoms fr controls p s, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live .l11454e) r
      | _ => True := by
  simp only [loopAtoms, frameAtoms, commonAtoms, outputAtoms, inputAtoms, savedInputAtoms,
    stateAtoms, signedAtoms, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  decide +kernel

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112190)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1141e0 initial).arguments
      initial.external (atoms .entry fr controls p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x1124fe ∧ RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l11454e final).arguments final.external
        (loopAtoms fr controls p (initialState p)) := by
  have hi : (layout fr controls).Rel code () ⟨.entry, #v[], p⟩
      (Machine.lifted.locationOf .l1141e0 initial) := ⟨rfl, ⟨p, rfl, rfl, hcore⟩, hframe⟩
  obtain ⟨l1,e1,h1⟩ := entry_block code hcode fr controls () #v[] p _ hi
  obtain ⟨l2,e2,h2⟩ := loads_block code hcode fr controls () #v[] p _ h1
  obtain ⟨l3,e3,h3⟩ := coefficients_block code hcode fr controls () #v[] p _ h2
  obtain ⟨l4,e4,h4⟩ := initialize_block code hcode fr controls () #v[] p _ h3
  obtain ⟨p',_,hp,ha⟩ := h4.params
  change p = p' at hp
  subst p'
  exact advance_to (entry := .l1141e0) (exit := .l11454e) hcode hready hrip hout
    ((((e1.reaches []).trans (e2.reaches [])).trans (e3.reaches [])).trans (e4.reaches []))
    h4.label ha h4.frame (loop_live fr controls p (initialState p))

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prefix
