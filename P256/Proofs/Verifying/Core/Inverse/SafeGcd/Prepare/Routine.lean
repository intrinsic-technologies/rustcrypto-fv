import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Zero
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Signed

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

set_option maxHeartbeats 800000

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem zero_live (halt : Bool) (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) :
    ∀ a ∈ Zero.atoms halt .finish fr controls p s, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live (Zero.exit halt)) r
      | _ => True := by
  cases halt <;> simp only [Zero.atoms, loopAtoms, frameAtoms, commonAtoms, outputAtoms,
    inputAtoms, savedInputAtoms, stateAtoms, signedAtoms,
    List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  all_goals decide +kernel

theorem zero_advances [Bindings] (halt : Bool) {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1124fe)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hzero : zeroWords s.g.words = halt)
    (hcore : Atom.All code (Machine.lifted.locationOf .l11454e initial).arguments
      initial.external (loopAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = Machine.lifted.address (Zero.exit halt) ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf (Zero.exit halt) final).arguments final.external
        (Zero.atoms halt .finish fr controls p s) := by
  have hi : (Zero.layout halt fr controls p).Rel code () ⟨.entry, #v[], s⟩
      (Machine.lifted.locationOf .l11454e initial) := by
    refine ⟨rfl, ⟨s, rfl, rfl, ?_⟩, hframe⟩
    change Atom.All code _ initial.external (loopAtoms fr controls p s ++ [.fact (zeroWords s.g.words = halt)])
    rw [Atom.all_append]
    exact ⟨hcore, hzero, trivial⟩
  obtain ⟨loc, e, h⟩ := Zero.block halt code fr controls p () #v[] s _ hi
  obtain ⟨s', _, hs, ha⟩ := h.params
  change s = s' at hs
  subst s'
  exact advance_to (entry := .l11454e) (exit := Zero.exit halt) hcode hready hrip hout
    (e.reaches []) h.label ha h.frame (zero_live halt fr controls p s)

theorem signed_live (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) :
    ∀ a ∈ Signed.finishAtoms fr controls p s, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live .l114675) r
      | _ => True := by
  simp only [Signed.finishAtoms, Signed.residentAtoms, Batch.wordAtoms, frameAtoms,
    commonAtoms, outputAtoms, inputAtoms, savedInputAtoms, stateAtoms, signedAtoms,
    List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  decide +kernel

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112524)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ s.remaining) (hbound : s.remaining ≤ 591)
    (hcore : Atom.All code (Machine.lifted.locationOf .l114574 initial).arguments
      initial.external (loopAtoms fr controls p s ++ [.gpr 2 s.g.words[0]])) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x112625 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l114675 final).arguments final.external
        (Signed.finishAtoms fr controls p s) := by
  have hi : (Selector.layout fr controls p).Rel code () ⟨.entry, #v[], s⟩
      (Machine.lifted.locationOf .l114574 initial) := by
    refine ⟨rfl, ⟨s, rfl, rfl, ?_⟩, hframe⟩
    change Atom.All code _ initial.external (loopAtoms fr controls p s ++
      [.gpr 2 s.g.words[0], .fact (1 ≤ s.remaining), .fact (s.remaining ≤ 591)])
    rw [Atom.all_append] at hcore ⊢
    exact ⟨hcore.1, hcore.2.1, hpos, hbound, trivial⟩
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
  exact advance_to (entry := .l114574) (exit := .l114675) hcode hready hrip hout
    ((e1.reaches []).trans (e2.reaches [])) h2.label ha h2.frame (signed_live fr controls p s)

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare
