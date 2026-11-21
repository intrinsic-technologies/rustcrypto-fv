import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Blocks
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem call_live (fr : Activation) (controls : RamState) (p : Inputs) :
    ∀ atom ∈ linearCall fr controls p, match atom with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live .l116d00) r
      | _ => True := by
  simp only [linearCall, frameAtoms, outputAtoms, inputAtoms, bounds, List.forall_mem_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  decide +kernel

theorem linear_prefix [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1115d0)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1170b0 initial).arguments
      initial.external (entryAtoms fr controls p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x111220 ∧ RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l116d00 final).arguments final.external
        (linearCall fr controls p) := by
  have hi : (layout fr controls).Rel code () ⟨.entry, #v[], p⟩
      (Machine.lifted.locationOf .l1170b0 initial) := ⟨rfl, ⟨p, rfl, rfl, hcore⟩, hframe⟩
  have sim := Machine.simulation code hcode hout
  have hb := call_block code hcode fr controls () #v[] p _ hi
  change Ahead Machine.lifted code _ _ at hb
  obtain ⟨fuel, final, callee, frame, he, hrel, c', hcall, _⟩ :=
    Support.ahead_call_advances sim
      (Rel.locationOf (P := Machine.lifted) (l := .l1170b0) hready hrip) hb
  obtain ⟨p', _, hp, hatoms⟩ := hcall.params
  change p = p' at hp
  subst p'
  have hlabel : callee.label = .l116d00 := hcall.label
  change Atom.All code callee.arguments callee.store (linearCall fr controls p) at hatoms
  rw [hrel.store] at hatoms
  have ha := Support.atoms_locationOf hrel (by
    intro atom hh
    have hh := call_live fr controls p atom hh
    cases atom with
    | reg _ _ => simpa only [hlabel] using hh
    | low _ _ _ => simpa only [hlabel] using hh
    | mem _ _ _ => trivial
    | words _ _ _ => trivial
    | readable _ _ => trivial
    | writable _ _ => trivial
    | fact _ => trivial) hatoms
  rw [hlabel] at ha
  have hf := hcall.frame
  rw [hrel.store] at hf
  exact ⟨fuel, final, he, ⟨hrel.ready, hrel.sse, hrel.code⟩,
    by rw [hrel.rip, hlabel]; rfl, hf, ha⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift
