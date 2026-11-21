import P256.Proofs.Scalar.Inverse.Wrapper.Blocks
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Scalar.Inverse.Wrapper
open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem call_live (v : Bool) (fr : Activation) (p : Inputs) :
    ∀ atom ∈ (if v then choiceCall fr p else coreCall fr p), match atom with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live (if v then .l126f60 else .l117650)) r
      | _ => True := by
  cases v <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals simp only [choiceCall, coreCall, frameAtoms, outputAtoms, inputAtoms, List.forall_mem_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  all_goals decide +kernel

theorem core_prefix [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112e30)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l118910 initial).arguments
      initial.external (entryAtoms fr p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x111b70 ∧ RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l117650 final).arguments final.external
        (coreCall fr p) := by
  have hi : (layout fr).Rel code () ⟨.entry, #v[], p⟩
      (Machine.lifted.locationOf .l118910 initial) := ⟨rfl, ⟨p, rfl, rfl, hcore⟩, hframe⟩
  have sim := Machine.simulation code hcode hout
  have hb := call_block false code hcode fr () #v[] p _ hi
  change Ahead Machine.lifted code _ _ at hb
  obtain ⟨fuel, final, callee, frame, he, hrel, c', hcall, _⟩ :=
    Core.Support.ahead_call_advances sim
      (Rel.locationOf (P := Machine.lifted) (l := .l118910) hready hrip) hb
  obtain ⟨p', _, hp, hatoms⟩ := hcall.params
  change p = p' at hp
  subst p'
  have hlabel : callee.label = .l117650 := hcall.label
  change Atom.All code callee.arguments callee.store (coreCall fr p) at hatoms
  rw [hrel.store] at hatoms
  have ha := Core.Support.atoms_locationOf hrel (by
    intro atom hh
    have hh := call_live false fr p atom hh
    cases atom with
    | reg _ _ => simpa only [hlabel, Bool.false_eq_true, ↓reduceIte] using hh
    | low _ _ _ => simpa only [hlabel, Bool.false_eq_true, ↓reduceIte] using hh
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


theorem choice_prefix [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112e5a)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l11893a initial).arguments
      initial.external (coreReturned fr p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x119070 ∧ RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l126f60 final).arguments final.external
        (choiceCall fr p) := by
  have hi : (layout fr).Rel code () ⟨.middle, #v[], p⟩
      (Machine.lifted.locationOf .l11893a initial) := ⟨rfl, ⟨p, rfl, rfl, hcore⟩, hframe⟩
  have sim := Machine.simulation code hcode hout
  have hb := call_block true code hcode fr () #v[] p _ hi
  change Ahead Machine.lifted code _ _ at hb
  obtain ⟨fuel, final, callee, frame, he, hrel, c', hcall, _⟩ :=
    Core.Support.ahead_call_advances sim
      (Rel.locationOf (P := Machine.lifted) (l := .l11893a) hready hrip) hb
  obtain ⟨p', _, hp, hatoms⟩ := hcall.params
  change p = p' at hp
  subst p'
  have hlabel : callee.label = .l126f60 := hcall.label
  change Atom.All code callee.arguments callee.store (choiceCall fr p) at hatoms
  rw [hrel.store] at hatoms
  have ha := Core.Support.atoms_locationOf hrel (by
    intro atom hh
    have hh := call_live true fr p atom hh
    cases atom with
    | reg _ _ => simpa only [hlabel, Bool.false_eq_true, ↓reduceIte] using hh
    | low _ _ _ => simpa only [hlabel, Bool.false_eq_true, ↓reduceIte] using hh
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


end P256.Proofs.Scalar.Inverse.Wrapper
