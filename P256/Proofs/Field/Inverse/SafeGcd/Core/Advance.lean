import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support
namespace P256.Proofs.Field.Inverse.SafeGcd.Core
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem advance_to [Bindings] {code : CodeMap} (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {boundary : ReturnBoundary} {entry exit : Machine.Label}
    {loc : Machine.lifted.Location} {atoms : List Atom} {original : Ram} {regions : List MemoryRegion}
    (hready : EntryReady code initial) (hrip : initial.RIP = Machine.lifted.address entry)
    (hout : ReturnOutside boundary code)
    (hreach : (Machine.lifted.program.sem (dialect code)).Reaches
      ⟨Machine.lifted.locationOf entry initial, []⟩ ⟨loc, []⟩)
    (hlabel : loc.label = exit) (hatoms : Atom.All code loc.arguments loc.store atoms)
    (hframe : RamWriteFrame original loc.store regions)
    (hlive : ∀ a ∈ atoms, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live exit) r | _ => True) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = Machine.lifted.address exit ∧ RamWriteFrame original final.external regions ∧
      Atom.All code (Machine.lifted.locationOf exit final).arguments final.external atoms := by
  obtain ⟨final, he, hr⟩ := (Machine.simulation code hcode hout).reaches hreach
    (Rel.locationOf (P := Machine.lifted) hready hrip)
  obtain ⟨fuel, hfuel⟩ := machine_reaches_iff.mp he
  rw [hr.store] at hatoms hframe
  have ha := Support.atoms_locationOf hr (by
    intro a h
    have hh := hlive a h
    cases a with
    | reg _ _ => simpa only [hlabel] using hh
    | low _ _ _ => simpa only [hlabel] using hh
    | mem _ _ _ => trivial
    | words _ _ _ => trivial
    | readable _ _ => trivial
    | writable _ _ => trivial
    | fact _ => trivial) hatoms
  rw [hlabel] at ha
  exact ⟨fuel, final, hfuel, ⟨hr.ready, hr.sse, hr.code⟩,
    by rw [hr.rip, hlabel], hframe, ha⟩
end P256.Proofs.Field.Inverse.SafeGcd.Core
