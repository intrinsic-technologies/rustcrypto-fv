import P256.Proofs.Field.Inverse.SafeGcd.Core.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Support

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def MemoryStable (regions : List MemoryRegion) : Atom → Prop
  | .reg _ _ | .low _ _ _ => False
  | .mem a w _ => Outside regions a (w / 8)
  | .words a w vs => 0 < w / 8 ∧ Outside regions a (w / 8 * vs.size)
  | _ => True

theorem atom_of_frame {code : CodeMap} {args args' : Values Value Reg.count} {before after : Ram}
    {regions : List MemoryRegion} (hf : RamWriteFrame before after regions)
    (a : Atom) (hs : MemoryStable regions a) (h : Atom.Holds code args before a) :
    Atom.Holds code args' after a := by
  cases a with
  | reg _ _ => exact False.elim hs
  | low _ _ _ => exact False.elim hs
  | mem a w v => exact (hf.memLoad_eq hs).trans h
  | words a w vs => exact h.of_frame hf hs.1 hs.2
  | readable a len => exact h.of_frame hf
  | writable a len => exact h.of_frame hf
  | fact p => exact h

theorem atoms_of_frame {code : CodeMap} {args args' : Values Value Reg.count} {before after : Ram}
    {regions : List MemoryRegion} (hf : RamWriteFrame before after regions)
    (atoms : List Atom) (hs : ∀ a ∈ atoms, MemoryStable regions a)
    (h : Atom.All code args before atoms) : Atom.All code args' after atoms := by
  induction atoms with
  | nil => trivial
  | cons a as ih =>
    exact ⟨atom_of_frame hf a (hs a (by simp)) h.1,
      ih (fun a ha => hs a (by simp [ha])) h.2⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.Support
