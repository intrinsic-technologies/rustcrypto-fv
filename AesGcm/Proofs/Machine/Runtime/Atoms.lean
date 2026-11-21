import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Layout

namespace AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

def AtomPreserved (before after : Values Value Reg.count)
    (regions : List MemoryRegion) : Atom → Prop
  | .reg r _ => after[r] = before[r]
  | .low r w _ => after[r].get w = before[r].get w
  | .mem a w _ => Outside regions a (w / 8)
  | .words a w vs => ∀ i < vs.size, Outside regions (wordAddr a w i) (w / 8)
  | .readable _ _ => True
  | .writable _ _ => True
  | .fact _ => True

theorem atomHolds_of_frame {code : CodeMap} {before after : Values Value Reg.count}
    {original mem : Ram} {regions : List MemoryRegion} {atom : Atom}
    (hf : RamWriteFrame original mem regions)
    (hp : AtomPreserved before after regions atom)
    (h : atom.Holds code before original) : atom.Holds code after mem := by
  cases atom with
  | reg r v => exact hp.trans h
  | low r w v => exact hp.trans h
  | mem a w v => exact (hf.memLoad_eq hp).trans h
  | words a w vs =>
    intro i hi
    exact (hf.memLoad_eq (hp i hi)).trans (h i hi)
  | readable a n => exact h.of_frame hf
  | writable a n => exact h.of_frame hf
  | fact p => exact h

theorem atomsAll_of_frame {code : CodeMap} {before after : Values Value Reg.count}
    {original mem : Ram} {regions : List MemoryRegion} {atoms : List Atom}
    (hf : RamWriteFrame original mem regions)
    (hp : ∀ atom ∈ atoms, AtomPreserved before after regions atom)
    (h : Atom.All code before original atoms) : Atom.All code after mem atoms := by
  induction atoms with
  | nil => trivial
  | cons atom rest ih =>
    exact ⟨atomHolds_of_frame hf (hp atom (by simp)) h.1,
      ih (fun a ha => hp a (by simp [ha])) h.2⟩

theorem atomsAll_mem {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {atoms : List Atom} {atom : Atom}
    (h : Atom.All code args mem atoms) (ha : atom ∈ atoms) :
    atom.Holds code args mem := by
  induction atoms with
  | nil => cases ha
  | cons a rest ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact ih h.2 ha

end AesGcm.Proofs.Machine.Runtime
