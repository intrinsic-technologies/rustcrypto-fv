import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Signed
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch.Routine

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

@[refine_layout] def afterBatchAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  Signed.residentAtoms fr controls p s ++
  [.gpr 9 ((BitVec.ofNat 32 (batchCount s)).setWidth 64),
   .gpr 3 (batchResult s).u, .gpr 15 (batchResult s).v,
   .gpr 13 (batchResult s).q, .gpr 14 (batchResult s).r, .gpr 12 (batchResult s).delta]

theorem empty_frame_eq {a b : Ram} (h : RamWriteFrame a b []) : b = a := by
  apply Std.ExtHashMap.ext_getElem?
  intro x
  apply h.outside
  exact ⟨by have hx := x.isLt; omega, by simp⟩

theorem resident_congr {code : CodeMap} {args args' : Values Value Reg.count} {mem : Ram}
    {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState}
    (h4 : args'[4] = args[4]) (h22 : args'[22] = args[22])
    (h39 : args'[39] = args[39]) (h51 : args'[51] = args[51])
    (h : Atom.All code args mem (Signed.residentAtoms fr controls p s)) :
    Atom.All code args' mem (Signed.residentAtoms fr controls p s) := by
  simp only [Signed.residentAtoms, Atom.all_append] at h ⊢
  refine ⟨⟨⟨⟨?_, h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩
  obtain ⟨r4, r22, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, r39, r51, _⟩ := h.1.1.1.1
  exact ⟨h4.trans r4, h22.trans r22, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, h39.trans r39, h51.trans r51, trivial⟩


set_option maxHeartbeats 800000 in
theorem batch_advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112625)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ s.remaining)
    (hcore : Atom.All code (Machine.lifted.locationOf .l114675 initial).arguments
      initial.external (Signed.finishAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x1122c1 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l114311 final).arguments final.external
        (afterBatchAtoms fr controls p s) := by
  rw [Signed.finishAtoms, Atom.all_append, Atom.all_append] at hcore
  have hresident := hcore.1.1
  have hr9 := hcore.1.2.1
  have hrsp := hresident
  simp only [Signed.residentAtoms, Atom.all_append] at hrsp
  have hf := hrsp.1.1.1.1
  have h4 := hf.1
  have h22 := hf.2.1
  have h39 := hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h51 := hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let bf : Activation := { fr with
    original := initial.external
    rsp := fr.rsp - 0x188
    r9 := (BitVec.ofNat 32 (batchCount s)).setWidth 64 }
  have ha : Atom.All code (Machine.lifted.locationOf .l114675 initial).arguments
      initial.external (Batch.loopAtoms bf controls (batchInput s) (batchCount s)) := by
    rw [Batch.loopAtoms, Atom.all_append]
    exact ⟨⟨h4, hr9, h22, h39, h51, trivial⟩, hcore.2⟩
  obtain ⟨fuel, final, he, ready, rip, frame, atoms⟩ := Batch.advances hcode hready hrip
    (fr := bf) (RamWriteFrame.refl _ []) hout (by simp only [batchCount]; omega)
    (by simp only [batchCount]; omega) ha
  have hm : final.external = initial.external := empty_frame_eq frame
  change Atom.All code _ _ (Batch.frameAtoms bf controls ++ _) at atoms
  rw [Atom.all_append] at atoms
  have hresident' : Atom.All code (Machine.lifted.locationOf .l114311 final).arguments
      final.external (Signed.residentAtoms fr controls p s) := by
    rw [hm]
    exact resident_congr (atoms.1.1.trans h4.symm) (atoms.1.2.2.1.trans h22.symm)
      (atoms.1.2.2.2.1.trans h39.symm) (atoms.1.2.2.2.2.1.trans h51.symm) hresident
  refine ⟨fuel, final, he, ready, rip, hm.symm ▸ hframe, ?_⟩
  rw [afterBatchAtoms, Atom.all_append]
  exact ⟨hresident', atoms.1.2.1, atoms.2⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare
