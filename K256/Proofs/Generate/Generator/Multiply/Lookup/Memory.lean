import K256.Proofs.Generate.Generator.Multiply.Lookup.State
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field

theorem copyGuard {m : Ram} {s d pc : Word} (r : Readable m s 120)
    (w : StoreOk Extracted.programImage m d 120 pc 3)
    (apart : s.toNat + 120 ≤ d.toNat ∨ d.toNat + 120 ≤ s.toNat) :
    RepMovsOk Extracted.programImage m 0 s d 15 8 pc 3 :=
  ⟨rfl, r.low, w.low, r.present, w.present, apart, w.tables, w.apart, w.notCode⟩

theorem copyStored {m : Ram} {s d : Word} {p : Projective} (h : p.Stored m s) :
    p.Stored (memCopy m d s 120) d := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    (Projective.Stored.memCopy (off := 0) (len := 120) (dst := d) (src := s)
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h) (by decide) (by decide))

theorem frameAtomsAfter {fr : Activation} {a b : Registers} {m n : Ram} {areas : List MemoryRegion}
    (atoms : Atom.All Extracted.programImage a m (Fn11c510.frameAt .l11c6ed fr))
    (frame : RamWriteFrame m n areas)
    (below : ∀ r ∈ areas, r.start + r.size ≤ fr.rsp.toNat - 48)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [3,4,22,39,50,51] → b[i] = a[i]) :
    Atom.All Extracted.programImage b n (Fn11c510.frameAt .l11c6ed fr) := by
  simp only [Fn11c510.frameAt, Fn11c510.frameAtG1, Atom.All, Atom.Holds] at atoms ⊢
  obtain ⟨sp, df, bx, mx, ft, fc, s48, s40, s32, s24, s16, s8, rr, ret, rl, win, low, align, _⟩ := atoms
  have high := rr.low
  have same (off : Word) (h : off.toNat ≤ 48) :
      memLoad n (fr.rsp - off) 64 = memLoad m (fr.rsp - off) 64 := by
    have eq := BitVec.toNat_sub_of_le (x := fr.rsp) (y := off) (BitVec.le_def.mpr (by omega))
    apply frame.memLoad_eq
    refine ⟨by rw [eq]; omega, fun r hr => Or.inr ?_⟩
    have := below r hr
    rw [eq]
    omega
  have retEq : memLoad n fr.rsp 64 = memLoad m fr.rsp 64 := by
    simpa only [show fr.rsp - (0 : Word) = fr.rsp by bv_omega] using same 0 (by decide)
  exact ⟨(keep 4 (by decide)).trans sp, (keep 22 (by decide)).trans df, (keep 3 (by decide)).trans bx,
    (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft, (keep 51 (by decide)).trans fc,
    (same 48 (by decide)).trans s48, (same 40 (by decide)).trans s40, (same 32 (by decide)).trans s32,
    (same 24 (by decide)).trans s24, (same 16 (by decide)).trans s16, (same 8 (by decide)).trans s8,
    rr.of_frame frame, retEq.trans ret, rl, win.of_frame frame, low, align, trivial⟩

end K256.Proofs.Generate.Generator.Multiply.Lookup
