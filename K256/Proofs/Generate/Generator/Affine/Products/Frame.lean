import K256.Proofs.Generate.Generator.Affine.State
import K256.Proofs.Sec1.Tactic.Lemma.Refine
import K256.Proofs.Common.Refine.Lemma.Region

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

def ProductScratch (fr : Activation) (regions : List MemoryRegion) : Prop :=
  ∀ r ∈ regions, fr.rsp.toNat - 976 ≤ r.start ∧ r.start + r.size ≤ fr.rsp.toNat - 48

theorem Coordinates.afterScratch {m n : Ram} {fr : Activation} {rs : List MemoryRegion}
    {x y z : Fin modulus} (h : Coordinates m fr.rsi x y z) (f : RamWriteFrame m n rs)
    (bounds : ProductScratch fr rs) (src : fr.rsi = fr.rsp + 232)
    (high : fr.rsp.toNat + 352 ≤ 2^32) : Coordinates n fr.rsi x y z := by
  obtain ⟨⟨xl, yl, zl, hx, hy, hz, hs⟩⟩ := h
  refine ⟨xl, yl, zl, hx.of_frame f (by decide) ?_, hy.of_frame f (by decide) ?_,
    hz.of_frame f (by decide) ?_, hs⟩
  all_goals
    rw [src]
    simp only [Outside, BitVec.toNat_add, BitVec.reduceToNat, Nat.reduceDiv, Nat.reduceMul]
    constructor
    · omega
    · intro r hr
      have := (bounds r hr).2
      omega

theorem State.afterProductScratch {fr : Activation} {a b : Registers} {m n : Ram}
    {rs : List MemoryRegion} {l l' : Label} (s : State l fr a m)
    (before : Atom.All Extracted.programImage a m (Fn10fe50.frameAt .l10eda1 fr))
    (target : Fn10fe50.frameAt l' fr = Fn10fe50.frameAt .l10eda1 fr)
    (f : RamWriteFrame m n rs) (bounds : ProductScratch fr rs)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [4,22,3,14,39,50,51] → b[i] = a[i]) :
    State l' fr b n := by
  obtain ⟨sp, df, bx, r14, mx, ft, fc, s48, s40, s32, s24, s16, s8, read, ret, low,
    win, room, align, _⟩ := before
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  change fr.low.toNat + 976 ≤ fr.rsp.toNat at room
  have off {d : Nat} (hd : d ≤ 976) :
      (fr.rsp - BitVec.ofNat 64 d).toNat = fr.rsp.toNat - d := by
    have h : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 d).toNat ≤ _; omega), h]
  have high := s.high
  have same (d : Nat) (hd : d ≤ 48) :
      memLoad n (fr.rsp - BitVec.ofNat 64 d) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 d) 64 := by
    apply f.memLoad_eq
    refine ⟨?_, fun r hr => Or.inr ?_⟩ <;> rw [off (by omega : d ≤ 976)]
    · omega
    · have := (bounds r hr).2
      omega
  have same0 := same 0 (by decide)
  change memLoad n (fr.rsp - 0) 64 = memLoad m (fr.rsp - 0) 64 at same0
  rw [show fr.rsp - 0 = fr.rsp by bv_omega] at same0
  refine ⟨?_, ?_, s.source.of_frame f, s.dest.of_frame f, s.srcAddr, s.dstAddr, high,
    s.frame.trans f ?_⟩
  · rw [target]
    exact ⟨(kept 4 (by decide)).trans sp, (kept 22 (by decide)).trans df,
      (kept 3 (by decide)).trans bx, (kept 14 (by decide)).trans r14,
      (kept 39 (by decide)).trans mx, (kept 50 (by decide)).trans ft, (kept 51 (by decide)).trans fc,
      (same 48 (by decide)).trans s48, (same 40 (by decide)).trans s40,
      (same 32 (by decide)).trans s32, (same 24 (by decide)).trans s24,
      (same 16 (by decide)).trans s16, (same 8 (by decide)).trans s8,
      Readable.of_frame read f, same0.trans ret,
      low, win.of_frame f, room, align, trivial⟩
  · intro v hv
    refine (f.outside v.1 ⟨by have := v.1.isLt; omega, fun r hr => ?_⟩).trans (s.image v hv)
    have bound := bounds r hr
    apply Classical.byContradiction
    intro inside
    have atLow := off (d := 976) (by decide)
    let start := fr.rsp - (976 : Word)
    have hn : start.toNat = fr.rsp.toNat - 976 := atLow
    apply win.notCode v hv (v.1.toNat - start.toNat) (by omega)
    change v.1 = start + _
    rw [← ofNat_toNat_add]
    have eq : start.toNat + (v.1.toNat - start.toNat) = v.1.toNat := by omega
    rw [eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r hr
    have := bounds r hr
    exact ⟨fr.region, .head _, by change fr.low.toNat ≤ _; omega,
      by change _ ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat); omega⟩

end K256.Proofs.Generate.Generator.Affine
