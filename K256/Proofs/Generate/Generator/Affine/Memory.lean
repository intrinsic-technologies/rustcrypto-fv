import K256.Proofs.Generate.Generator.Affine.State
import K256.Proofs.Sec1.Tactic.Lemma.Refine

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field

def scratch (sp : Word) : MemoryRegion := ⟨(sp - 976).toNat, 976⟩

theorem sub_toNat {sp : Word} (room : 976 ≤ sp.toNat) (k : Word) (hk : k.toNat ≤ 976) :
    (sp - k).toNat = sp.toNat - k.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_trans hk room))

theorem add_toNat {sp : Word} (high : sp.toNat + 352 ≤ 2^32) (k : Word) (hk : k.toNat ≤ 352) :
    (sp + k).toNat = sp.toNat + k.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem scratch_image {sp : Word} {m m' : Ram}
    (w : Writable Extracted.programImage m (sp - 976) 976)
    (hf : RamWriteFrame m m' [scratch sp])
    (loaded : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) :
    ∀ b ∈ Extracted.programImage, m'[b.1]? = some b.2 := by
  intro b hb
  apply (hf.outside b.1 ?_).trans (loaded b hb)
  refine ⟨by have := b.1.isLt; omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  change b.1.toNat + 1 ≤ (sp - 976).toNat ∨ (sp - 976).toNat + 976 ≤ b.1.toNat
  by_cases lo : b.1.toNat < (sp - 976).toNat
  · exact Or.inl (by omega)
  · right
    apply Classical.byContradiction
    intro h
    have i := w.notCode b hb (b.1.toNat - (sp - 976).toNat) (by omega)
    apply i
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ - _) (by omega),
      Nat.add_sub_cancel' (by omega), Nat.mod_eq_of_lt b.1.isLt]

theorem outside_subregion {rs : List MemoryRegion} {a b : Word} {n k : Nat}
    (h : Outside rs a n) (l : a.toNat ≤ b.toNat) (u : b.toNat + k ≤ a.toNat + n) :
    Outside rs b k := by
  obtain ⟨low, apart⟩ := h
  exact ⟨by omega, fun r hr => by rcases apart r hr with _|_ <;> omega⟩

theorem Coordinates.of_frame {rs : List MemoryRegion} {m m' : Ram} {p : Word} {x y z : Fin modulus}
    (h : Coordinates m p x y z) (hf : RamWriteFrame m m' rs) (out : Outside rs p 120) :
    Coordinates m' p x y z := by
  obtain ⟨xl, yl, zl, wx, wy, wz, rx, ry, rz⟩ := h
  have shift (k : Word) (hk : k.toNat ≤ 80) :
      Outside rs (p + k) 40 := by
    have low := out.1
    have eq : (p + k).toNat = p.toNat + k.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact outside_subregion out (by omega) (by omega)
  exact ⟨xl, yl, zl, wx.of_frame hf (by decide) (outside_subregion out (Nat.le_refl _) (by omega)),
    wy.of_frame hf (by decide) (shift 40 (by decide)),
    wz.of_frame hf (by decide) (shift 80 (by decide)), rx, ry, rz⟩

end K256.Proofs.Generate.Generator.Affine
