import K256.Proofs.Generate.Generator.Multiply.Projective
import K256.Proofs.Common.Field.SqrtRepr
import K256.Proofs.Generate.Generator.Affine.Memory
import K256.Proofs.Sec1.Parser.Result.Copy

namespace K256.Proofs.Generate.Generator.Multiply.Projective

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Common.Field K256.Proofs.Refine

structure Stored (p : Projective) (mem : Ram) (base : Word) : Prop where
  coordinates : ∃ xl yl zl : Limbs,
    WordsAt mem base 64 xl ∧ WordsAt mem (base + 40) 64 yl ∧ WordsAt mem (base + 80) 64 zl ∧
    FieldRepr xl p.x 1 ∧ FieldRepr yl p.y 1 ∧ FieldRepr zl p.z 1

theorem Stored.projectiveAt {p : Projective} {mem : Ram} {base : Word} (s : p.Stored mem base) :
    Affine.ProjectiveAt mem base p.value := by
  obtain ⟨xl, yl, zl, hx, hy, hz, rx, ry, rz⟩ := s.coordinates
  exact ⟨p.x, p.y, p.z, xl, yl, zl, hx, hy, hz, rx.mono (by decide), ry.mono (by decide),
    rz.mono (by decide), rfl⟩

theorem Stored.of_word_copy {p : Projective} {m n : Ram} {src dst : Word}
    (h : p.Stored m src)
    (words : ∀ i : Fin 15, memLoad n (wordAddr dst 64 i.val) 64 =
      memLoad m (wordAddr src 64 i.val) 64) : p.Stored n dst := by
  obtain ⟨xl, yl, zl, wx, wy, wz, rx, ry, rz⟩ := h.coordinates
  have coord (k : Nat) (hk : k + 5 ≤ 15) {v : Limbs}
      (atSrc : WordsAt m (wordAddr src 64 k) 64 v) : WordsAt n (wordAddr dst 64 k) 64 v := by
    intro i hi
    have eq := words ⟨k+i, by omega⟩
    simp only [wordAddr, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc] at eq
    exact eq.trans (atSrc i hi)
  have copiedX : WordsAt n dst 64 xl := by
    simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      coord 0 (by decide) (by simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using wx)
  exact ⟨xl, yl, zl, copiedX, coord 5 (by decide) wy, coord 10 (by decide) wz, rx, ry, rz⟩

theorem Stored.of_frame {p : Projective} {m n : Ram} {base : Word}
    {rs : List MemoryRegion} (s : p.Stored m base)
    (frame : RamWriteFrame m n rs) (out : Outside rs base 120) : p.Stored n base := by
  apply s.of_word_copy
  intro i
  apply frame.memLoad_eq
  have room := out.1
  have hi := i.isLt
  have eq : (wordAddr base 64 i.val).toNat = base.toNat + 8*i.val := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8*i.val) (by omega), Nat.mod_eq_of_lt (by omega)]
  exact Affine.outside_subregion out (by omega) (by change _ + 8 ≤ _; omega)

theorem Stored.memCopy {p : Projective} {m : Ram} {src dst : Word} {off len : Nat}
    (s : p.Stored m (src + BitVec.ofNat 64 off)) (bound : len ≤ 2^64) (fits : off + 120 ≤ len) :
    p.Stored (Lift.memCopy m dst src len) (dst + BitVec.ofNat 64 off) := by
  apply s.of_word_copy
  intro i
  have hi := i.isLt
  simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc] using
    Sec1.Parser.Result.memLoad_memCopy (len := len) (off := off + 8*i.val) (width := 64)
      m dst src bound (by change _ + 8 ≤ len; omega)

end K256.Proofs.Generate.Generator.Multiply.Projective
