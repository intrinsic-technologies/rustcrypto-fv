import K256.Proofs.Sec1.Affine.Compressed.Phases
import K256.Proofs.Sec1.Parser.Result.Copy

namespace K256.Proofs.Sec1.Affine.Compressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR K256.Proofs.Common.Field K256.Proofs.Sec1.Serialize.Coordinates

def stagePoint (mem : Ram) (sp : Word) (xs : Limbs) : Ram :=
  let m := memStore mem (sp + 352) xs[0]
  let m := memStore m (sp + 360) xs[1]
  let m := memStore m (sp + 368) xs[2]
  let m := memStore m (sp + 376) xs[3]
  let m := memStore m (sp + 384) xs[4]
  memStore m (sp + 432) (0 : BitVec 8)

theorem skipStore (m : Ram) (sp o k : Word) {n : Nat} (v : BitVec n) (width : Nat)
    (h : n/8 ≤ (k-o).toNat ∧ width/8 ≤ (o-k).toNat) :
    memLoad (memStore m (sp+o) v) (sp+k) width = memLoad m (sp+k) width :=
  memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl h)

theorem stagedAffine (mem : Ram) (sp : Word) (xs ys : Limbs) (x y : Fin modulus) (m : Nat)
    (hx : FieldRepr xs x m) (hy : FieldRepr ys y m) (hm : WordsAt mem (sp+392) 64 ys) :
    Parser.AffineAt (stagePoint mem sp xs) (sp+352) x y m := by
  refine ⟨xs, ys, ?_, ?_, ?_, hx, hy⟩
  · intro i hi
    have idx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases idx with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [stagePoint, wordAddr, BitVec.add_assoc]
      simp (disch := decide +kernel) only [skipStore, BitVec.reduceAdd, Nat.reduceDiv, Nat.reduceMul]
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · have e : sp + 352 + 40 = sp + 392 := BitVec.add_assoc _ _ _
    rw [e]
    unfold stagePoint
    iterate 6
      apply WordsAt.write_apart
      case hap => exact RangeApart.of_offsets (x := sp) rfl rfl (by decide)
    exact hm
  · have e : sp + 352 + 80 = sp + 432 := BitVec.add_assoc _ _ _
    rw [e]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem copiedAffine {mem : Ram} {src dst : Word} {x y : Fin modulus} {mag : Nat}
    (h : Parser.AffineAt mem src x y mag) :
    Parser.AffineAt (memCopy mem dst src 88) dst x y mag :=
  h.of_copy (fun _ _ b => Parser.Result.memLoad_memCopy _ _ _ (by decide) b)

end K256.Proofs.Sec1.Affine.Compressed
