import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.FinishCopy
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Frame
import K256.Proofs.Common.Point.TableWords.Negate

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR
  K256.Proofs.Common.Field Common.Point.TableWords

def negativeRecord (m : Ram) (q : Word) (x y z : Limbs) : Ram :=
  let m := memStore m (q + 840) x[4]
  let m := memStore m (q + 832) x[3]
  let m := memStore m (q + 824) x[2]
  let m := memStore m (q + 816) x[1]
  let m := memStore m (q + 808) x[0]
  let m := memStore m (q + 920) z[4]
  let m := memStore m (q + 912) z[3]
  let m := memStore m (q + 904) z[2]
  let m := memStore m (q + 896) z[1]
  let m := memStore m (q + 888) z[0]
  let m := memStore m (q + 848) (negateY y)[0]
  let m := memStore m (q + 856) (negateY y)[1]
  let m := memStore m (q + 864) (negateY y)[2]
  let m := memStore m (q + 872) (negateY y)[3]
  memStore m (q + 880) (negateY y)[4]

theorem negativeRecord_frame {fr : Activation} {a : Registers} {d : Nat} (e : CoreEntry fr a d)
    (m : Ram) (x y z : Limbs) :
    RamWriteFrame m (negativeRecord m (sp fr) x y z) (Bases.writes fr [(808,120)]) := by
  unfold negativeRecord
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 880) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 872) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 864) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 856) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 848) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 888) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 896) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 904) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 912) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 920) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 808) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 816) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 824) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 832) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.inSlot e (xs := [(808,120)]) (i := 840) (size := 8) (by decide) (by decide))
  exact RamWriteFrame.refl _ _

theorem negativeRecord_stored {q : Word} {m : Ram} {p : Projective} {x y z : Limbs}
    (rx : FieldRepr x p.x 1) (ry : FieldRepr y p.y 1) (rz : FieldRepr z p.z 1) :
    p.neg.Stored (negativeRecord m q x y z) (q+808) := by
  refine ⟨x,negateY y,z,?_,?_,?_,rx,negateY_repr ry,rz⟩
  all_goals
    intro i hi
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,
      Lift.reduceAddOffset,BitVec.add_zero]
    segment_words [negativeRecord]

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
