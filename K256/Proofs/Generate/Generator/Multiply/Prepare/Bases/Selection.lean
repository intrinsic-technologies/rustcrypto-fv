import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Frame
import K256.Proofs.Common.Point.TableWords.Negate
import K256.Proofs.Generate.Generator.Multiply.Lookup.SelectCall

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.DomainParameters.Secp256k1 Common.Point.TableWords

def stageSelect (m : Ram) (t : Word) (flag : BitVec 8) (mag : Vector Word 4) (x y z : Limbs) : Ram :=
  let m := memStore m (t+0x1d0) flag
  let m := memStore m (t+0x290) mag[0]
  let m := memStore m (t+0x298) mag[1]
  let m := memStore m (t+0x2a0) mag[2]
  let m := memStore m (t+0x2a8) mag[3]
  let m := memStore m (t+0x410) z[4]
  let m := memStore m (t+0x408) z[3]
  let m := memStore m (t+0x400) z[2]
  let m := memStore m (t+0x3f8) z[1]
  let m := memStore m (t+0x3f0) z[0]
  let m := memStore m (t+0x3a8) x[1]
  let m := memStore m (t+0x3b0) x[2]
  let m := memStore m (t+0x3b8) x[3]
  let m := memStore m (t+0x3c0) x[4]
  let m := memStore m (t+0x3a0) x[0]
  let m := memStore m (t+0x3c8) (negateY y)[0]
  let m := memStore m (t+0x3d0) (negateY y)[1]
  let m := memStore m (t+0x3d8) (negateY y)[2]
  let m := memStore m (t+0x3e0) (negateY y)[3]
  memStore m (t+0x3e8) (negateY y)[4]


abbrev selectWrites : Spans := [(0x1d0,1),(0x290,32),(0x328,120),(0x3a0,120)]

theorem selectFrame {fr : Activation} {a : Registers} {d : Nat} (e : CoreEntry fr a d)
    (m : Ram) (flag : BitVec 8) (mag : Vector Word 4) (x y z : Limbs) :
    RamWriteFrame m (stageSelect m (sp fr) flag mag x y z) (writes fr selectWrites) := by
  unfold stageSelect
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 1000) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 992) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 984) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 976) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 968) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 928) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 960) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 952) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 944) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 936) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 1008) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 1016) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 1024) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 1032) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 1040) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 680) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 672) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 664) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 656) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := selectWrites) (i := 464) (size := 1) (by decide) (by decide))
  exact RamWriteFrame.refl _ _


private theorem readStage {m : Ram} {t : Word} {flag : BitVec 8} {mag : Vector Word 4} {x y z : Limbs} :
    let n := stageSelect m t flag mag x y z
    WordsAt n (t+0x290) 64 mag ∧ WordsAt n (t+0x3a0) 64 x ∧
    WordsAt n (t+0x3c8) 64 (negateY y) ∧ WordsAt n (t+0x3f0) 64 z := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro i hi
  all_goals have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  all_goals rcases h with rfl|rfl|rfl|rfl|rfl
  all_goals try omega
  all_goals
    simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,
      BitVec.add_zero]
    segment_words [stageSelect]

theorem stagedValues {m : Ram} {t : Word} (flag : BitVec 8) (mag : Vector Word 4)
    (x y z : Limbs) {p : Projective}
    (rx : FieldRepr x p.x 1) (ry : FieldRepr y p.y 1) (rz : FieldRepr z p.z 1) :
    let n := stageSelect m t flag mag x y z
    WordsAt n (t+0x290) 64 mag ∧ p.neg.Stored n (t+0x3a0) := by
  obtain ⟨w,wx,wy,wz⟩ := readStage (m := m) (t := t) (flag := flag) (mag := mag) (x := x) (y := y) (z := z)
  refine ⟨w,x,negateY y,z,wx,?_,?_,rx,negateY_repr ry,rz⟩
  · simpa only [Lift.reduceAddOffset,BitVec.reduceAdd] using wy
  · simpa only [Lift.reduceAddOffset,BitVec.reduceAdd] using wz

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
