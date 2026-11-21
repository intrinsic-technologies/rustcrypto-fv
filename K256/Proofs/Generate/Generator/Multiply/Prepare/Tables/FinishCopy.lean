import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Induction

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR

def finishCopy (first : Bool) (q : BitVec 64) (m : Ram) :=
  memCopy (memCopy m (q+1048) (q+464) 120) (ptr q (entryOff first 7)) (q+1048) 120

set_option maxRecDepth 4096 in
theorem finished (first : Bool) {q : BitVec 64} {m : Ram} {p : Projective}
    (high : q.toNat+3256 ≤ 2^32) (tab : Partial first 7 q m p) :
    TableAt (finishCopy first q m) (q+offset first) p.value ∧
    RamWriteFrame m (finishCopy first q m) [⟨q.toNat+1048,120⟩,⟨q.toNat+entryOff first 7,120⟩] := by
  let rs : List MemoryRegion := [⟨q.toNat+1048,120⟩,⟨q.toNat+entryOff first 7,120⟩]
  have un : (q+1048).toNat = q.toNat+1048 := ptrNat high (by decide)
  have kb : entryOff first 7+120 ≤ 3088 := by cases first <;> decide
  have en := ptrNat (k := entryOff first 7) high (by omega)
  have delta : RamWriteFrame m (finishCopy first q m) rs := by
    apply Sec1.Wrapper.Copy.memCopy_frame
    · apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl m rs)
      exact ⟨_,.head _,by simp [InRegion]; omega⟩
    · exact ⟨_,.tail _ (.head _),by simp [InRegion,en]; omega⟩
  refine ⟨?_,delta⟩
  intro j
  have addr : q+offset first+BitVec.ofNat 64 (120*j.val) = ptr q (entryOff first j) := by
    cases first <;> simp only [offset,ptr,entryOff,ite_true,ite_false,Bool.false_eq_true,BitVec.ofNat_add,BitVec.add_assoc] <;> rfl
  rw [addr]
  by_cases e : j.val = 7
  · rw [e]
    obtain ⟨t,valid,stored,value⟩ := tab.next
    change t.Stored m (q+464) at stored
    exact ⟨t,valid,copyRecord (copyRecord stored),value⟩
  · have hj : j.val < 7 := by have := j.isLt; omega
    obtain ⟨t,v,stored,val⟩ := tab.entries _ hj
    refine ⟨t,v,stored.of_frame delta ?_,val⟩
    have bound : entryOff first j + 120 ≤ entryOff first 7 := by unfold entryOff; omega
    rw [show rs = [⟨q.toNat+1048,120⟩,⟨q.toNat+entryOff first 7,120⟩] from rfl]
    have jn := ptrNat (k := entryOff first j) high (by omega)
    have low : 1168 ≤ entryOff first j := by cases first <;> simp [entryOff] <;> omega
    simp [Outside,jn]; omega

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
