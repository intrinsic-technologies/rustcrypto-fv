import P256.Proofs.Sec1.Affine.Compact.Compare.Word0
import P256.Proofs.Sec1.Affine.Compact.Compare.Word1
import P256.Proofs.Sec1.Affine.Compact.Compare.Word2
import P256.Proofs.Sec1.Affine.Compact.Compare.Word3
import P256.Proofs.Sec1.Affine.Compact.Compare.Tail

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Compare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Field.Subtract (borrow subWord subRaw)

theorem compare_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {n y : Nat} (pre : AffineDecodePre s boundary bytes)
    (frame : Frame s t) (rip : t.RIP=0x1103d8)
    (left : Nat256At t (stackPtr s-416) n) (right : Nat256At t (stackPtr s-184) y)
    (zero : t.regValue .r13=0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP=0x1104ea ∧
      u.regValue .rax=(if n<y then 1 else 0) ∧
      (∀ r∈[Syntax.Reg.rbx,.rbp,.r12,.r14,.r15],u.regValue r=t.regValue r) ∧
      (∀ offset len,offset≤760 → len≤offset+8 → (offset+8≤512 ∨ 512+len≤offset) →
        ∀ i<len,u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?=
          t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) ∧
      AgreesExcept (clobbers s) t u := by
  let a := Field.readLimbs t (stackPtr s-416)
  let b := Field.readLimbs t (stackPtr s-184)
  have a0 : memLoad t.external ((stackPtr s-760)+344) 64=a.l0 := by
    dsimp [a,Field.readLimbs]
    apply congrArg (fun address ↦ memLoad t.external address 64)
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have b0 : memLoad t.external ((stackPtr s-760)+576) 64=b.l0 := by
    dsimp [b,Field.readLimbs]
    apply congrArg (fun address ↦ memLoad t.external address 64)
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  let q0 := borrow a.l0 b.l0 (a.l0-b.l0)
  obtain ⟨t1,run1,f1,ip1,v1,g1⟩ := word0 pre frame rip a.l0 b.l0 0 a0 b0
  have all1 : AgreesExcept (clobbers s) t t1 := g1.mono (by simp [clobbers])
  have a1 : memLoad t1.external ((stackPtr s-760)+352) 64=a.l1 := by
    have h := stack_word all1 408 (by decide) (by decide)
    have address : (stackPtr s-760)+352=stackPtr s-408 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [address]
    refine h.trans ?_
    dsimp [a,Field.readLimbs]
    apply congrArg (fun address ↦ memLoad t.external address 64)
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have b1 : memLoad t1.external ((stackPtr s-760)+584) 64=b.l1 := by
    have h := stack_word all1 176 (by decide) (by decide)
    have address : (stackPtr s-760)+584=stackPtr s-176 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [address]
    refine h.trans ?_
    dsimp [b,Field.readLimbs]
    apply congrArg (fun address ↦ memLoad t.external address 64)
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  let q1 := borrow a.l1 b.l1 (subWord a.l1 b.l1 q0)
  obtain ⟨t2,run2,f2,ip2,v2,g2⟩ := word1 pre f1 ip1 a.l1 b.l1 q0 a1 b1 v1
  have all2 : AgreesExcept (clobbers s) t t2 := (g1.trans g2).mono (by simp [clobbers])
  have a2 : memLoad t2.external ((stackPtr s-760)+360) 64=a.l2 := by
    have h := stack_word all2 400 (by decide) (by decide)
    have address : (stackPtr s-760)+360=stackPtr s-400 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [address]
    refine h.trans ?_
    dsimp [a,Field.readLimbs]
    apply congrArg (fun address ↦ memLoad t.external address 64)
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have b2 : memLoad t2.external ((stackPtr s-760)+592) 64=b.l2 := by
    have h := stack_word all2 168 (by decide) (by decide)
    have address : (stackPtr s-760)+592=stackPtr s-168 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [address]
    refine h.trans ?_
    dsimp [b,Field.readLimbs]
    apply congrArg (fun address ↦ memLoad t.external address 64)
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  let q2 := borrow a.l2 b.l2 (subWord a.l2 b.l2 q1)
  obtain ⟨t3,run3,f3,ip3,v3,g3⟩ := word2 pre f2 ip2 a.l2 b.l2 q1 a2 b2 v2
  have all3 : AgreesExcept (clobbers s) t t3 := ((g1.trans g2).trans g3).mono (by simp [clobbers])
  have a3 : memLoad t3.external ((stackPtr s-760)+368) 64=a.l3 := by
    have h := stack_word all3 392 (by decide) (by decide)
    have address : (stackPtr s-760)+368=stackPtr s-392 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [address]
    refine h.trans ?_
    dsimp [a,Field.readLimbs]
    apply congrArg (fun address ↦ memLoad t.external address 64)
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have b3 : memLoad t3.external ((stackPtr s-760)+600) 64=b.l3 := by
    have h := stack_word all3 160 (by decide) (by decide)
    have address : (stackPtr s-760)+600=stackPtr s-160 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [address]
    refine h.trans ?_
    dsimp [b,Field.readLimbs]
    apply congrArg (fun address ↦ memLoad t.external address 64)
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  let q3 := borrow a.l3 b.l3 (subWord a.l3 b.l3 q2)
  have zero3 : t3.regValue .r13=0 := (((g1.trans g2).trans g3).read (n := 64) (r := 13) (by simp)).trans zero
  obtain ⟨t4,run4,f4,ip4,v4,g4⟩ := word3 pre f3 ip3 a.l3 b.l3 q2 a3 b3 v3 zero3
  have all4 : AgreesExcept (clobbers s) t t4 := (((g1.trans g2).trans g3).trans g4).mono (by simp [clobbers])
  have value : memLoad t4.external (stackPtr s-512) 64=(if n<y then 1 else 0) := by
    have h : memLoad t4.external (stackPtr s-512) 64=(subRaw a b).2 := v4
    rw [h,borrow_eq a b,Field.readLimbs_toNat left,Field.readLimbs_toNat right]
  obtain ⟨u,run5,f5,ip5,ax5,g5⟩ := tail pre f4 ip4 (if n<y then 1 else 0)
    (by split <;> simp) value
  have agrees : AgreesExcept (clobbers s) t u := (all4.trans g5).mono (by simp)
  refine ⟨_,u,((((run1.trans run2).trans run3).trans run4).trans run5),f5,ip5,ax5,?_,?_,agrees⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact agrees.read (n := 64) (r := 3) (by simp [clobbers])
    · exact agrees.read (n := 64) (r := 5) (by simp [clobbers])
    · exact agrees.read (n := 64) (r := 12) (by simp [clobbers])
    · exact agrees.read (n := 64) (r := 14) (by simp [clobbers])
    · exact agrees.read (n := 64) (r := 15) (by simp [clobbers])
  · exact stack_bytes agrees

end P256.Proofs.Sec1.Affine.Compact.Compare
