import P256.Proofs.Ecdh.Table.Support

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

def RegistersAt (t : RamState) : List (Syntax.Reg × BitVec 64) → Prop
  | [] => True
  | (r, v) :: rest => t.regValue r = v ∧ RegistersAt t rest

def PointsAt (s t : RamState) : List (Nat × Projective) → Prop
  | [] => True
  | (offset, point) :: rest =>
    ProjectiveAt t (stackPtr s - BitVec.ofNat 64 offset) point ∧ PointsAt s t rest

structure Facts (s t : RamState) (registers : List (Syntax.Reg × BitVec 64))
    (points : List (Nat × Projective)) : Prop where
  regs : RegistersAt t registers
  points : PointsAt s t points
  scalar : (Operand.mem (stackPtr s - 2048) : Operand 64).read t = s.regValue .rsi

theorem point_of_external {s t : RamState} {address : BitVec 64} {point : Projective}
    (atPoint : ProjectiveAt s address point) (memory : t.external = s.external) :
    ProjectiveAt t address point := atPoint.of_bytes_eq (by intros; rw [memory])

theorem table_address (s : RamState) (i : Fin 8) :
    frameBase s + 1016 + BitVec.ofNat 64 (96*i.val) =
      stackPtr s - BitVec.ofNat 64 (1040 - 96*i.val) := by
  have base : frameBase s+1016 = stackPtr s-1040 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  rw [base]
  have bound : 96*i.val ≤ 1040 := by have := i.isLt; omega
  rw [← BitVec.ofNat_sub_ofNat_of_le 1040 (96*i.val) (by omega) bound]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

end P256.Proofs.Ecdh.Table
