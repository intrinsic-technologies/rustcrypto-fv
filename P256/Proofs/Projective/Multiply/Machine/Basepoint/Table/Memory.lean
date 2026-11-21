import P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Registers

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame TableSteps

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

theorem point_of_external {s t : RamState} {address : BitVec 64} {point : Projective}
    (atPoint : ProjectiveAt s address point) (memory : t.external = s.external) :
    ProjectiveAt t address point := atPoint.of_bytes_eq (by intros; rw [memory])

theorem copy_point [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {destination offset : Nat} {point : Projective}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (agrees : AgreesExcept (copyComponents s destination) t u)
    (destBound : destination ≤ 3352) (destSaved : 144 ≤ destination)
    (ho : offset ≤ 3352) (hl : 96 ≤ offset + 8)
    (apart : offset + 96 ≤ destination ∨ destination + 96 ≤ offset)
    (atPoint : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 offset) point) :
    ProjectiveAt u (stackPtr s - BitVec.ofNat 64 offset) point :=
  atPoint.of_bytes_eq (fun _ hi => copy_byte pre agrees destBound destSaved ho hl apart hi)

theorem call_point [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {destination offset : Nat} {point resultPoint : Projective}
    (result : PointCallResult s t u boundary ret destination resultPoint)
    (ho : offset ≤ 1944) (hl : 96 ≤ offset + 8)
    (apart : offset + 96 ≤ destination ∨ destination + 96 ≤ offset)
    (atPoint : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 offset) point) :
    ProjectiveAt u (stackPtr s - BitVec.ofNat 64 offset) point :=
  atPoint.of_bytes_eq (fun _ hi => result.bytes offset 96 ho hl apart _ hi)

theorem table_address (s : RamState) (i : Fin 8) :
    stackPtr s - 1680 + BitVec.ofNat 64 (96*i.val) =
      stackPtr s - BitVec.ofNat 64 (1680 - 96*i.val) := by
  have bound : 96*i.val ≤ 1680 := by have := i.isLt; omega
  rw [← BitVec.ofNat_sub_ofNat_of_le 1680 (96*i.val) (by omega) bound]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Table
