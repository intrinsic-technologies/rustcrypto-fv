import P256.Proofs.Signing.Core.Iteration.Point.Add
import P256.Proofs.Signing.Core.Iteration.Point.Copy
import P256.Proofs.Projective.Multiply.Table

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply.Machine.Basepoint (basePoint)
open Projective.Multiply.Machine.Basepoint.TableSteps (PointCallResult)
open NextNonce (scalarFrame coreFrame base_add)

structure Registers (s t : RamState) (r14Offset : Nat) : Prop where
  rbp : t.regValue .rbp = frameBase s+528
  r13 : t.regValue .r13 = frameBase s+432
  r15 : t.regValue .r15 = frameBase s+1328
  rbx : t.regValue .rbx = frameBase s+BitVec.ofNat 64 r14Offset

theorem Registers.preserve {s t u : RamState} {offset : Nat}
    (regs : Registers s t offset)
    (same : ∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r) :
    Registers s u offset :=
  ⟨(same _ (by simp)).trans regs.rbp,(same _ (by simp)).trans regs.r13,
    (same _ (by simp)).trans regs.r15,(same _ (by simp)).trans regs.rbx⟩

theorem Registers.agrees {s t u : RamState} {offset : Nat} {cs : List Component}
    (regs : Registers s t offset) (same : AgreesExcept cs t u)
    (unchanged : ∀ r ∈ [3,5,13,15], Component.reg r ∉ cs) : Registers s u offset := by
  exact ⟨(same.read (n := 64) (r := 5) (unchanged 5 (by simp))).trans regs.rbp,
    (same.read (n := 64) (r := 13) (unchanged 13 (by simp))).trans regs.r13,
    (same.read (n := 64) (r := 15) (unchanged 15 (by simp))).trans regs.r15,
    (same.read (n := 64) (r := 3) (unchanged 3 (by simp))).trans regs.rbx⟩

def Prefix (s t : RamState) (count : Nat) : Prop :=
  ∀ i < count, ProjectiveAt t (frameBase s+BitVec.ofNat 64 (528+96*i))
    (Projective.tableEntry basePoint i)

theorem Prefix.of_external {s t u : RamState} {count : Nat}
    (entries : Prefix s t count) (memory : u.external = t.external) : Prefix s u count := by
  intro i hi
  exact (entries i hi).of_bytes_eq (by intros; rw [memory])

theorem Prefix.copy {s t u : RamState} {count offset : Nat}
    (entries : Prefix s t count) (same : AgreesExcept (copyComponents s offset) t u)
    (bound : offset+96 ≤ 2232) (countBound : count ≤ 8)
    (apart : offset+96 ≤ 528 ∨ 528+96*count ≤ offset) : Prefix s u count := by
  intro i hi
  exact copy_point same bound (by omega) (by omega) (entries i hi)

theorem Prefix.append {s t : RamState} {count : Nat}
    (entries : Prefix s t count)
    (value : ProjectiveAt t (frameBase s+BitVec.ofNat 64 (528+96*count))
      (Projective.tableEntry basePoint count)) : Prefix s t (count+1) := by
  intro i hi
  rcases Nat.lt_or_eq_of_le (by omega : i ≤ count) with h|rfl
  · exact entries i h
  · exact value

theorem call_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {point : Projective} {offset : Nat}
    (result : PointCallResult s t u boundary ret 952 point 65 4584 2280)
    (bound : offset ≤ 2280) (apart : offset < 1328 ∨ 1424 ≤ offset) :
    u.external[frameBase s+BitVec.ofNat 64 offset]? =
      t.external[frameBase s+BitVec.ofNat 64 offset]? := by
  have h := result.bytes (2280-offset) 1 (by omega) (by omega) (by omega) 0 (by decide)
  simpa only [← base_add s bound,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h

theorem call_preserved [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {point : Projective}
    (result : PointCallResult s t u boundary ret 952 point 65 4584 2280) : Preserved s t u := by
  intro i live
  exact call_byte result (by rcases live with h|h|h|h <;> omega)
    (by rcases live with h|h|h|h <;> omega)

theorem Prefix.call [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {point : Projective} {count : Nat}
    (entries : Prefix s t count) (bound : count ≤ 8)
    (result : PointCallResult s t u boundary ret 952 point 65 4584 2280) : Prefix s u count := by
  intro i hi
  apply (entries i hi).of_bytes_eq
  intro j hj
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using
    call_byte result (offset := 528+96*i+j) (by omega) (.inl (by omega))

end P256.Proofs.Signing.Core.Iteration.Point.Table
