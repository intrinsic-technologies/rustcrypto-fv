import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Frame

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4#5 : Operand 64).read s := rfl

theorem firstProducts_pointer {p : BitVec 64} {s t : RamState}
    (h : (firstProductsEffect p s).Holds s t) :
    (Operand.mem (stackPtr t+24#64) : Operand 64).read t =
      (Operand.mem (stackPtr s+24#64) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstProducts_frame h)]
  have hf : ∀ w ∈ (firstProductsEffect p s).writes, w.Full := by
    simp [firstProductsEffect, Write.Full, Operand.Full]
  have hp := (h.obsAfter hf true).read (Operand.mem (stackPtr s+24#64) : Operand 64) (by trivial)
  x86_norm [firstProductsEffect, stackPtr_read] at hp
  exact hp.symm

theorem firstCarry_pointer {p : BitVec 64} {s t : RamState}
    (h : (firstCarryEffect p s).Holds s t) :
    (Operand.mem (stackPtr t+24#64) : Operand 64).read t =
      (Operand.mem (stackPtr s+24#64) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstCarry_frame h)]
  have hf : ∀ w ∈ (firstCarryEffect p s).writes, w.Full := by
    simp [firstCarryEffect, Write.Full, Operand.Full]
  have hp := (h.obsAfter hf true).read (Operand.mem (stackPtr s+24#64) : Operand 64) (by trivial)
  x86_norm [firstCarryEffect, stackPtr_read] at hp
  exact hp.symm

theorem firstMiddle_pointer {p : BitVec 64} {s t : RamState}
    (h : (firstMiddleEffect p s).Holds s t) :
    (Operand.mem (stackPtr t+24#64) : Operand 64).read t =
      (Operand.mem (stackPtr s+24#64) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstMiddle_frame h)]
  have hf : ∀ w ∈ (firstMiddleEffect p s).writes, w.Full := by
    simp [firstMiddleEffect, Write.Full, Operand.Full]
  have hp := (h.obsAfter hf true).read (Operand.mem (stackPtr s+24#64) : Operand 64) (by trivial)
  x86_norm [firstMiddleEffect, stackPtr_read] at hp
  exact hp.symm

theorem firstHigh_pointer {p : BitVec 64} {s t : RamState}
    (h : (firstHighEffect p s).Holds s t) :
    (Operand.mem (stackPtr t+24#64) : Operand 64).read t =
      (Operand.mem (stackPtr s+24#64) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstHigh_frame h)]
  have hf : ∀ w ∈ (firstHighEffect p s).writes, w.Full := by
    simp [firstHighEffect, Write.Full, Operand.Full]
  have hp := (h.obsAfter hf true).read (Operand.mem (stackPtr s+24#64) : Operand 64) (by trivial)
  x86_norm [firstHighEffect, stackPtr_read] at hp
  exact hp.symm

end P256.Proofs.Sec1.SquareRoot.Montgomery
