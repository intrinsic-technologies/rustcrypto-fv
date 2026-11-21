import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Borrow.Low
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Borrow.Middle
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Borrow.High
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Borrow.Top

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def borrowComponents (s : RamState) : List Component :=
  [.reg 3, .reg 5, .reg 8, .reg 9, .reg 11, .reg 13, .reg 14,
   .flags, .rip, .mem (stackPtr s + 8) 8]

theorem borrow_frame {s t : RamState} (h : AgreesExcept (borrowComponents s) s t) :
    AgreesExcept (scratchComponents s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [borrowComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Component.isMem, scratchComponents]
  · intro address c hc hv
    refine ⟨.mem (stackPtr s) 112, by simp [scratchComponents], ?_⟩
    simp only [borrowComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hv.elim | exact scratch_covered (offset := 8) (by decide) hv

theorem borrow_input {s t : RamState} {a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs} {high : BitVec 64}
    (h : AgreesExcept (borrowComponents s) s t) (input : Input s a high) : Input t a high := by
  constructor
  · exact (h.read (by simp [borrowComponents])).trans input.l0
  · exact (h.read (by simp [borrowComponents])).trans input.l1
  · exact (h.read (by simp [borrowComponents])).trans input.l2
  · exact (h.read (by simp [borrowComponents])).trans input.l3
  · exact (h.read (by simp [borrowComponents])).trans input.hi

theorem borrow_trans {s t u : RamState} (h₁ : AgreesExcept (borrowComponents s) s t)
    (h₂ : AgreesExcept (borrowComponents t) t u) : AgreesExcept (borrowComponents s) s u := by
  have hr := scratch_rsp (borrow_frame h₁)
  have he : borrowComponents t = borrowComponents s := by simp only [borrowComponents, hr]
  rw [he] at h₂
  exact (h₁.trans h₂).mono (by simp)

theorem borrowLow_frame {p : BitVec 64} {s t : RamState}
    (h : (borrowLowEffect p s).Holds s t) : AgreesExcept (borrowComponents s) s t := by
  exact h.agrees.mono (by simp [borrowComponents, borrowLowEffect, Effect.components])

theorem borrowMiddle_frame {p : BitVec 64} {s t : RamState}
    (h : (borrowMiddleEffect p s).Holds s t) : AgreesExcept (borrowComponents s) s t := by
  exact h.agrees.mono (by simp [borrowComponents, borrowMiddleEffect, Effect.components])

theorem borrowHigh_frame {p : BitVec 64} {s t : RamState}
    (h : (borrowHighEffect p s).Holds s t) : AgreesExcept (borrowComponents s) s t := by
  exact h.agrees.mono (by simp [borrowComponents, borrowHighEffect, Effect.components])

theorem borrowTop_frame {p : BitVec 64} {s t : RamState}
    (h : (borrowTopEffect p s).Holds s t) : AgreesExcept (borrowComponents s) s t := by
  exact h.agrees.mono (by simp [borrowComponents, borrowTopEffect, Effect.components])

theorem borrow_memory {s t : RamState} (h : AgreesExcept (borrowComponents s) s t)
    (offset : BitVec 64) (apart : OffsetsApart 8 8 offset 8) :
    (Operand.mem (stackPtr t + offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + offset) : Operand 64).read s := by
  rw [scratch_rsp (borrow_frame h)]
  apply memLoad_congr
  intro i hi
  simp only [memByte, PhysicalMemory.read]
  rw [h.memory _]
  intro c hc hv
  simp only [borrowComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  obtain ⟨j, hj, he⟩ := hv
  exact apart.ne (stackPtr s) hj hi (by decide) he.symm

theorem borrow_modulus {s t : RamState} {p : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs}
    (h : AgreesExcept (borrowComponents s) s t) (modulus : Modulus s p) : Modulus t p := by
  constructor
  · exact (borrow_memory h 32 (by unfold OffsetsApart; decide +kernel)).trans modulus.l0
  · exact (borrow_memory h 48 (by unfold OffsetsApart; decide +kernel)).trans modulus.l1
  · exact (borrow_memory h 40 (by unfold OffsetsApart; decide +kernel)).trans modulus.l2
  · exact (h.read (by simp [borrowComponents])).trans modulus.l3

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
