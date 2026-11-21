import P256.Proofs.Program.Compare.Contract
import P256.Proofs.Program.Compare.Model
import P256.Proofs.Program.Compare.Stack

set_option autoImplicit false

namespace P256.Proofs.Program.Compare

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s : RamState} {boundary : ReturnBoundary} {size : Nat}

theorem ComparePre.callFrame (pre : ComparePre s boundary size) : CallFrame s 64 :=
  ⟨readyToStep pre.machine pre.bindingsSupported, programLoaded_codeIn pre.loaded,
    pre.stack, fun a ha hp ↦ pre.avoids _ (by simp) a ha (.inr hp),
    fun a ha hp ↦ pre.avoids _ (by simp) a ha (.inl hp), pre.directionFlag,
    inProgram_low pre.returnInProgram⟩

theorem ComparePre.callPre (allowed : size ∈ [1,33,39,65])
    (pre : ComparePre s boundary size) : CallPre s := by
  have frame := pre.callFrame
  have bounded : size < 2^64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
    rcases allowed with rfl | rfl | rfl | rfl <;> decide
  have small : ((Operand.reg 2 : Operand 64).read s).toNat % 16 < 8 := by
    rw [show (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 size from pre.count,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
    rcases allowed with rfl | rfl | rfl | rfl <;> decide
  refine ⟨pre.rip, small, frame, ?_, ?_, ?_, ?_⟩
  · rw [show (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 size from pre.count,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    exact memoryRegion_memReadable pre.leftBounded pre.leftAllocated (Nat.le_refl _)
      (Nat.le_refl _)
  · rw [show (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 size from pre.count,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    exact memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _)
      (Nat.le_refl _)
  · rw [show (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 size from pre.count,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    intro i hi j hj he
    apply pre.stackLeft _ (frame.stack_sub_contains (offset := 64) (len := 64)
      (by decide) (by decide) hi)
    simp only [BitVec.ofNat_eq_ofNat] at he ⊢
    rw [he]
    exact memoryRegion_contains_add pre.leftBounded (Nat.le_refl _) (Nat.le_refl _) hj
  · rw [show (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 size from pre.count,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    intro i hi j hj he
    have disjoint : (Stack.region s 64).Disjoint (registerRegion s .rsi size) :=
      fun a hs hi ↦ pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a hi hs
    apply disjoint _ (frame.stack_sub_contains (offset := 64) (len := 64)
      (by decide) (by decide) hi)
    simp only [BitVec.ofNat_eq_ofNat] at he ⊢
    rw [he]
    exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hj

theorem ComparePre.callBoundary (pre : ComparePre s boundary size) : CallBoundary boundary s :=
  ⟨pre.outerBoundary, boundary_ne_program pre.outerBoundary pre.returnInProgram⟩

end P256.Proofs.Program.Compare
