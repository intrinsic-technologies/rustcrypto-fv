import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Initialize
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Frame

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field.SquareRoot.Multiply

theorem scratch_apart_register [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (pre : CalleePre s boundary entry 32 32 160) (r : X86.Syntax.Reg)
    (bounded : (registerRegion s r 32).Bounded)
    (sep : (registerRegion s r 32).Disjoint (Stack.region s 160)) :
    RangeApart (stackPtr s-160) 112 (s.regValue r) 32 := by
  intro i hi j hj he
  have ha : (Stack.region s 160).Contains
      (stackPtr s-160+BitVec.ofNat 64 i).toNat := by
    apply scratch_inside pre (offset := 0) (len := 112) (by decide)
    exact ⟨i, hi, by rw [BitVec.add_zero]⟩
  have hb := memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hj
  rw [he] at ha
  exact sep _ hb ha

theorem initialize_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (he : Entry entry) (pre : MontgomeryPre s boundary entry)

    (ag : AgreesExcept (prologueComponents s) s t)
    (rip : t.RIP = entry+14#64) (rsp : stackPtr t = stackPtr s-160) :
    InitializePre (entry+14#64) t := by
  have h6 : (Operand.reg 6#5 : Operand 64).read t = (Operand.reg 6#5 : Operand 64).read s :=
    ag.read (by simp [prologueComponents])
  have h2 : (Operand.reg 2#5 : Operand 64).read t = (Operand.reg 2#5 : Operand 64).read s :=
    ag.read (by simp [prologueComponents])
  have h1 : (Operand.reg 1#5 : Operand 64).read t = (Operand.reg 1#5 : Operand 64).read s :=
    ag.read (by simp [prologueComponents])
  have mem := memoryPre pre.toCalleePre ag.grow rsp
    (ag.read (r := 7) (n := 64) (by simp [prologueComponents]))
  refine ⟨rip, mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := mem.scratch_apart he 0 112 14 initializeBytes.length (by decide) (by decide)
    simpa only [BitVec.add_zero] using h
  · rw [h6]
    exact readable_of_grow
      (memoryRegion_memReadable pre.inputBounded pre.inputAllocated
        (Nat.le_refl _) (Nat.le_refl _)) ag.grow
  · rw [h2]
    exact readable_of_grow
      (memoryRegion_memReadable pre.rightBounded pre.rightAllocated
        (Nat.le_refl _) (Nat.le_refl _)) ag.grow
  · rw [h1]
    exact readable_of_grow
      (memoryRegion_memReadable pre.modulusBounded pre.modulusAllocated
        (Nat.le_refl _) (Nat.le_refl _)) ag.grow
  · rw [rsp, h6]
    exact scratch_apart_register pre.toCalleePre .rsi pre.inputBounded
      (pre.separation (0 : Fin 3) (2 : Fin 3) (by decide))
  · rw [rsp, h2]
    exact scratch_apart_register pre.toCalleePre .rdx pre.rightBounded pre.rightStack
  · rw [rsp, h1]
    exact scratch_apart_register pre.toCalleePre .rcx pre.modulusBounded pre.modulusStack


end P256.Proofs.Sec1.SquareRoot.Montgomery
