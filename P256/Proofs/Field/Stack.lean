import P256.Proofs.Field.Interface
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem BinaryFieldPre.of_stack_region [bindings : Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {entry : BitVec 64}
    {outerReserve reserve : Nat}
    (stack : Stack.Valid s outerReserve)
    (avoids : (Stack.region s outerReserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip)
    (layout : StackCallLayout outerReserve 32 32 reserve)
    (rightOffset : Nat) (rightAbove : rightOffset + 8 ≤ layout.stackOffset)
    (rightEnd : 32 ≤ rightOffset + 8)
    (rightApart : layout.outputOffset + 32 ≤ rightOffset ∨ rightOffset + 32 ≤ layout.outputOffset)
    (supported : MachineRamUnitStrideDecodable bindings t)
    (machine : SupportedIntegerMachineState bindings.processor t)
    (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS)
    (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = entry)
    (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.inputOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary t).rip) : BinaryFieldPre t boundary entry reserve := by
  have bounds := stack_bounds stack
  have capacity := layout.capacity
  have outputAbove := layout.outputAbove
  have outputEnd := layout.outputEnd
  have hr : (t.regValue .rdx).toNat = (stackPtr s).toNat - rightOffset := by
    rw [right]
    exact stack_sub_toNat stack (by omega)
  have hd : (t.regValue .rdi).toNat = (stackPtr s).toNat - layout.outputOffset := by
    rw [output]
    exact stack_sub_toNat stack (by omega)
  have hs : (stackPtr t).toNat = (stackPtr s).toNat - layout.stackOffset := by
    rw [rsp]
    exact stack_sub_toNat stack (by omega)
  refine {
    toCalleePre := CalleePre.of_stack_region stack avoids outside layout supported machine direction loaded grow
      rip rsp input output ret
    rightBounded := ?_, rightAllocated := ?_, rightOutput := ?_, rightStack := ?_ }
  · change (t.regValue .rdx).toNat + 32 < 2^32
    rw [hr]
    omega
  · intro a ha
    apply Option.isSome_iff_exists.mp (grow a (Option.isSome_iff_exists.mpr (stack.2.1 a ?_)))
    change (t.regValue .rdx).toNat ≤ a.toNat ∧ a.toNat < (t.regValue .rdx).toNat + 32 at ha
    rw [hr] at ha
    change (stackPtr s).toNat - outerReserve ≤ a.toNat ∧
      a.toNat < (Stack.region s outerReserve).start + (Stack.region s outerReserve).size
    rw [stack_region_end]
    constructor <;> omega
  · intro a ha hb
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at hb
    rw [hr] at ha
    rw [hd] at hb
    omega
  · intro a ha hb
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
    change (Stack.region t reserve).start ≤ a ∧
      a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
    rw [hr] at ha
    rw [stack_region_end, hs] at hb
    omega

theorem BinaryFieldPre.of_stack [bindings : Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {outerEntry entry : BitVec 64}
    {outerInput outerOutput outerReserve reserve : Nat} {inputRegister : Syntax.Reg}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister)
    (layout : StackCallLayout outerReserve 32 32 reserve)
    (rightOffset : Nat) (rightAbove : rightOffset + 8 ≤ layout.stackOffset)
    (rightEnd : 32 ≤ rightOffset + 8)
    (rightApart : layout.outputOffset + 32 ≤ rightOffset ∨ rightOffset + 32 ≤ layout.outputOffset)
    (supported : MachineRamUnitStrideDecodable bindings t)
    (machine : SupportedIntegerMachineState bindings.processor t)
    (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS)
    (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = entry)
    (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.inputOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary t).rip) : BinaryFieldPre t boundary entry reserve :=
  BinaryFieldPre.of_stack_region pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    layout rightOffset rightAbove rightEnd rightApart supported machine direction loaded grow
    rip rsp input right output ret

end P256.Proofs.Field
