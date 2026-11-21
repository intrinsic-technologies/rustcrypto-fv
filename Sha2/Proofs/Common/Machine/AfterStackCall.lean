import Sha2.Proofs.Common.Machine.CallState
import Sha2.Proofs.Common.Machine.StackCall

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem callee_pre_after_stack_call [bindings : Bindings] {initial s u : RamState}
    {n outerReserve frameOffset inputBytes outputBytes reserve : Nat}
    {regions : Vector MemoryRegion n} {entry ret : BitVec 64}
    (stride : UnitStringStride bindings) (initialMachine : SupportedMachine bindings initial)
    (stack : Stack.Valid initial outerReserve)
    (avoids : (Stack.region initial outerReserve).Avoids
      (fun a => InProgram a ∨ InPageTables a)) (returnAddress : ValidReturnAddress initial)
    (state : ExecutionState initial s regions)
    (layout : Sha2.Proofs.Wrapper.StackCallLayout outerReserve inputBytes outputBytes reserve)
    (offset : layout.stackOffset = frameOffset + 8)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 frameOffset)
    (input : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (ready : ReadyToStep u) (effect : (callEffect (fun _ => entry) ret s).Holds s u)
    (returnInside : InProgram ret) :
    CalleePre u (returnBoundary initial) entry inputBytes outputBytes reserve := by
  have slot : pushAddr s = stackPtr initial - BitVec.ofNat 64 layout.stackOffset := by
    rw [pushAddr, rsp, offset, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have capacity : frameOffset + 8 ≤ outerReserve := by
    have h := layout.capacity
    rw [offset] at h
    omega
  exact callee_pre_of_stack stride initialMachine stack avoids returnAddress
    (supportedMachine_of_ready_agrees state.machine ready effect.agrees)
    (effect.agrees.directionFlagClear (by simp [callEffect, pushEffect_components]) state.directionFlag)
    (loaded_after_call stack avoids state rsp capacity effect)
    (fun a ha => effect.agrees.grow a (state.allocated a ha)) layout effect.rip
    (effect.writes.1.trans slot)
    ((effect.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans input)
    ((effect.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans output)
    (by change InProgram (stackTop u)
        rw [(callEffect_stack effect).1]
        exact returnInside)

end Sha2.Proofs.Common.Machine
