import Sha2.Proofs.Common.Machine.InputCall
import Sha2.Proofs.Common.Machine.CallState
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem callee_pre_after_call [bindings : Bindings] {initial s u : RamState}
    {n outerReserve frameOffset outputOffset inputBytes outputBytes reserve : Nat}
    {regions : Vector MemoryRegion n} {entry ret : BitVec 64}
    (stride : UnitStringStride bindings) (initialMachine : SupportedMachine bindings initial)
    (stack : Stack.Valid initial outerReserve)
    (avoids : (Stack.region initial outerReserve).Avoids
      (fun a => InProgram a ∨ InPageTables a)) (returnAddress : ValidReturnAddress initial)
    (state : ExecutionState initial s regions)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 frameOffset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (aligned : (frameOffset + 8) % 16 = 0)
    (capacity : frameOffset + 8 + reserve ≤ outerReserve)
    (outputAbove : outputOffset ≤ frameOffset) (outputEnd : outputBytes ≤ outputOffset + 8)
    (inputBounded : (registerRegion s .rsi inputBytes).Bounded)
    (inputAllocated : (registerRegion s .rsi inputBytes).Allocated s.external)
    (inputApart : (registerRegion s .rsi inputBytes).Disjoint (Stack.region initial outerReserve))
    (ready : ReadyToStep u) (effect : (callEffect (fun _ => entry) ret s).Holds s u)
    (returnInside : InProgram ret) :
    CalleePre u (returnBoundary initial) entry inputBytes outputBytes reserve := by
  have slot : pushAddr s = stackPtr initial - BitVec.ofNat 64 (frameOffset + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have loaded := loaded_after_call stack avoids state rsp (by omega) effect
  have source : u.regValue .rsi = s.regValue .rsi :=
    effect.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])
  have outputU : u.regValue .rdi = s.regValue .rdi :=
    effect.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])
  have inputSame : registerRegion u .rsi inputBytes = registerRegion s .rsi inputBytes := by
    simp only [registerRegion, source]
  apply callee_pre_of_input stride initialMachine stack avoids returnAddress
    (supportedMachine_of_ready_agrees state.machine ready effect.agrees)
    (effect.agrees.directionFlagClear (by simp [callEffect, pushEffect_components]) state.directionFlag)
    loaded (fun a ha => effect.agrees.grow a (state.allocated a ha))
    (frameOffset + 8) outputOffset aligned capacity (by omega) outputEnd
    (inputSame ▸ inputBounded) ?_ (inputSame ▸ inputApart) effect.rip
    (effect.writes.1.trans slot) (outputU.trans output)
    (by change InProgram (stackTop u)
        rw [(callEffect_stack effect).1]
        exact returnInside)
  rw [inputSame]
  intro a member
  obtain ⟨b, byte⟩ := inputAllocated a member
  exact Option.isSome_iff_exists.mp (effect.agrees.grow a (by rw [byte]; rfl))

end Sha2.Proofs.Common.Machine
