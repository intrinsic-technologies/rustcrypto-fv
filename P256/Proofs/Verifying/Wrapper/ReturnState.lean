import P256.Proofs.Verifying.Wrapper.Save
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ReturnState [bindings : Bindings] (initial s : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  loaded : ProgramLoaded s
  directionFlag : DirectionFlagUnset s
  rsp : stackPtr s = stackPtr initial - 280
  saved : ∀ entry ∈ savedRegisters,
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 entry.2) 64 = initial.regValue entry.1
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  rbp : s.regValue .rbp = initial.regValue .rbp
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome

theorem ReturnState.after_registers [Bindings] {initial s t : RamState} {cs : List Component}
    (state : ReturnState initial s) (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (registers : ∀ r ∈ ([4, 5] : List (BitVec 5)), Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : ReturnState initial t := by
  have hm := agrees.external memory
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear df state.directionFlag,
    (agrees.read (n := 64) (registers 4 (by simp))).trans state.rsp, ?_, ?_,
    (agrees.read (n := 64) (registers 5 (by simp))).trans state.rbp, ?_⟩
  · simpa only [ProgramLoaded, hm] using state.loaded
  · intro entry member
    simpa only [hm] using state.saved entry member
  · simpa only [hm] using state.returnAddress
  · intro a ha
    rw [hm]
    exact state.allocated a ha

end P256.Proofs.Verifying.Wrapper
