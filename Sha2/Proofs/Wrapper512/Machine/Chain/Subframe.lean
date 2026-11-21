import Sha2.Proofs.Wrapper512.Machine.Chain.Entry
import Sha2.Proofs.Wrapper512.Machine.Stages.Subframe
import Sha2.Proofs.Wrapper512.Absorb.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Machine.Chain

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512
open Sha2.Proofs.Wrapper512.Absorb
open Sha2.Proofs.Wrapper512.Machine.Stages

 theorem after_subframe [bindings : Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs) (pushed : Pushed v initial s)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = v.pc 0xa)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 48) :
    ∃ t, State v initial t ∧ t.RIP = v.pc 0x11 ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 632 := by
  obtain ⟨t, run, readyT, loadedT, ripT, rspT, agrees⟩ :=
    subframe ctx ready loaded rip rsp
  have machineT : SupportedMachine bindings t :=
    supportedMachine_of_ready_agrees pushed.machine readyT agrees
  have allocatedT : ∀ a : BitVec 64, (initial.external[a]?).isSome →
      (t.external[a]?).isSome := fun a ha => agrees.grow a (pushed.allocated a ha)
  have savedT : SavedStackAt initial t := by
    apply SavedStackAt.of_bytes pushed.saved
    intro a ha
    have external : t.external = s.external :=
      agrees.external (by simp [Component.Covers])
    rw [external]
  have frameT : MemoryWriteFrame initial t
      #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes] := by
    apply memoryWriteFrame_trans pushed.frame
    apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact ha.elim
  have directionT : DirectionFlagUnset t :=
    agrees.directionFlagClear (by simp) pushed.directionFlag
  obtain ⟨fuel, execution⟩ := pushed.execution
  refine ⟨t, ⟨⟨fuel + 1, execution.trans run⟩, machineT, loadedT,
    allocatedT, savedT, directionT, frameT, rspT⟩, ripT, rspT⟩

end Sha2.Proofs.Wrapper512.Machine.Chain
