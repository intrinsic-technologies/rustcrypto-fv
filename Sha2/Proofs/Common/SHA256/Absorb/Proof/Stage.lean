import Sha2.Proofs.Common.SHA256.Absorb.Proof.Frame

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem run_stage [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context l initial regions reserve) (input : Preserved l initial before s regions)
    (stage : Stage) (nonCall : stage.isCall = false) (rip : s.RIP = l.pc stage)
    (bufferRegister : ∀ r ∈ l.bufferSource, Blocks.readReg s r = l.buffer (l.sp initial))
    (bufferRestored : stage = .tailSetup →
      ∀ r ∈ l.bufferRestore, Blocks.readReg s r = l.buffer (l.sp initial)) :
    ∃ t, Preserved l initial before t regions ∧
      (stage.effect l (l.sp initial) s).Holds s t := by
  have pre : stage.Pre l (l.sp initial) s := by
    refine ⟨rip, input.rsp, ?_, ?_, ?_, ?_, bufferRegister, bufferRestored⟩
    · exact ctx.buffer_writable input.state (by decide : 63 + 1 ≤ 104) (by decide)
    · exact ctx.buffer_writable input.state (by decide : 96 + 8 ≤ 104) (by decide)
    · intro site member
      exact ctx.stage_codeApart input.state stage member (by decide : 63 + 1 ≤ 104)
    · intro site member
      exact ctx.stage_codeApart input.state stage member (by decide : 96 + 8 ≤ 104)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := ctx.blocks.run stage nonCall (l.sp initial) s
    (supportedMachine_readyToStep input.state.machine) (ctx.code.blocks stage s input.state.loaded) pre
  refine ⟨t, input.of_agrees ctx run ready effect.agrees (ctx.stage_writes stage) ?_ ?_, effect⟩
  · intro r _ kept member
    exact kept (ctx.flow.blockClobbers stage (l.sp initial) s r member)
  · cases stage <;> simp [Stage.effect, Blocks.effect, Effect.components,
      Write.component, Operand.component, testR64R64Effect, branchEffect,
      Common.Instructions.AddByte.addR8R8Effect, List.mem_map]

end Sha2.Proofs.Common.SHA256.Absorb
