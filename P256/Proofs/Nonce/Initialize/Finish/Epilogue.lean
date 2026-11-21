import P256.Proofs.Nonce.Initialize.State
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Restore
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Conversions.Int2Octets (RestoreState RestoreCode restoreComponents restore_registers)

theorem finish_epilogue [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : Nonce.InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107c68) :
    ∃ t, CalleeResult initial t boundary 72 2144 ∧ t.external = s.external := by
  obtain ⟨v, run, ready, effect⟩ :=
    (add_r64_imm32_effect_step 0x107c68 0x48 0xc4 232
      (by constructor <;> decide) (by decide) (by decide)).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7c68
        [0x48, 0x81, 0xc4, 0xe8, 0, 0, 0] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7c6f (by decide)))
  change (addR64Imm32Effect 0x107c68 4 232 s).Holds s v at effect
  have memory : v.external = s.external := effect.agrees.external (by simp [Component.Covers])
  have restore : RestoreState initial v := by
    refine ⟨bindingsSupported_of_ready_agrees stage.bindingsSupported ready effect.agrees,
      supportedMachine_of_ready_agrees stage.machine ready effect.agrees, ?_,
      fun a ha => effect.agrees.grow a (stage.allocated a ha), ?_, ?_, ?_⟩
    · intro a b hb
      rw [memory]
      exact stage.loaded a b hb
    · have hw : stackPtr v = stackPtr s + 232 := effect.writes
      rw [hw, stage.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    · intro item hi
      rw [memory]
      exact stage.saved item hi
    · rw [memory]
      exact stage.returnAddress
  obtain ⟨t, run', ready', frame, rip', rsp', regs⟩ :=
    restore_registers pre.toCalleePre (by decide) restore (codeOffset := 0x7c6f)
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩ effect.rip
  have agrees := effect.agrees.trans frame
  have memory' : t.external = s.external :=
    (frame.external (by simp [restoreComponents, Component.Covers])).trans memory
  obtain ⟨fuel, execution⟩ := stage.execution
  refine ⟨t, ⟨⟨fuel + (1 + 7), execution.trans (run.trans run')⟩, rip', rsp',
    bindingsSupported_of_ready_agrees stage.bindingsSupported ready' agrees,
    supportedMachine_of_ready_agrees stage.machine ready' agrees, regs,
    agrees.directionFlagClear (by component_not_mem) stage.directionFlag,
    (agrees.mxcsr (by component_not_mem)).trans stage.mxcsr,
    (agrees.fcw (by component_not_mem)).trans stage.fp87,
    ?_, ?_, fun a ha => agrees.grow a (stage.allocated a ha)⟩, memory'⟩
  · intro a ha
    rw [memory']
    exact stage.frame a ha
  · intro a b hb
    rw [memory']
    exact stage.loaded a b hb

end P256.Proofs.Nonce.Initialize
