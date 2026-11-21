import P256.Proofs.Nonce.Fill.Tail.Finish.Return
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Restore
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Signing.Search
open P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
  (RestoreState RestoreCode restoreComponents restore_registers)

theorem epilogue [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (stage : Serialized initial s orderAddress state) (rip : s.RIP = 0x1076fa) :
    ∃ t, Advances boundary 8 s t ∧
      ReturnState initial t orderAddress (nextCandidate state).1 (nextState state) := by
  obtain ⟨v, run, ready, effect⟩ :=
    (add_r64_imm32_effect_step 0x1076fa 0x48 0xc4 184
      (by constructor <;> decide) (by decide) (by decide)).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x76fa
        [0x48, 0x81, 0xc4, 0xb8, 0, 0, 0] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7701 (by decide)))
  change (addR64Imm32Effect 0x1076fa 4 184 s).Holds s v at effect
  have memory : v.external = s.external := effect.agrees.external (by simp [Component.Covers])
  have restore : RestoreState initial v := by
    refine ⟨bindingsSupported_of_ready_agrees stage.bindingsSupported ready effect.agrees,
      supportedMachine_of_ready_agrees stage.machine ready effect.agrees,
      ?_, fun a ha => effect.agrees.grow a (stage.allocated a ha), ?_, ?_, ?_⟩
    · intro a b hb
      rw [memory]
      exact stage.loaded a b hb
    · have hw : stackPtr v = stackPtr s + 184 := effect.writes
      rw [hw, stage.rsp, frameBase]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    · intro item hi
      rw [memory]
      exact stage.saved item hi
    · rw [memory]
      exact stage.returnAddress
  obtain ⟨t, run', ready', frame, rip', rsp', regs⟩ :=
    restore_registers pre.toCalleePre (by decide) restore (codeOffset := 0x7701)
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩ effect.rip
  have agrees := effect.agrees.trans frame
  have memory' : t.external = s.external :=
    (frame.external (by simp [restoreComponents, Component.Covers])).trans memory
  refine ⟨t, run.trans run', ⟨rip', rsp',
    bindingsSupported_of_ready_agrees stage.bindingsSupported ready' agrees,
    supportedMachine_of_ready_agrees stage.machine ready' agrees,
    regs, agrees.directionFlagClear (by component_not_mem) stage.directionFlag,
    (agrees.mxcsr (by component_not_mem)).trans stage.mxcsr,
    (agrees.fcw (by component_not_mem)).trans stage.fp87,
    ?_, ?_, fun a ha => agrees.grow a (stage.allocated a ha), ?_, ?_⟩⟩
  · intro a ha
    rw [memory']
    exact stage.frame a ha
  · intro a b hb
    rw [memory']
    exact stage.loaded a b hb
  · simpa only [memory'] using stage.output
  · simpa only [GeneratorAt, DrbgAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, memory'] using stage.generator

end P256.Proofs.Nonce.Fill.Tail.Finish
