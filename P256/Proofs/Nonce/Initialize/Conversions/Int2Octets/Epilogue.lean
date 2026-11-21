import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Restore
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.State
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar

theorem finish_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {value : Nat} (pre : Pre s boundary) (stage : Stage s t boundary)
    (rip : t.RIP = 0x107093)
    (output : (registerRegion s .rdx 32).HasBytes t.external
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets P256.Spec.Operations.domain.n value)) :
    ∃ u, Result s u boundary value := by
  obtain ⟨v, run, ready, effect⟩ :=
    (add_r64_imm8_effect_step 0x107093 0x48 0xc4 24
      (by constructor <;> decide) (by decide) (by decide)).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7093
        [0x48, 0x83, 0xc4, 0x18] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7097 (by decide)))
  change (addR64Imm8Effect 0x107093 4 24 t).Holds t v at effect
  have memory : v.external = t.external := effect.agrees.external (by simp [Component.Covers])
  have restore : RestoreState s v := by
    refine ⟨bindingsSupported_of_ready_agrees stage.bindingsSupported ready effect.agrees,
      supportedMachine_of_ready_agrees stage.machine ready effect.agrees,
      ?_, fun a ha => effect.agrees.grow a (stage.allocated a ha), ?_, ?_, ?_⟩
    · intro a b hb
      rw [memory]
      exact stage.loaded a b hb
    · have hw : stackPtr v = stackPtr t + 24 := effect.writes
      rw [hw, stage.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    · intro item hi
      rw [memory]
      exact stage.saved item hi
    · rw [memory]
      exact stage.returnAddress
  obtain ⟨u, run', ready', frame, rip', rsp', regs⟩ :=
    restore_registers (stack_pre pre) (by decide) restore (codeOffset := 0x7097)
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩ effect.rip
  have agrees := effect.agrees.trans frame
  have memory' : u.external = t.external :=
    (frame.external (by simp [restoreComponents, Component.Covers])).trans memory
  obtain ⟨fuel, execution⟩ := stage.execution
  refine ⟨u, { execution := ⟨fuel + (1 + 7), execution.trans (run.trans run')⟩
               rip := rip'
               rsp := rsp'
               bindingsSupported := bindingsSupported_of_ready_agrees stage.bindingsSupported ready' agrees
               machine := supportedMachine_of_ready_agrees stage.machine ready' agrees
               calleeSaved := regs
               directionFlag := agrees.directionFlagClear (by component_not_mem) stage.directionFlag
               mxcsr := (agrees.mxcsr (by component_not_mem)).trans stage.mxcsr
               fp87 := (agrees.fcw (by component_not_mem)).trans stage.fp87
               frame := ?_
               loaded := ?_
               allocated := fun a ha => agrees.grow a (stage.allocated a ha)
               output := ?_ }⟩
  · intro a ha
    rw [memory']
    exact stage.frame a ha
  · intro a b hb
    rw [memory']
    exact stage.loaded a b hb
  · rw [memory']
    exact output

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
