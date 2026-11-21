import P256.Proofs.Signing.Wrapper.Finish.Pops
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem restore [bindings : Bindings] {initial t : RamState} (pre : Pre initial)
    (state : State initial t) (low : (returnBoundary initial).rip.toNat < 2^32)
    (rip : t.RIP = 0x102b19) :
    ∃ u, Returns (returnBoundary initial) 8 t u ∧
      SupportedIntegerMachineState bindings.processor u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      CalleeSavedRegistersUnchanged initial u ∧ DirectionFlagUnset u ∧
      u.external = t.external ∧ u.regValue .rax = t.regValue .rax := by
  obtain ⟨v,run,ready,effect⟩ :=
    (add_r64_imm32_effect_step 0x102b19 0x48 0xc4 472
      (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x2b19 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outside (inProgram_of_textOffset 0x2b20 (by decide)))
  change (addR64Imm32Effect 0x102b19 4 472 t).Holds t v at effect
  have memory : v.external = t.external := effect.agrees.external (by simp [Component.Covers])
  have sp : stackPtr v = stackPtr initial-48 := by
    have hw : stackPtr v = stackPtr t+472 := effect.writes
    rw [hw,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have saved : ∀ item ∈ savedRegisters,
      memLoad v.external (stackPtr initial-BitVec.ofNat 64 item.2) 64 = initial.regValue item.1 := by
    intro item hi
    rw [memory]
    simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact state.savedRbx
    · exact state.savedR12
    · exact state.savedR13
    · exact state.savedR14
    · exact state.savedR15
    · exact state.savedRbp
  obtain ⟨u,returned,readyU,frame,regs⟩ := restore_registers ready
    (by simpa only [ProgramLoaded,memory] using state.loaded) pre.outside low
    sp
    (fun off bound => (readable_of_grow
      (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated).of_external_eq memory)
    saved (by simpa only [memory] using state.returnAddress)
    (codeOffset := 0x2b20)
    ⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,
      by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩ effect.rip
  have ag := effect.agrees.trans frame
  exact ⟨u,run.returns returned,
    supportedMachine_of_ready_agrees state.machine readyU ag,
    bindingsSupported_of_ready_agrees state.bindingsSupported readyU ag,regs,
    ag.directionFlagClear (by simp [restoreComponents]) state.directionFlag,
    ag.external (by simp [restoreComponents,Component.Covers]),
    ag.read (n := 64) (r := 0) (by simp [restoreComponents])⟩

end P256.Proofs.Signing.Wrapper.Finish
