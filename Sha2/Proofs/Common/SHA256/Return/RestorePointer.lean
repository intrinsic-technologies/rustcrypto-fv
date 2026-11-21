import Sha2.Proofs.Common.SHA256.Return.Store
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem restore_output_pointer [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt32} {input : ByteArray} {index count : Nat}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : LoopState initial current hash index count)
    (rip : current.RIP = 0x10dcc4) :
    ∃ next, Advances boundary 1 current next ∧
      OutputState initial next hash [] ∧ next.RIP = 0x10dccc := by
  have haddr : stackPtr current + 0xc0 = stackPtr initial - 144 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have readable : MemReadable current (stackPtr current + 0xc0) 8 := by
    rw [haddr]
    exact Sha2.Proofs.Common.Encoding.Serialize.readable_of_grow
      (Sha2.Proofs.Common.Encoding.Serialize.stack_sub_readable pre.toCalleePre
        (by decide) (by decide)) state.allocated
  obtain ⟨next, run, ready, effect⟩ :=
    (mov_r64_m64_effect_step 0x10dcc4 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 0xc0)) (by decide +kernel) rfl rfl).advances
      (supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded) 0xdcc4
        [0x48,0x8b,0xbc,0x24,0xc0,0,0,0] (by decide) (by decide +kernel))
      ⟨rip, readable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xdccc (by decide)))
  have frame : AgreesExcept [.reg 7, .rip] current next := effect.agrees
  refine ⟨next, run, ?_, effect.rip⟩
  refine ⟨state.toFrameState.after_registers ready frame (by simp [Component.Covers]) (by simp),
    state.registers.after_output frame ?_, ?_, by simp⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · have hw : next.regValue .rdi = memLoad current.external (stackPtr current + 0xc0) 64 :=
      effect.writes
    exact hw.trans state.statePointer

end Sha2.Proofs.Common.SHA256
