import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Common.Instructions.MemoryAlu.Add
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions.MemoryAlu

theorem add_count [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Program.Input}
    (ctx : Context (v := v) initial inputs) (input : Preserved (v := v) initial s) (rip : s.RIP = (v.pc 0x155)) :
    ∃ t, Preserved (v := v) initial t ∧ t.RIP = (v.pc 0x15d) ∧
      memLoad t.external (stackPtr initial - 56) 64 =
        memLoad s.external (stackPtr initial - 56) 64 + s.regValue .rdx ∧
      AgreesExcept [.mem (stackPtr initial - 56) 8, .flags, .rip] s t := by
  have address : (AddrMode.sib 4 none 0 (.d32 288)).addr s (v.pc 0x15d) = stackPtr initial - 56 := by
    change rspOf s + 288 = _
    exact stack_add input.rsp (by cases v <;> decide)
  have code := programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x155)
    [0x48,0x01,0x94,0x24,0x20,0x01,0,0] (by cases v <;> decide) (by cases v <;> decide +kernel)
  obtain ⟨t, run, ready, effect⟩ :=
    (add_m64_r64_effect_step (v.pc 0x155) 0x48 (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d32 288)) (by cases v <;> decide +kernel) rfl rfl).advances
      (supportedMachine_readyToStep input.machine) code
      ⟨rip, by
          change MemWritable s ((AddrMode.sib 4 none 0 (.d32 288)).addr s (v.pc 0x15d)) 8
          rw [address]
          exact stack_writable8 ctx input.toState (by cases v <;> decide) (by cases v <;> decide), by
          change RangeApart ((AddrMode.sib 4 none 0 (.d32 288)).addr s (v.pc 0x15d)) 8 (v.pc 0x155) 8
          rw [address]
          exact stack_codeApart ctx (codeOffset := (v.textOffset + 0x155)) (codeLen := 8)
            (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide)⟩
      (by
        change v.pc 0x155 + BitVec.ofNat 64 8 ≠ (returnBoundary initial).rip
        rw [Variant.pc_add]
        exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
          (Variant.pc_inProgram v (by decide)))
  have frame : AgreesExcept [.mem (stackPtr initial - 56) 8, .flags, .rip] s t := by
    have frame := effect.agrees
    x86_norm [addM64R64Effect, Effect.components] at frame
    change AgreesExcept [.mem (rspOf s + 288) 8,.flags,.rip] s t at frame
    have addr : rspOf s + 288 = stackPtr initial - 56 := stack_add input.rsp (by cases v <;> decide)
    simpa only [addr] using frame
  refine ⟨t, preserved_of_agrees ctx input run ready frame ?_ (by simp), (effect.rip.trans (Variant.pc_add v 0x155 8)), ?_, frame⟩
  · intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact local_memory (by cases v <;> decide) (by cases v <;> decide) (.inr (by cases v <;> decide)) a ha
    · exact ha.elim
    · exact ha.elim
  · have value := effect.writes
    change memLoad t.external (rspOf s + 288) 64 =
      memLoad s.external (rspOf s + 288) 64 + s.regValue .rdx at value
    have addr : rspOf s + 288 = stackPtr initial - 56 := stack_add input.rsp (by decide)
    simpa only [addr] using value

end Sha2.Proofs.Wrapper.Absorb.Blocks
