import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Common.Instructions.MemoryAlu.Inc

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Partial

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions.MemoryAlu

theorem increment [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context (v := v) initial inputs) (input : Preserved (v := v) initial s) (rip : s.RIP = (v.pc 0x11f)) :
    ∃ t, Preserved (v := v) initial t ∧ t.RIP = (v.pc 0x127) ∧
      memLoad t.external (stackPtr initial - 56) 64 =
        memLoad s.external (stackPtr initial - 56) 64 + 1 ∧
      AgreesExcept [.mem (stackPtr initial - 56) 8, .flags, .rip] s t := by
  have address : rspOf s + 288 = stackPtr initial - 56 := stack_add input.rsp (by cases v <;> decide)
  have writable : MemWritable s (rspOf s + 288) 8 := by
    rw [address]
    exact stack_writable8 ctx input.toState (by cases v <;> decide) (by cases v <;> decide)
  have apart : RangeApart (rspOf s + 288) 8 (v.pc 0x11f) 8 := by
    rw [address]
    exact stack_codeApart ctx (offset := 56) (len := 8) (codeOffset := (v.textOffset + 0x11f)) (codeLen := 8)
      (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide)
  obtain ⟨t, run, ready, effect⟩ :=
    (inc_m64_effect_step (v.pc 0x11f) 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d32 288)) (by cases v <;> decide +kernel) rfl rfl).advances
      (supportedMachine_readyToStep input.machine)
      (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x11f) _ (by cases v <;> decide) (by cases v <;> decide +kernel))
      ⟨rip, writable, apart⟩
      (by
        change v.pc 0x11f + BitVec.ofNat 64 8 ≠ (returnBoundary initial).rip
        rw [Variant.pc_add]
        exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
          (Variant.pc_inProgram v (by decide)))
  have frame : AgreesExcept [.mem (stackPtr initial - 56) 8, .flags, .rip] s t := by
    have h := effect.agrees
    simp only [incM64Effect, Effect.components, List.map_cons, List.map_nil, Write.component, Operand.component] at h
    change AgreesExcept [.mem (rspOf s + 288) 8, .flags, .rip] s t at h
    rwa [address] at h
  refine ⟨t, preserved_of_agrees ctx input run ready frame ?_ (by simp), (effect.rip.trans (Variant.pc_add v 0x11f 8)), ?_, frame⟩
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact local_memory (by cases v <;> decide) (by cases v <;> decide) (.inr (by cases v <;> decide)) a ha
    · exact ha.elim
    · exact ha.elim
  · have value := effect.writes
    change memLoad t.external (rspOf s + 288) 64 =
      memLoad s.external (rspOf s + 288) 64 + 1 at value
    rwa [address] at value


end Sha2.Proofs.Wrapper.Absorb.Partial
