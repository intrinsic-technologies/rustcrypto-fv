import Sha2.Proofs.Wrapper.Memory
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Partial

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem finish [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context (v := v) initial inputs) (input : Preserved (v := v) initial s) (rip : s.RIP = (v.pc 0x141)) :
    ∃ t, Preserved (v := v) initial t ∧ t.RIP = (v.pc 0x14c) ∧
      t.regValue .r13 = s.regValue .rbx ∧ t.external[stackPtr initial - 89]? = some 0 ∧
      AgreesExcept [.mem (stackPtr initial - 89) 1, .reg 13, .rip] s t := by
  have address : rspOf s + 255 = stackPtr initial - 89 := stack_add input.rsp (by cases v <;> decide)
  have writable : MemWritable s (rspOf s + 255) 1 := by
    rw [address]
    exact stack_writable1 ctx input.toState (by cases v <;> decide)
  have apart : RangeApart (rspOf s + 255) 1 (v.pc 0x141) 8 := by
    rw [address]
    exact stack_codeApart ctx (offset := 89) (len := 1) (codeOffset := (v.textOffset + 0x141)) (codeLen := 8)
      (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide)
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (mov_m8_imm8_effect_step (v.pc 0x141) (.sib 4 none 0 (.d32 255))
      (by cases v <;> decide +kernel) rfl rfl 0).advances (supportedMachine_readyToStep input.machine)
      (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x141) _ (by cases v <;> decide) (by cases v <;> decide +kernel))
      ⟨rip, writable, apart⟩
      (by
        change v.pc 0x141 + BitVec.ofNat 64 8 ≠ (returnBoundary initial).rip
        rw [Variant.pc_add]
        exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
          (Variant.pc_inProgram v (by decide)))
  have frameU : AgreesExcept [.mem (stackPtr initial - 89) 1, .rip] s u := by
    have h := effectU.agrees
    simp only [movM8Imm8Effect, storeEffect_components] at h
    change AgreesExcept [.mem (rspOf s + 255) 1, .rip] s u at h
    rwa [address] at h
  have preservedU := preserved_of_agrees ctx input runU readyU frameU (by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact local_memory (by cases v <;> decide) (by cases v <;> decide) (.inr (by cases v <;> decide)) a ha
    · exact ha.elim) (by simp)
  have byte : u.external[stackPtr initial - 89]? = some 0 := by
    have value := effectU.writes
    change memLoad u.external (rspOf s + 255) 8 = 0 at value
    have allocated : ∀ i < 1, (u.external[rspOf s + 255 + BitVec.ofNat 64 i]?).isSome :=
      fun i hi => effectU.agrees.grow _ (writable.mem i hi)
    have stored := Bytes.of_memLoad (n := 8) allocated 0 (by cases v <;> decide)
    rw [value] at stored
    rw [BitVec.add_zero, address] at stored
    simpa [storedByte] using stored
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (mov_r64_r64_effect_step (v.pc 0x149) 0x49 0xdd (by simp [RexWPrefix]) rfl).advances
      (supportedMachine_readyToStep preservedU.machine)
      (programText_slice (programLoaded_codeIn preservedU.loaded) (v.textOffset + 0x149) _ (by cases v <;> decide) (by cases v <;> decide +kernel))
      (effectU.rip.trans (Variant.pc_add v 0x141 8))
      (by
        change v.pc 0x149 + BitVec.ofNat 64 3 ≠ (returnBoundary initial).rip
        rw [Variant.pc_add]
        exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
          (Variant.pc_inProgram v (by decide)))
  have frameT : AgreesExcept [.reg 13, .rip] u t := effectT.agrees
  have preservedT := preserved_of_agrees ctx preservedU runT readyT frameT
    (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact ha.elim) (by simp)
  refine ⟨t, preservedT, (effectT.rip.trans (Variant.pc_add v 0x149 3)), ?_, ?_, ?_⟩
  · exact effectT.writes.trans (frameU.read (n := 64) (r := 3) (by simp))
  · exact (frameT.byte (by simp [Component.Covers])).trans byte
  · exact (frameU.trans frameT).mono (by simp)


end Sha2.Proofs.Wrapper.Absorb.Partial
