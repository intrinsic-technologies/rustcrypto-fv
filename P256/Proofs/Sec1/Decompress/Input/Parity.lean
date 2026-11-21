import P256.Proofs.Sec1.Decompress.Input.Prologue

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem store_parity [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Decompress.Pre s boundary bytes odd)
    (state : Frame s u) (rip : u.RIP = 0x10fc11) :
    ∃ t, Advances boundary 1 u t ∧ Frame s t ∧ t.RIP = 0x10fc15 ∧
      memLoad t.external (stackPtr s - 332) 32 = (u.regValue .rdx).setWidth 32 ∧
      AgreesExcept [.mem (stackPtr s - 332) 4, .rip] u t := by
  have address : stackPtr u + 76 = stackPtr s - 332 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  obtain ⟨t, run, ready, effect⟩ :=
    (mov_m32_r32_legacy_effect_step_any 0x10fc11 2 (.sib 4 none 0 (.d8 76))
      (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xfc11 _
        (by decide) (by decide +kernel))
      ⟨rip, ScalarFrame.stack_writable pre.toCalleePre state
        (offset := 76) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre state
        (offset := 76) (len := 4) (codeOffset := 0xfc11) (codeLen := 4) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfc15 (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - 332) 4, .rip] u t := by
    have h := effect.agrees
    simp only [movM32R32LegacyEffect, storeEffect_components] at h
    change AgreesExcept [.mem (stackPtr u + 76) 4, .rip] u t at h
    rwa [address] at h
  have writes : WritesWithin [.mem (stackPtr s - 332) 4, .rip]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha⟩
    · exact ha.elim
  refine ⟨t, run, state.after_effect pre.toCalleePre (by decide) ready agrees writes
    (by simp), effect.rip, ?_, agrees⟩
  have value := effect.writes
  change memLoad t.external (stackPtr u + 76) 32 = _ at value
  rw [← address]
  exact value

end P256.Proofs.Sec1.Decompress.Input
