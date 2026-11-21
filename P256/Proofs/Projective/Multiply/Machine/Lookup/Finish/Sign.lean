import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Shift
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.State
import P256.Proofs.Common.Instructions.LegacyLoad
import P256.Proofs.Common.Instructions.MovzxByte

set_option autoImplicit false

open P256.Proofs.Common.Instructions.LegacyLoad (movR32M32LegacyEffect movR32M32LegacyEffect_components mov_r32_m32_legacy_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_effect_step)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions

theorem extract_sign [Bindings] {s t : RamState} {boundary : ReturnBoundary} {digit : BitVec 8}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (rip : t.RIP = 0x10482d)
    (saved : (Operand.mem (stackPtr s - 348) : Operand 32).read t = (s.regValue .rdx).setWidth 32)
    (hdigit : (s.regValue .rdx).setWidth 8 = digit) :
    ∃ u, Advances boundary 3 t u ∧ FrameState s u ∧ u.RIP = 0x104837 ∧
      u.regValue .rdi = (if digit.msb then 1 else 0) ∧
      AgreesExcept [.reg 0,.reg 7,.flags,.rip] t u := by
  have code := programLoaded_codeIn state.loaded
  obtain ⟨v,run1,ready1,e1⟩ :=
    (mov_r32_m32_legacy_effect_step 0x10482d 0 (.sib 4 none 0 (.d8 12))
      (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice code 0x482d _ (by decide) (by decide +kernel))
      ⟨rip,stack_readable pre state (offset := 12) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x4831 (by decide)))
  change (movR32M32LegacyEffect 0x10482d 0 (.sib 4 none 0 (.d8 12)) t).Holds t v at e1
  have m1 : v.external = t.external :=
    e1.agrees.external (by simp [movR32M32LegacyEffect_components, Component.Covers])
  have f1 := state.after_registers ready1 e1.agrees
    (by simp [movR32M32LegacyEffect_components, Component.Covers])
    (by simp [movR32M32LegacyEffect_components])
  have ax1 : (v.regValue .rax).setWidth 8 = digit := by
    have h := e1.writes
    change v.regValue .rax = ((Operand.mem (stackPtr t+12) : Operand 32).read t).setWidth 64 at h
    have a : stackPtr t+12 = stackPtr s-348 := stack_address state.rsp (by decide)
    rw [a,saved] at h
    rw [h]
    simpa using hdigit
  obtain ⟨w,run2,ready2,e2⟩ := (shr_al_seven_effect_step 0x104831).advances ready1
    (programText_slice (programLoaded_codeIn f1.loaded) 0x4831 _ (by decide) (by decide +kernel))
    e1.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x4834 (by decide)))
  have f2 := f1.after_registers ready2 e2.agrees
    (by simp [Component.Covers]) (by simp)
  have ax2 : (w.regValue .rax).setWidth 8 = if digit.msb then 1 else 0 := by
    have h := e2.writes
    change w.regValue .rax = mergeGPR 8 ((v.regValue .rax).setWidth 8 >>> 7) (v.regValue .rax) at h
    rw [h, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, ax1]
    exact sign_instruction digit
  obtain ⟨u,run3,ready3,e3⟩ := (movzx_r32_r8_effect_step 0x104834 0xf8 rfl (by decide)).advances ready2
    (programText_slice (programLoaded_codeIn f2.loaded) 0x4834 _ (by decide) (by decide +kernel))
    e2.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x4837 (by decide)))
  change (movzxR32R8Effect 0x104834 3 7 0 w).Holds w u at e3
  have f3 := f2.after_registers ready3 e3.agrees
    (by simp [movzxR32R8Effect,Effect.components,Component.Covers])
    (by simp [movzxR32R8Effect,Effect.components])
  refine ⟨u,(run1.trans run2).trans run3,f3,e3.rip,?_,?_⟩
  · have h := e3.writes
    change u.regValue .rdi = ((w.regValue .rax).setWidth 8).setWidth 64 at h
    rw [ax2] at h
    exact h.trans (by cases digit.msb <;> rfl)
  · apply ((e1.agrees.trans e2.agrees).trans e3.agrees).mono
    simp only [movR32M32LegacyEffect_components,shrAlSevenEffect_components,List.mem_append]
    simp only [movzxR32R8Effect,Effect.components,List.map_cons,List.map_nil,Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro c hc
    rcases hc with ((rfl | rfl) | rfl | rfl | rfl) | rfl | rfl <;> simp

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
