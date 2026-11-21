import P256.Proofs.Field.Inverse.Tail.Choice
import P256.Proofs.Common.Instructions.LegacyLoad
import P256.Proofs.Field.Inverse.Tail.Support

set_option autoImplicit false

open P256.Proofs.Common.Instructions.LegacyLoad (movR32M32LegacyEffect_components mov_r32_m32_legacy_effect_step)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem choice_prepare_flag [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11414b) (flag : t.external[stackPtr s - 136]? = some (if select then 1 else 0)) :
    ∃ u, Advances boundary 1 t u ∧ FrameState s u ∧ u.RIP = 0x11414f ∧
      (u.regValue .rdi).setWidth 8 = (if select then 1 else 0) ∧ u.external = t.external := by
  have addr : (AddrMode.sib 4 none 0 (.d8 32)).addr t 0x11414f = stackPtr s - 136 := by
    change stackPtr t + 32 = _
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read : MemReadable t ((AddrMode.sib 4 none 0 (.d8 32)).addr t 0x11414f) 4 := by
    rw [addr]
    exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack
      (offset := 136) (len := 4) (by decide) (by decide)) state.allocated
  obtain ⟨u,run,ready,effect⟩ :=
    (mov_r32_m32_legacy_effect_step 0x11414b 7 (.sib 4 none 0 (.d8 32))
      (by decide) rfl rfl).advances (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x1414b [0x8b,0x7c,0x24,0x20]
        (by decide) (by decide +kernel)) ⟨rip,read⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1414f (by decide)))
  have mem := effect.agrees.external (by simp [movR32M32LegacyEffect_components, Component.Covers])
  have state1 := state.of_registers pre ready effect.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [movR32M32LegacyEffect_components, gprNumber])
    (by simp [movR32M32LegacyEffect_components, Component.Covers])
  refine ⟨u,run,state1,effect.rip,?_,mem⟩
  have h : u.regValue .rdi =
      (memLoad t.external ((AddrMode.sib 4 none 0 (.d8 32)).addr t 0x11414f) 32).setWidth 64 :=
    effect.writes
  rw [h,addr,BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),memLoad32_lowByte]
  change ((t.external[stackPtr s - 136]?).getD 0).toBitVec = (if select then 1 else 0)
  rw [flag]
  cases select <;> rfl

end P256.Proofs.Field.Inverse
