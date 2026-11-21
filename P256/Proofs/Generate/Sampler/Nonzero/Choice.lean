import P256.Proofs.Generate.Sampler.Memory
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Generate.Zero.Mask
import P256.Proofs.Common.Instructions.ByteLogic.Unary

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame
open P256.Proofs.Common.Instructions.ByteLogic

theorem invert [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray} {x : Nat}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100c7c)
    (value : (t.regValue .rax).setWidth 8 = (if x=0 then 1 else 0)) :
    ∃ u, Advances boundary 3 t u ∧ State s u ∧ u.RIP = 0x100c83 ∧
      u.regValue .rdi = (if x=0 then 0 else 1) ∧
      AgreesExcept [.reg 0,.reg 7,.flags,.rip] t u := by
  obtain ⟨a,ha,ra,ea⟩ := (not_al_effect_step 0x100c7c).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xc7c _ (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc7e (by decide)))
  have sa := state.after_registers pre ra ea.agrees
    (by simp [Effect.components,notAlEffect,Component.Covers])
    (by simp [Effect.components,notAlEffect])
  obtain ⟨u,hu,ru,gu,ipu,vu⟩ := Generate.Zero.mask_arguments boundary 0x100c7e ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0xc7e _ (by decide) (by decide +kernel))
    ea.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc80 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc83 (by decide)))
  refine ⟨u,ha.trans hu,sa.after_registers pre ru gu (by simp [Component.Covers]) (by simp),ipu,?_,
    (ea.agrees.trans gu).mono (by simp [Effect.components,notAlEffect])⟩
  have ax : a.regValue .rax = mergeGPR 8 (~~~((t.regValue .rax).setWidth 8)) (t.regValue .rax) := ea.writes
  rw [vu,ax,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
  change ((~~~((t.regValue .rax).setWidth 8) &&& 1).setWidth 64) = _
  rw [value]
  split <;> rfl

theorem choice [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100c83) :
    ∃ u, Advances boundary 6 t u ∧ State s u ∧ u.RIP = 0x100c88 ∧
      u.regValue .rax = ((t.regValue .rdi).setWidth 8).setWidth 64 ∧
      AgreesExcept (choiceClobbers s 264) t u := by
  obtain ⟨u,run,ready,sp,ip,value,g⟩ := choice_step pre.toCalleePre (frameOffset := 264)
    (by decide) (by decide) (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated state.rsp 0xc83 0x183e8 (by decide)
    (by decide +kernel) (by decide) rip
  have su := state.after pre ready g (by
    intro c hc a ha
    simp only [choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    all_goals exact ⟨workRegion s 3624,by simp [bodyWrites],
      work_contains pre.toCalleePre (by decide) (by decide) ha⟩) sp
  exact ⟨u,run,su,ip,value,g⟩

end P256.Proofs.Generate.Sampler.Nonzero
