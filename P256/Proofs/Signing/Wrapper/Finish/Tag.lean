import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Signing.Wrapper.Finish.State
import P256.Proofs.Common.Instructions.CompareMemory
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem tag_branch [Bindings] {initial t : RamState}
    (state : State initial t) (stack : Stack.Valid initial 5112)
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : t.RIP = 0x102a3e) :
    ∃ u, Advances (returnBoundary initial) 1 t u ∧ State initial u ∧
      u.RIP = 0x102a46 ∧ u.external = t.external ∧ u.regValue .rdx = initial.regValue .r8 := by
  have readable : MemReadable t (stackPtr initial - 200) 8 :=
    readable_of_grow (stack_sub_readable stack (offset := 200) (len := 8)
      (by decide) (by decide)) state.allocated
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_r64_m64_effect_step 0x102a3e 0x48 (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d32 320)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x2a3e _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change MemReadable t (stackPtr t + 320#64) 8
        rw [stack_address state.rsp (by decide)]
        exact readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x2a46 (by decide)))
  have ag : AgreesExcept [.reg 2, .rip] t u := effect.agrees
  refine ⟨u,run,state.after_registers ready ag (by simp [Component.Covers])
    (by simp) (by simp),effect.rip,ag.external (by simp [Component.Covers]),?_⟩
  have h : u.regValue .rdx = memLoad t.external (stackPtr t+320#64) 64 := effect.writes
  rw [h,stack_address state.rsp (off := 320) (by decide)]
  exact state.capacity

end P256.Proofs.Signing.Wrapper.Finish
