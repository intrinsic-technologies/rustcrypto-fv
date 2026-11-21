import P256.Proofs.Verifying.Core.Finish.Tail.Arguments

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem reduce_arguments [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e149) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (reduceArgumentEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := reduce_arguments_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe149 reduceArgumentBytes
      (by decide) (by decide +kernel)) rip
  exact ⟨fuel,u,run,state.after_registers ready effect.agrees
    (by simp [reduceArgumentEffect,Effect.components,Component.Covers])
    (by simp [reduceArgumentEffect,Effect.components]),effect⟩

theorem equal_arguments [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e15c) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (equalArgumentEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := equal_arguments_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe15c equalArgumentBytes
      (by decide) (by decide +kernel)) rip
  exact ⟨fuel,u,run,state.after_registers ready effect.agrees
    (by simp [equalArgumentEffect,Effect.components,Component.Covers])
    (by simp [equalArgumentEffect,Effect.components]),effect⟩

end P256.Proofs.Verifying.Core.Finish.Tail
