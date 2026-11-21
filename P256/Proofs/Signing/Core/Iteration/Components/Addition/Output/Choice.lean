import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Choice.Prefix
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Choice.Tail

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Field (BinaryFieldPre)
open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem choice_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a b : Nat}
    (pre : BinaryFieldPre s boundary 0x113310 64) (state : DifferenceState s t a b) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x113a75 ∧
      u.regValue .rax = s.regValue .rdi ∧
      (u.regValue .rcx).setWidth 8 = choiceByte t ∧
      sumLimbs u = sumLimbs t ∧ differenceLimbs u = differenceLimbs t := by
  obtain ⟨n,v,run,ready,_,effect⟩ := Choice.prefix_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x13a42 Choice.prefixBytes
      (by decide +kernel) (by decide +kernel)) state.rip
  have agrees : AgreesExcept (Choice.frame t) t v :=
    effect.agrees.mono (by simp [Choice.prefixEffect,Effect.components,Choice.frame])
  have framed := FrameState.after_effect pre.toCalleePre state.toFrameState ready agrees
    (Choice.writes pre.toCalleePre state.toFrameState) (by simp [Choice.frame])
  obtain ⟨u,tail,final,last,preserved⟩ := Choice.tail pre.toCalleePre framed effect.rip
  have ptr : v.regValue .rax = t.regValue .rdi := effect.writes.1
  have byte : (v.regValue .rcx).setWidth 8 = choiceByte t := by
    have value : v.regValue .rcx = mergeGPR 8 (choiceByte t) (t.regValue .rcx) := effect.writes.2
    rw [value,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
  refine ⟨n+11,u,run.trans tail,final,last,?_,?_,?_,?_⟩
  · exact (preserved 0 (by decide)).trans (ptr.trans state.output)
  · have reg : u.regValue .rcx = v.regValue .rcx := preserved 1 (by decide)
    rw [reg,byte]
  · rw [← Choice.sum_eq agrees]
    unfold sumLimbs
    congr 1
    · exact preserved 11 (by decide)
    · exact preserved 10 (by decide)
    · exact preserved 9 (by decide)
    · exact preserved 8 (by decide)
  · rw [← Choice.difference_eq agrees]
    unfold differenceLimbs
    congr 1
    · exact preserved 2 (by decide)
    · exact preserved 6 (by decide)
    · exact preserved 14 (by decide)
    · exact preserved 15 (by decide)

end P256.Proofs.Signing.Core.Iteration.Components.Addition
