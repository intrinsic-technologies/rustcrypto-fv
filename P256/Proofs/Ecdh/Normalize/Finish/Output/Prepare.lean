import P256.Proofs.Ecdh.Normalize.Finish.State
import P256.Proofs.Ecdh.Normalize.Finish.Output.Copy
import P256.Proofs.Ecdh.Normalize.Finish.Output.Setup
import P256.Proofs.Ecdh.Normalize.Coordinates.Copy

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish.Output

open P256.Spec.Program P256.Spec.Program.Routines Program Program.ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Prepared [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (x : Nat) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10052a
  output : t.regValue .rbx = s.regValue .rdi
  x : MontgomeryAt t (stackPtr s - 1808) x
  rsi : t.regValue .rsi = stackPtr s - 1808
  rdi : t.regValue .rdi = stackPtr s - 1040

theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x100000 32 32 3464) (state : Selected s t boundary x) :
    ∃ u, Prepared s u boundary x := by
  have src : Copy.source t = stackPtr s - 1976 :=
    scalar_stack_address state.rsp (by decide) (by decide)
  have dst : Copy.destination t = stackPtr s - 1808 :=
    scalar_stack_address state.rsp (by decide) (by decide)
  have cp : Copy32.Pre 0x1004e6 Copy.source Copy.destination t := by
    apply Coordinates.stack_pre pre state.toFrameState (offset := 248) (by decide) rfl state.rip
    · exact stack_readable (frameOffset := 2056) pre state.toFrameState (by decide) (by decide)
    · exact RangeApart.offsets (stackPtr t) (a := 248) (b := 80)
        (by decide) (by decide) (.inr (by decide))
  obtain ⟨n,v,run,frame,ip,value,agrees⟩ := Coordinates.execute_stack pre state.toFrameState
    (Copy.copy boundary pre.outerBoundary) (entryOffset := 0x4e6)
    (by decide) (by decide +kernel) (offset := 248) (by decide) rfl cp (by rw [src]; exact state.x)
  rw [dst] at value agrees
  obtain ⟨m,u,run',frame',effect,memory⟩ := setup frame pre.outerBoundary ip
  obtain ⟨k,before⟩ := state.execution
  have regs := effect.writes
  change u.regValue .rdi = stackPtr v + 1016 ∧ u.regValue .rsi = stackPtr v + 248 at regs
  refine ⟨u,frame',⟨k+n+m,(before.trans run).trans run'⟩,effect.rip,?_,
    value.of_bytes_eq (by intro i hi; rw [memory]),?_,?_⟩
  · exact ((effect.agrees.read (n := 64) (r := 3) (by simp [setupEffect,Effect.components])).trans
      (agrees.read (n := 64) (r := 3) (by simp [Copy32.components]))).trans state.output
  · exact regs.2.trans (scalar_stack_address frame.rsp (by decide) (by decide))
  · exact regs.1.trans (scalar_stack_address frame.rsp (by decide) (by decide))

end P256.Proofs.Ecdh.Normalize.Finish.Output
