import P256.Proofs.Verifying.Message.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem work_frame_stack [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (frame : MemoryWriteFrame s t #v[ScalarFrame.workRegion initial 9992]) :
    MemoryWriteFrame s t #v[Stack.region initial 9992] := by
  have bounds := stack_bounds pre.stack
  intro a outside
  apply frame a
  intro region member inside
  have eq : region = ScalarFrame.workRegion initial 9992 := by simpa using member
  subst region
  apply outside (Stack.region initial 9992) (by simp)
  change (stackPtr initial).toNat - 9992 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 9992 + (9992 - 48) at inside
  change (stackPtr initial).toNat - 9992 ≤ a.toNat ∧
    a.toNat < (Stack.region initial 9992).start + (Stack.region initial 9992).size
  rw [stack_region_end]
  omega

end P256.Proofs.Verifying.Message
