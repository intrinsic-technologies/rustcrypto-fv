import P256.Proofs.Scalar.Multiply.ReductionPre
import P256.Proofs.Scalar.Multiply.Call
import P256.Proofs.Field.Montgomery.Wrapper.Reduction

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program P256.Proofs.Program
open P256.Proofs.Field.Montgomery.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64}

theorem reduction_work_frame (pre : CalleePre s boundary entryPC 32 32 280)
    (rsp : stackPtr t = stackPtr s - 144)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (result : CalleeResult t u boundary 32 112) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 32, workRegion s] := by
  have hb := stack_bounds pre.stack
  have hspn : (stackPtr t).toNat = (stackPtr s).toNat - 144 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  intro a hout
  apply result.frame a
  intro r hr hin
  have hr' : r = registerRegion t .rdi 32 ∨ r = Stack.region t 112 := by simpa using hr
  rcases hr' with rfl | rfl
  · apply hout (registerRegion s .rdi 32) (by simp)
    simpa only [registerRegion, destination] using hin
  · apply hout (workRegion s) (by simp)
    change (stackPtr s).toNat - 280 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 280 + 272
    change (stackPtr t).toNat - 112 ≤ a.toNat ∧
      a.toNat < (Stack.region t 112).start + (Stack.region t 112).size at hin
    rw [stack_region_end] at hin
    change (stackPtr t).toNat - 112 ≤ a.toNat ∧ a.toNat < (stackPtr t).toNat + 8 at hin
    rw [hspn] at hin
    constructor <;> omega

end P256.Proofs.Scalar.Multiply
