import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Callee

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem call_result_byte {entry ret : BitVec 64} {output outputBytes reserve offset len i : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (effect : (callEffect (fun _ => entry) ret t).Holds t u)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 output)
    (result : CalleeResult u v boundary outputBytes reserve)
    (outputBound : output + outputBytes ≤ 192) (bound : offset + len ≤ 216)
    (apart : offset + len ≤ output ∨ output + outputBytes ≤ offset) (index : i < len) :
    v.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := Program.stack_bounds pre.stack
  have tn : (stackPtr t).toNat = (stackPtr s).toNat - 216 := by
    rw [state.rsp]
    exact Program.stack_sub_toNat pre.stack (by decide)
  have un : (stackPtr u).toNat = (stackPtr s).toNat - 224 := by
    have hu : stackPtr u = stackPtr s - 224 := effect.writes.1.trans (constructor_call_address state)
    rw [hu]
    exact Program.stack_sub_toNat pre.stack (by decide)
  have dst : u.regValue .rdi = stackPtr t + BitVec.ofNat 64 output :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have dn : (u.regValue .rdi).toNat = (stackPtr s).toNat - 216 + output := by
    rw [dst, toNat_add_ofNat _ _ (by rw [tn]; omega), tn]
  rw [result.frame _]
  · rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)]
    exact Program.ScalarFrame.call_byte (frameOffset := 216) (by decide) state.rsp effect (offset := 216-offset) (len := len)
      (by omega) (by omega) index
  · intro region hr hin
    have an : (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat - 216 + offset + i := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by rw [tn]; omega), tn]
      omega
    have cases : region = registerRegion u .rdi outputBytes ∨ region = Stack.region u reserve := by
      simpa using hr
    rcases cases with rfl | rfl
    · change (u.regValue .rdi).toNat ≤ _ ∧ _ < (u.regValue .rdi).toNat + outputBytes at hin
      rw [dn, an] at hin
      omega
    · change (stackPtr u).toNat - reserve ≤ _ ∧ _ <
        (Stack.region u reserve).start + (Stack.region u reserve).size at hin
      rw [stack_region_end, un, an] at hin
      omega

theorem call_result_scalar {entry ret : BitVec 64} {output outputBytes reserve offset d : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (effect : (callEffect (fun _ => entry) ret t).Holds t u)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 output)
    (result : CalleeResult u v boundary outputBytes reserve)
    (outputBound : output + outputBytes ≤ 192) (bound : offset + 32 ≤ 216)
    (apart : offset + 32 ≤ output ∨ output + outputBytes ≤ offset)
    (value : Nat256At t (stackPtr t + BitVec.ofNat 64 offset) d) :
    Nat256At v (stackPtr v + BitVec.ofNat 64 offset) d := by
  have sp : stackPtr v = stackPtr t := result.rsp.trans (callEffect_stack effect).2
  rw [sp]
  refine ⟨value.1, fun i hi => ?_⟩
  rw [call_result_byte pre state effect destination result outputBound bound apart hi]
  exact value.2 i hi

theorem scalar_call {target : RamState → BitVec 64} {ret : BitVec 64} {off d : Nat}
    (state : Frame s t) (effect : (callEffect target ret t).Holds t u)
    (bound : off + 32 ≤ 216)
    (value : Nat256At t (stackPtr t + BitVec.ofNat 64 off) d) :
    Nat256At u (stackPtr t + BitVec.ofNat 64 off) d := by
  rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)] at value ⊢
  refine ⟨value.1, fun i hi => ?_⟩
  rw [Program.ScalarFrame.call_byte (frameOffset := 216) (by decide) state.rsp effect (offset := 216-off) (len := 32)
    (by omega) (by omega) hi]
  exact value.2 i hi

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
