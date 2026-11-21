import P256.Proofs.Scalar.Multiply.ReductionFrame
import P256.Proofs.Scalar.Multiply.Correct

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program P256.Proofs.Program
open P256.Proofs.Field.Montgomery.Wrapper
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64}

theorem reduction_stage {value : Nat} (pre : CalleePre s boundary entryPC 32 32 280)
    (state : FrameState s t) (rip : t.RIP = 0x1130bd)
    (left : t.regValue .rsi = scratch s) (right : t.regValue .rdx = scratch s + 32)
    (destination : t.regValue .rdi = s.regValue .rdi)
    (bytes : Bytes t.external (scratch s) 64 (fun i => UInt8.ofNat (value / 256^i % 256)))
    (bound : value < 2^256 * 2^256) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x1130c2 ∧
      Nat256At u (s.regValue .rdi)
        (value % P256.Spec.Operations.domain.n) := by
  obtain ⟨entered, callRun, ready, effect⟩ := call_reduction pre state rip
  have saved := call_state pre state ready effect
  have hsp : stackPtr entered = stackPtr s - 144 := effect.writes.1.trans (call_address state)
  have hleft : entered.regValue .rsi = scratch s :=
    (effect.agrees.read (r := 6) (n := 64) (by simp)).trans left
  have hright : entered.regValue .rdx = scratch s + 32 :=
    (effect.agrees.read (r := 2) (n := 64) (by simp)).trans right
  have hdst : entered.regValue .rdi = s.regValue .rdi :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans destination
  have hright' : entered.regValue .rdx = stackPtr s - 104 := by
    rw [hright]
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have calleePre := reduction_pre pre saved hsp hleft hright' hdst
    ⟨effect.rip, by change InProgram (stackTop entered); rw [(callEffect_stack effect).1]; exact inProgram_of_textOffset 0x130c2 (by decide)⟩
  have hbytes : Bytes entered.external (scratch s) 64
      (fun i => UInt8.ofNat (value / 256^i % 256)) :=
    fun i hi => (call_scratch_bytes state effect i hi).trans (bytes i hi)
  have hlow : Nat256At entered (entered.regValue .rsi) (value % 2^256) := by
    rw [hleft]
    exact low_nat256 hbytes
  have hhigh : Nat256At entered (entered.regValue .rdx) (value / 2^256) := by
    rw [hright]
    exact high_nat256 hbytes bound
  obtain ⟨final, result, output⟩ := barrett_correct calleePre hlow hhigh
  have saved' := saved.after_result pre result (reduction_work_frame pre hsp hdst result)
  have finalSp : stackPtr final = scratch s := by
    change final.regValue .rsp = scratch s
    rw [result.rsp]
    exact (callEffect_stack effect).2.trans state.rsp
  have finalBx : final.regValue .rbx = s.regValue .rdi :=
    (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (r := 3) (n := 64) (by simp)).trans state.rbx)
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨1+fuel, final, callRun.trans run, ⟨saved', finalSp, finalBx⟩,
    result.rip.trans (callEffect_stack effect).1, ?_⟩
  simpa only [hdst, Nat.mod_add_div] using output

end P256.Proofs.Scalar.Multiply
