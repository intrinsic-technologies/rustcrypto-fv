import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Encode.Copy
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Result
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem encode_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat} (pre : ScalarPre s boundary cursor point)
    (state : Memory s t cursor point) (rip : t.RIP = 0x10b18d)
    (rcx : t.regValue .rcx = point) (input : Nat256At s (point + 96) n) :
    ∃ fuel u, Advances boundary fuel t u ∧ Memory s u cursor point ∧
      u.RIP = 0x10b1cf ∧ u.regValue .rbx = t.regValue .rbx ∧
      Bytes u.external (stackPtr s - 352) 32
        (fun i => UInt8.ofNat (n / 256^(31-i) % 256)) := by
  obtain ⟨fuel, copied, run, stored, atcall, dst, src, rbx, scalar⟩ :=
    copy_scalar pre state rip rcx input
  have out : copied.regValue .rdi = stackPtr s - 352 :=
    dst.trans (stack_address state.rsp (by decide))
  have source : copied.regValue .rsi = stackPtr s - 80 :=
    src.trans (stack_address state.rsp (by decide))
  have scalar' : Nat256At copied (stackPtr s - 80) n := by
    have h : stackPtr t + 280 = stackPtr s - 80 := stack_address state.rsp (offset := 280) (by decide)
    rw [h] at scalar
    exact scalar
  obtain ⟨called, callrun, ready, effect⟩ := direct_call pre stored.toFrameState 0xb1ca 0x7cd1
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x12ea0 (by decide)) atcall
  change (callEffect (fun _ => 0x112ea0) 0x10b1cf copied).Holds copied called at effect
  have frame := stored.toFrameState.after_call pre ready effect
  have inputReg : called.regValue .rsi = stackPtr s - 80 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have outputReg : called.regValue .rdi = stackPtr s - 352 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans out
  have returnEq : (returnBoundary called).rip = 0x10b1cf := by
    exact (callEffect_stack effect).1
  have callpre : CalleePre called boundary 0x112ea0 32 32 0 :=
    pre.toCalleePre.of_stack
      ⟨368, 80, 352, by decide, by decide, by decide, by decide,
        by decide, by decide, Or.inr (by decide)⟩
      frame.bindingsSupported frame.machine frame.directionFlag frame.loaded frame.allocated effect.rip frame.rsp
      inputReg outputReg (returnEq ▸ inProgram_of_textOffset 0xb1cf (by decide))
  have callinput : Nat256At called (called.regValue .rsi) n := by
    rw [inputReg]
    refine ⟨scalar'.1, ?_⟩
    intro i hi
    exact (call_byte stored.toFrameState effect (offset := 80) (len := 32) (by decide) (by decide) hi).trans (scalar'.2 i hi)
  have cursorEq : memLoad called.external cursor 64 = point + 128 := by
    apply Eq.trans (cursor_read_of_frame pre ?_) stored.cursorValue
    intro a ha
    apply effect.agrees.memoryWriteFrame (call_writes pre stored.toFrameState) a
    intro region hr hin
    have hr' : region = Stack.region s 536 := by simpa using hr
    exact ha _ (by simp [hr']) hin
  obtain ⟨u, result, bytes, _, _⟩ := P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.scalar_encode_correct callpre callinput
  have work := stack_result_work_frame pre frame result outputReg (by decide) (by decide) (by decide)
  have finalstate : Memory s u cursor point :=
    ⟨frame.after_result pre result work, (work_cursor_read pre work).trans cursorEq⟩
  obtain ⟨amount, encoded⟩ := result.execution
  refine ⟨fuel + 1 + amount, u, (run.trans callrun).trans encoded,
    finalstate, result.rip.trans returnEq, ?_, ?_⟩
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans rbx)
  · rw [outputReg] at bytes
    exact bytes

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
