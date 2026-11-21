import P256.Proofs.Nonce.Fill.Tail.Decode.Read.Setup
import P256.Proofs.Nonce.Fill.Tail.Decode.Read.Call
import P256.Proofs.Nonce.Fill.Tail.Decode.CallFrame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem read [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : ScanReady initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadDone initial t orderAddress state := by
  obtain ⟨prepared, setupRun, stage⟩ := Read.prepare pre input
  obtain ⟨called, callRun, effect, cp, bytes⟩ := Read.call pre stage
  obtain ⟨t, result⟩ := ReadBe.read_be_correct cp bytes
  have cr : CalleeResult called t boundary 32 128 .rdx :=
    ⟨result.execution, result.rip, result.rsp, result.bindingsSupported, result.machine,
      result.calleeSaved, result.directionFlag, result.mxcsr, result.fp87,
      result.frame, result.loaded, result.allocated⟩
  have output : called.regValue .rdx = frameBase initial + 104 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans stage.destination
  have context := context_after_call pre stage.toContext effect (offset := 104)
    (by decide) (by decide +kernel) output cr
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨8 + 1 + fuel, t, (setupRun.trans callRun).trans run,
    context, result.rip.trans (callEffect_stack effect).1, ?_, ?_, result.status, ?_⟩
  · exact ((result.calleeSaved .r12 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 12) (by simp))).trans stage.r12
  · exact ((result.calleeSaved .r14 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 14) (by simp))).trans stage.r14
  · have size : (updateValue state).value.size = 32 := HMAC.hmac_size state.key state.value
    have value : Arith.uint (updateValue state).value = (Signing.Search.nextCandidate state).1 := by
      simp only [nextCandidate_eq, Arith.uint, Arith.decodeBigEndian]
    apply nat256At_of_memLoad_limbs
    · rw [← value]
      simpa only [Arith.uint, Arith.decodeBigEndian, size,
        show (256 : Nat)^32 = 2^256 by decide +kernel] using
        SecretKeyFromBytes.Encoding.octetsToNat_lt (updateValue state).value
    · intro i hi
      have address : frameBase initial + 104 = stackPtr initial - 128 :=
        frameBase_add initial (offset := 104) (by decide)
      rw [address]
      exact context.allocated _ ((stack_sub_readable pre.stack (offset := 128) (len := 32)
        (by decide) (by decide)).mem i hi)
    · simpa only [output, value] using result.value

end P256.Proofs.Nonce.Fill.Tail.Decode
