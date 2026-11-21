import P256.Proofs.Nonce.Initialize.Finish.Result
import P256.Proofs.Nonce.Initialize.Finish.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {state : Nonce.State}
    (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary)
    (rip : s.RIP = 0x107c1a)
    (order : s.regValue .r15 = orderAddress)
    (output : s.regValue .r14 = initial.regValue .rdi)
    (drbg : DrbgAt s (stackPtr s + 8) state) :
    ∃ t, CalleeResult initial t boundary 72 2144 ∧
      GeneratorAt t (initial.regValue .rdi) orderAddress state := by
  have output' : Finish.outputPointer s = initial.regValue .rdi := output
  obtain ⟨fuel, u, run, ready, _, effect⟩ :=
    Finish.copy_run boundary pre.outerBoundary s (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7c1a Finish.copyBytes
        (by decide +kernel) (by decide +kernel))
      (Finish.copy_pre pre stage rip output')
  obtain ⟨stage', generator⟩ := Finish.copy_result pre stage ready run effect order output' drbg
  obtain ⟨t, result, memory⟩ := finish_epilogue pre stage' effect.rip
  refine ⟨t, result, ?_⟩
  simpa only [GeneratorAt, DrbgAt, Nat256At, memory] using generator

end P256.Proofs.Nonce.Initialize
