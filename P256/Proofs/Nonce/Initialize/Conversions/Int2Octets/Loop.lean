import P256.Proofs.Program.Interface
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop.Iteration

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar

theorem loop_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {value : Nat} (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (integer : Nat256At initial (initial.regValue .rdi) value)
    (registers : LoopRegisters initial s 0) (rip : s.RIP = 0x107050) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x107093 ∧
      (registerRegion initial .rdx 32).HasBytes t.external
        (Standards.RFC.DeterministicSigning.Nonce.intToOctets P256.Spec.Operations.domain.n value) := by
  obtain ⟨s1,stage1,registers1,words1,rip1⟩ := Loop.iteration pre stage integer registers
    (by intro j hj; omega) (by decide) rip
  obtain ⟨s2,stage2,registers2,words2,rip2⟩ := Loop.iteration pre stage1 integer registers1
    words1 (by decide) rip1
  obtain ⟨s3,stage3,registers3,words3,rip3⟩ := Loop.iteration pre stage2 integer registers2
    words2 (by decide) rip2
  obtain ⟨s4,stage4,_,words4,rip4⟩ := Loop.iteration pre stage3 integer registers3
    words3 (by decide) rip3
  exact ⟨s4,stage4,rip4,Loop.words_output pre stage4 words4⟩

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
