import P256.Proofs.Signing.Core.Iteration.Output.Retry
import P256.Proofs.Signing.Core.Iteration.Output.Copy
import P256.Proofs.Signing.Core.Iteration.Output.Success

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program SecretKeyFromBytes.Scalar

theorem correct : OutputContract := by
  intro inst s t boundary state secret nonce x y digest pre input rip execution
  rcases input.decision with ⟨model,tag,null⟩|⟨signature,model,tag,first,second⟩
  · obtain ⟨n,u,run,ip,loop⟩ := retry_correct pre input rip tag null
    exact ⟨n,u,run,.inl ⟨model,ip,loop⟩⟩
  · obtain ⟨nA,a,runA,fa,ipa,lo,next,agA⟩ := dispatch pre input.frame rip tag
    have ma := agA.external (by simp [Component.Covers])
    have ipa' : a.RIP = 0x10d377 := by simpa using ipa
    have firstA : Nat256At a (frameBase s+536) signature.1 := ⟨first.1,by simpa only [ma] using first.2⟩
    have secondA : Nat256At a (frameBase s+568) signature.2 := ⟨second.1,by simpa only [ma] using second.2⟩
    have outputA : (Operand.mem (frameBase s+72) : Operand 64).read a = s.regValue .rdi := by
      change memLoad a.external _ 64 = _
      rw [ma]
      exact input.arguments.output
    have low : a.regValue .r12 = BitVec.ofNat 64 signature.1 :=
      lo.trans (by simpa using first.memLoad_limb 0 (by decide))
    have secondWord : a.regValue .rbx = BitVec.ofNat 64 (signature.1/2^64) :=
      next.trans (by simpa [BitVec.add_assoc] using first.memLoad_limb 1 (by decide))
    obtain ⟨nB,b,runB,fb,pb,ipb,mb⟩ := copy_signature pre fa outputA ipa' firstA secondA low secondWord
    have keep (offset : Nat) (bound : offset+32 ≤ 2280) :
        ∀ i < 32,b.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
      intro i hi
      have h := (mb (offset+i) (by omega)).trans (congrArg (·[_]?) ma)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using h
    have hx : Field.MontgomeryAt b (frameBase s+104) x := input.point.1.of_bytes_eq (keep 104 (by decide))
    have hy : Field.MontgomeryAt b (frameBase s+136) y := input.point.2.1.of_bytes_eq (by
      intro i hi
      simpa only [BitVec.add_assoc,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using keep 136 (by decide) i hi)
    have reduced : Nat256At b (frameBase s+176) (x % P256.Spec.Operations.domain.n) :=
      ⟨input.reducedX.1,fun i hi => (keep 176 (by decide) i hi).trans (input.reducedX.2 i hi)⟩
    obtain ⟨n0,run0⟩ := execution
    obtain ⟨nC,u,runC,result,r,sigS⟩ := success pre fb pb ipb hx hy reduced ⟨_,(run0.trans runA).trans runB⟩
    exact ⟨nA+nB+nC,u,(runA.trans runB).trans runC,.inr ⟨signature,model,result,r,sigS⟩⟩

end P256.Proofs.Signing.Core.Iteration.Output
