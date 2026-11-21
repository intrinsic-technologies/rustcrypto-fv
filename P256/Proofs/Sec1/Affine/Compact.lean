import P256.Proofs.Sec1.Affine.Branches
import P256.Proofs.Sec1.Affine.Compact.Entry
import P256.Proofs.Sec1.Affine.Compact.Model
import P256.Proofs.Sec1.Affine.Compact.Select
import P256.Proofs.Sec1.Affine.Compact.Flags.Correct
import P256.Proofs.Sec1.Affine.Compact.Normalize
import P256.Proofs.Sec1.Affine.Compact.Finish
import P256.Proofs.Sec1.Decompress

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compact_correct : CompactCorrect := by
  intro bindings s t boundary bytes pre size tag state rip
  obtain ⟨n,a,runA,frameA,ripA,valueA,outputA,sourceA,zeroA⟩ :=
    Compact.enter pre state size
      (fun _ hp => by simpa only [Spec.Points.element] using Decompress.decompress_correct hp) rip
  obtain ⟨m,b,runB,stateB⟩ := Compact.select_decompressed pre frameA ripA valueA outputA sourceA zeroA
  obtain ⟨k,c,runC,stateC⟩ := Compact.Flags.prepare_flags pre stateB
  obtain ⟨j,d,runD,stateD⟩ := Compact.normalize pre stateC
  obtain ⟨l,u,runU,frameU,ripU,valueU⟩ := Compact.Finish.finish pre stateD
  refine ⟨n+m+k+j+l,u,(((runA.trans runB).trans runC).trans runD).trans runU,frameU,ripU,?_⟩
  rw [Compact.decodePoint_eq_decompact size tag]
  exact valueU

end P256.Proofs.Sec1.Affine
