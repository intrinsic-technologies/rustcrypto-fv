import P256.Proofs.Sec1.Affine.Uncompressed.Output.Constants
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Coordinates
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Copy
import P256.Proofs.Sec1.Affine.Uncompressed.Output.CopyX
import P256.Proofs.Sec1.Affine.Uncompressed.Output.CopyY
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Finish
import P256.Proofs.Sec1.Affine.Uncompressed.Output.FlagStore
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Flags
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Mask
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Memory
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Not
import P256.Proofs.Sec1.Affine.Uncompressed.Output.OutputMemory
import P256.Proofs.Sec1.Affine.Uncompressed.Output.OutputX
import P256.Proofs.Sec1.Affine.Uncompressed.Output.OutputY
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Prefix
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Prepare
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Result
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Select
import P256.Proofs.Sec1.Affine.Uncompressed.Output.SelectSetup
import P256.Proofs.Sec1.Affine.Uncompressed.Output.State
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Transfer

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Validated s t bytes)
    (size : bytes.size = 65) (tag : bytes.data[0]? = some 4) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (Spec.Points.decodePoint bytes) := by
  obtain ⟨n,a,runA,sa⟩ := copy_coordinates pre state
  obtain ⟨m,b,runB,sb⟩ := prepare pre sa
  obtain ⟨k,c,runC,sc⟩ := select_x pre sb
  obtain ⟨l,d,runD,sd⟩ := select_y pre sc
  obtain ⟨e,runE,se⟩ := mask pre sd
  obtain ⟨p,f,runF,sf⟩ := transfer_coordinates pre se
  obtain ⟨q,u,runG,frame,rip,value⟩ := finish pre sf size tag
  exact ⟨n+m+k+l+1+p+q,u,(((((runA.trans runB).trans runC).trans runD).trans runE).trans runF).trans runG,
    frame,rip,value⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Output
