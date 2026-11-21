import P256.Proofs.Ecdh.Normalize.Finish.Output.Call
import P256.Proofs.Ecdh.Normalize.Finish.Output.Serialize
import P256.Proofs.Ecdh.Normalize.Return

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec.Program P256.Spec.Program.Routines Program Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x100000 32 32 3464) (state : Selected s t boundary x) :
    ∃ u, CalleeResult s u boundary 32 3464 ∧
      (registerRegion s .rdi 32).HasBytes u.external (Standards.SECG.ECC.Encoding.natToOctets 32 x) := by
  obtain ⟨v,prepared⟩ := Output.prepare pre state
  obtain ⟨w,frame,execution,rip,out,value⟩ := Output.conversion pre prepared
  obtain ⟨n,z,run,frame',rip',bytes⟩ := Output.serialize pre frame rip out value
  obtain ⟨u,result,memory⟩ := Return.return_correct pre frame' rip' (by
    obtain ⟨m,before⟩ := execution
    exact ⟨m+n,before.trans run⟩)
  exact ⟨u,result,memory.symm ▸ bytes⟩

end P256.Proofs.Ecdh.Normalize.Finish
