import Hkdf.Proofs.Key.Entry
import Hkdf.Proofs.Key.Short
import Hkdf.Proofs.Key.Hash
import Hkdf.Proofs.Key.Tail

set_option autoImplicit false

namespace Hkdf.Proofs.Key

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine

theorem normalize_correct [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (ctx : Context initial boundary key) :
    ∃ final, CalleeResult initial final boundary 64 720 ∧
      (registerRegion initial .rdi 64).HasBytes final.external
        (Hkdf.Proofs.Common.HMAC.keyBlock key) := by
  obtain ⟨s, prepared, branch⟩ := Entry.prepare ctx
  rcases branch with ⟨fits, rip⟩ | ⟨large, rip⟩
  · obtain ⟨t, ready⟩ := Short.run ctx prepared rip fits
    exact Tail.finish ctx ready
  · obtain ⟨t, ready⟩ := Hash.run ctx prepared rip large
    exact Tail.finish ctx ready

end Hkdf.Proofs.Key
