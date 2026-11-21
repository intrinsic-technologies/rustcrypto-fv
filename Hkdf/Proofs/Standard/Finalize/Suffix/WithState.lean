import Hkdf.Proofs.Standard.Finalize.Suffix.Outer
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey
import Hkdf.Proofs.Standard.Finalize.Suffix.Return

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine

theorem finalize_correct_with_state [Bindings]
    {initial : RamState} {boundary : ReturnBoundary} {key message : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (hmac : HmacAt initial (initial.regValue .rsi) key message)
    (size : 64 + message.size < 2^61) :
    ∃ t, CalleeResult initial t boundary 176 1264 ∧
      (registerRegion initial .rdi 32).HasBytes t.external
        (Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message) ∧
      HmacAt t (initial.regValue .rdi + 32)
        (Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message)
        ByteArray.empty := by
  obtain ⟨s, stateS, ripS, inner, outer, count⟩ := from_hmac pre hmac size
  obtain ⟨a, stateA, ripA, bytesA, keyA⟩ := Outer.run pre stateS ripS inner outer count
  obtain ⟨b, stateB, ripB, bytesB, packed⟩ := Rekey.run pre stateA ripA bytesA keyA
  exact Return.run pre stateB ripB bytesB packed

end Hkdf.Proofs.Standard.Finalize.Suffix
