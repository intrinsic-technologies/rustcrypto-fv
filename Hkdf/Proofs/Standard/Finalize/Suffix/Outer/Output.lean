import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Normalize

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key message : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e020)
    (outer : HashStateAt s (stackPtr initial - 232)
      (Hkdf.Proofs.NIST.SHA256.compress (Suffix.outerHash key)
        (Hkdf.Proofs.NIST.Encoding.octetsToBits (tailFirst
          (HMAC.xorPad (HMAC.keyBlock key) 0x5c ++ Standards.NIST.SHA2.SHA256.hashBytes
            (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message)))))) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e0c0 ∧
      (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes t.external
        (Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message) ∧
      (MemoryRegion.mk (stackPtr initial - 336).toNat 64).HasBytes t.external
        (HMAC.keyBlock (Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message)) := by
  obtain ⟨u, currentU, ipU, digest⟩ := Serialize.run_of_state pre state rip outer
  rw [Suffix.outerHash, Common.serializeHash_hmac_sha256_outer] at digest
  exact Normalize.run pre currentU ipU digest

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output
