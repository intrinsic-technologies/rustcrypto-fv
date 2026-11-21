import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Compression
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key message : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s)
    (rip : s.RIP = 0x10df0d)
    (inner : HashStateAt s (stackPtr initial - 272) (Suffix.innerHash key message))
    (outer : HashStateAt s (stackPtr initial - 232) (Suffix.outerHash key))
    (count : loadBytes s.external (stackPtr initial - 200) 8 = .ok 1) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e0c0 ∧
      (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes t.external
        (Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message) ∧
      (MemoryRegion.mk (stackPtr initial - 336).toNat 64).HasBytes t.external
        (HMAC.keyBlock (Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message)) := by
  obtain ⟨a, stateA, ripA, destination, source, countA, hashA, bytesA⟩ :=
    Prepare.run pre state rip inner outer count
  obtain ⟨b, stateB, ripB, hashB⟩ :=
    Compression.run pre stateA ripA destination source countA bytesA hashA
  exact Output.run pre stateB ripB hashB

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer
