import Hkdf.Proofs.Key.Hash.Serialize.Payload
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.SHA256

theorem payload_hashBytes {s t : RamState} {message : ByteArray}
    (pre : Pre s)
    (hashWords : HashStateAt s (rspOf s + 128)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (bytePadding message)))
    (h : (effect s).Holds s t) :
    (⟨(rspOf s).toNat, 32⟩ : MemoryRegion).HasBytes t.external
      (Standards.NIST.SHA2.SHA256.hashBytes message) := by
  rw [← Hkdf.Proofs.Common.serializeHash_compressBlocks_bytePadding_eq_hashBytes]
  exact payload pre hashWords h

end Hkdf.Proofs.Key.Hash.Serialize
