import Sha2.Spec.Program
import Sha2.Proofs.FIPS180

set_option autoImplicit false

namespace Sha2.Proofs.Common.Memory

open Sha2.Spec Sha2.Spec.Program Standards.NIST Prelude X86 X86.Machine

theorem readBytes_of_hasBytes {final : RamState} {region : MemoryRegion}
    (digest : Vector UInt8 region.size)
    (bytes : region.HasBytes final.external ⟨digest.toArray⟩) :
    readBytes region final = .ok digest := by
  have read (j : Fin region.size) :
      final.external[BitVec.ofNat 64 (region.start + j.val)]? = some digest[j.val] :=
    bytes.2 ⟨j.val, by simpa only [ByteArray.size, Vector.size_toArray] using j.isLt⟩
  unfold readBytes
  simp only [read]
  change Vector.ofFnM (fun j : Fin region.size => pure digest[j.val]) =
    (pure digest : Except Fault (Vector UInt8 region.size))
  rw [Vector.ofFnM_pure, Vector.ofFn_getElem]

theorem readBytes_sha256 {final : RamState} {start : Nat} {message : ByteArray}
    (bytes : (⟨start, 32⟩ : MemoryRegion).HasBytes final.external (NIST.SHA256.sha256 message)) :
    readBytes ⟨start, 32⟩ final = .ok (SHA2.SHA256 (SHA2.bytesToBits message)).bytes := by
  apply readBytes_of_hasBytes
  have equal : NIST.SHA256.sha256 message =
      ⟨(SHA2.SHA256 (SHA2.bytesToBits message)).bytes.toArray⟩ := by
    apply ByteArray.ext
    exact FIPS180.sha256_eq_fips180 message
  exact equal ▸ bytes

end Sha2.Proofs.Common.Memory
