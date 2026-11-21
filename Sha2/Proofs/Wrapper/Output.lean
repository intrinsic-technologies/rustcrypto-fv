import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.FIPS180.Computation

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

open Sha2.Spec Sha2.Spec.Program Standards.NIST Prelude X86 X86.Machine

 theorem readOutput_of_hasBytes {v : Variant} {initial final : RamState} (digest : Vector UInt8 v.outputBytes)
    (bytes : (outputRegion v.routine initial).HasBytes final.external ⟨digest.toArray⟩) :
    readOutput v.routine initial final = .ok digest := by
  have read (j : Fin v.outputBytes) :
      final.external[BitVec.ofNat 64 ((outputRegion v.routine initial).start + j.val)]? =
        some digest[j.val] := bytes.2 ⟨j.val, by simpa only [ByteArray.size, Vector.size_toArray] using j.isLt⟩
  unfold readOutput readBytes
  change (Vector.ofFnM (fun j : Fin v.outputBytes =>
    match final.external[BitVec.ofNat 64 ((outputRegion v.routine initial).start + j.val)]? with
    | some byte => Except.ok byte
    | none => Except.error (Fault.unmappedMemory
        (BitVec.ofNat 64 ((outputRegion v.routine initial).start + j.val))))) = .ok digest
  simp only [read]
  change Vector.ofFnM (fun j : Fin v.outputBytes => pure digest[j.val]) =
    (pure digest : Except Fault (Vector UInt8 v.outputBytes))
  rw [Vector.ofFnM_pure, Vector.ofFn_getElem]

 theorem readOutput_sha256 {initial final : RamState} {message : ByteArray}
    (bytes : (outputRegion sha256DigestSlices initial).HasBytes final.external (NIST.SHA256.sha256 message)) :
    readOutput sha256DigestSlices initial final =
      .ok (SHA2.SHA256 (SHA2.bytesToBits message)).bytes := by
  apply readOutput_of_hasBytes (v := .sha256)
  have equal : NIST.SHA256.sha256 message =
      ⟨(SHA2.SHA256 (SHA2.bytesToBits message)).bytes.toArray⟩ := by
    apply ByteArray.ext
    exact FIPS180.sha256_eq_fips180 message
  exact equal ▸ bytes

 theorem readOutput_variant {v : Variant} {initial final : RamState} {message : ByteArray}
    (bytes : (outputRegion v.routine initial).HasBytes final.external (v.hash message)) :
    readOutput v.routine initial final = .ok (v.digest message) := by
  cases v with
  | sha224 => exact readOutput_of_hasBytes (v := .sha224) _ bytes
  | sha256 => exact readOutput_sha256 bytes

end Sha2.Proofs.Wrapper
