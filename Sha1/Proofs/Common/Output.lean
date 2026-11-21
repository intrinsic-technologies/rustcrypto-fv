import Sha1.Spec.Program

namespace Sha1.Proofs.Common

open Prelude X86 X86.Machine Sha1.Spec.Program

set_option linter.unusedVariables false in
 theorem readBytes_of_hasBytes {initial final : RamState} {region : MemoryRegion}
    {digest : Vector UInt8 region.size}
    (bytes : region.HasBytes final.external ⟨digest.toArray⟩) :
    readBytes region final.external = .ok digest := by
  have read (j : Fin region.size) :
      final.external[BitVec.ofNat 64 (region.start + j.val)]? = some digest[j.val] := by
    exact bytes.2 ⟨j.val, by simpa only [ByteArray.size, Vector.size_toArray] using j.isLt⟩
  unfold readBytes
  simp only [read]
  change Vector.ofFnM (fun j : Fin region.size => pure digest[j.val]) =
    (pure digest : Except Machine.Fault (Vector UInt8 region.size))
  rw [Vector.ofFnM_pure, Vector.ofFn_getElem]

end Sha1.Proofs.Common
