import Hkdf.Proofs.NewExpand.Wrapper.Copy.Memcpy
import Hkdf.Proofs.NewExpand.Wrapper.Copy.Descriptor
import Hkdf.Proofs.NewExpand.Wrapper.Copy.Pre

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copyToExpand [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    {s : RamState} (start : ExtractReturn initial s (RFC5869.extract .sha256 salt ikm))
    (stride : UnitStringStride bindings) :
    ∃ t, ExpandEntry initial t (RFC5869.extract .sha256 salt ikm) info length := by
  obtain ⟨u, copied⟩ := Copy.copyKey hCall start stride
  obtain ⟨t, prepared⟩ := Copy.prepareExpand hCall copied
  exact ⟨t, Copy.expandEntry hCall prepared stride⟩

end Hkdf.Proofs.NewExpand.Wrapper
