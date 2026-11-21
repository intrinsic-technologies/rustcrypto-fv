import P256.Spec
import P256.Proofs.Program.SavePair

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev SavedEntry [Bindings] (initial s : RamState) := SavePair.SavedEntry initial s 0x2220 72

theorem save_correct [bindings : Bindings] {s : RamState} {input : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (h : ValidCallWithSlices signatureFromSlice s [input] slices) :
    ∃ t, SavedEntry s t :=
  SavePair.save_correct h.stackAvailable.1 (call_stack_avoids h)
    (outer_boundary h hm hb) (readyToStep hm hb) h.programLoaded h.atEntryPoint
    (by decide +kernel) ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end P256.Proofs.SignatureFromSlice.Wrapper
