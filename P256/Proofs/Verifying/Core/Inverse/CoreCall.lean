import P256.Proofs.Verifying.Core.Inverse.Defs

namespace P256.Proofs.Verifying.Core.Inverse

open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def CoreStage [Bindings] : Prop :=
  ∀ {code : CodeMap}
    (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {p : Inputs} {boundary : ReturnBoundary}
    (_hready : EntryReady code initial) (_hrip : initial.RIP = 0x112190)
    (_hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (_hout : ReturnOutside boundary code)
    (_hcore : Atom.All code (Machine.lifted.locationOf .l1141e0 initial).arguments
      initial.external (coreCall fr p)),
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x112ffa ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l11504a final).arguments final.external
        (coreReturned fr p)

end P256.Proofs.Verifying.Core.Inverse
