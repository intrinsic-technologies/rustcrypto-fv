import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Support

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open Prelude X86 X86.Machine X86Proofs

abbrev FrameState [Bindings] (s t : RamState) (stackOffset : BitVec 64 := 136) : Prop :=
  P256.Proofs.Program.ScalarFrame.FrameState s t 257 168 stackOffset

end P256.Proofs.Verifying.Combination.Naf.Machine
