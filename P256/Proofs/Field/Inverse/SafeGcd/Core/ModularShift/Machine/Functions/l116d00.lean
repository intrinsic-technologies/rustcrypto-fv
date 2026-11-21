import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116d00 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111220 bytes_l116d00) (entryMap (live .l116d00))
      0 0x111220 bytes_l116d00 b_l116d00 := by
  exact Rest.cut

theorem block_l116d00 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116d00 :=
  Rest.liftedBlock (rest_l116d00 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116d00 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
