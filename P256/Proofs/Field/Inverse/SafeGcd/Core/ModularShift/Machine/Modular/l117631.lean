import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117631 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111b51 bytes_l117631) (entryMap (live .l117631))
      0 0x111b51 bytes_l117631 b_l117631 := by
  exact Rest.cut

theorem block_l117631 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117631 :=
  Rest.liftedBlock (rest_l117631 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117631 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
