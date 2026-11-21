import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11718a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1116aa bytes_l11718a) (entryMap (live .l11718a))
      0 0x1116aa bytes_l11718a b_l11718a := by
  exact Rest.cut

theorem block_l11718a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11718a :=
  Rest.liftedBlock (rest_l11718a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11718a x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
