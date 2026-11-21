import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11715a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11167a bytes_l11715a) (entryMap (live .l11715a))
      0 0x11167a bytes_l11715a b_l11715a := by
  exact Rest.cut

theorem block_l11715a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11715a :=
  Rest.liftedBlock (rest_l11715a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11715a x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
