import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1170d6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1115f6 bytes_l1170d6) (entryMap (live .l1170d6))
      2 0x1115f6 bytes_l1170d6 b_l1170d6 := by
  have f0 : InstrSpec 0x1115f6 [0x83, 0xFD, 0x40] (fun s => s.RIP = 0x1115f6) (cmpR32Imm8Effect 0x1115f6 3 5 0x40)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1115f6 3 5 0x40).toInstrSpec (cmp_r32_imm8_effect_step 0x1115f6 0xfd 0x40 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115f9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1115f9 3 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1170d6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1170d6 :=
  Rest.liftedBlock (rest_l1170d6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1170d6 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
