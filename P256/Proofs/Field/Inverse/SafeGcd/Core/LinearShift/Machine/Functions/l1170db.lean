import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1170db [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1115fb bytes_l1170db) (entryMap (live .l1170db))
      2 0x1115fb bytes_l1170db b_l1170db := by
  have f0 : InstrSpec 0x1115fb [0x85, 0xED] (fun s => s.RIP = 0x1115fb) (testR32R32Effect 0x1115fb 2 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x1115fb 2 5 5).toInstrSpec (test_r32_r32_effect_step 0x1115fb 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115fd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1115fd 4 0xa7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1170db [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1170db :=
  Rest.liftedBlock (rest_l1170db code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1170db x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
