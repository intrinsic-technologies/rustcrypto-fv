import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117a59_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x111f79 bytes_l117a59) [(0, 67), (1, 85), (2, 81), (4, 4), (5, 5), (6, 87), (7, 83), (8, 8), (9, 9), (12, 91), (13, 13), (14, 89), (22, 22), (39, 39), (51, 51)]
      1 0x111fbb bytes_l117a59_1 b_l117a59_1 := by
  have f20 : InstrSpec 0x111fbb [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x111fbb) (fun _ => nopEffect 0x111fbb 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x111fbb 5).toInstrSpec (nop_m_effect_step 0x111fbb [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 67), (1, 85), (2, 81), (4, 4), (5, 5), (6, 87), (7, 83), (8, 8), (9, 9), (12, 91), (13, 13), (14, 89), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fc0) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 94) (by decide) rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
