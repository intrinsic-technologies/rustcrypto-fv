import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117849_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x111d69 bytes_l117849) [(0, 82), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]
      1 0x111dd3 bytes_l117849_1 b_l117849_1 := by
  have f20 : InstrSpec 0x111dd3 [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111dd3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x111dd3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111dd3 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111dd3 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111dd3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ddb) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 85) (by decide) rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
