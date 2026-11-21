import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11795a_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x111e7a bytes_l11795a) [(0, 81), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]
      2 0x111ef3 bytes_l11795a_1 b_l11795a_1 := by
  have f20 : InstrSpec 0x111ef3 [0x48, 0x8B, 0x42, 0x20] (LoadPre 0x111ef3 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x111ef3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111ef3 0 (.base 2 (.d8 0x20)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111ef3 0 (.base 2 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x111ef3 0x48 (by decide) 0 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x111ef7 [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111ef7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x111ef7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111ef7 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111ef7 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111ef7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ef7) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111eff) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 87) (by decide) rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
