import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116d95_1 [Bindings] (code : CodeMap) :
    Rest (n := 95) code lifted (codeRange 0x1112b5 bytes_l116d95) [(0, 93), (1, 62), (2, 82), (3, 59), (4, 4), (5, 86), (6, 6), (7, 7), (8, 90), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)]
      1 0x1112ff bytes_l116d95_1 b_l116d95_1 := by
  have f20 : InstrSpec 0x1112ff [0x49, 0xF7, 0x63, 0x18] (LoadPre 0x1112ff (fun s => AddrMode.addr (.base 11 (.d8 0x18)) s (0x1112ff + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1112ff 4 (.base 11 (.d8 0x18)))
      [.gpr 0, .gpr 11] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x1112ff 4 (.base 11 (.d8 0x18))).toInstrSpec (mul_m64_effect_step 0x1112ff 0x49 (by decide) (.base 11 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 96) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 97) (ρ' := [(0, 95), (1, 62), (2, 96), (3, 59), (4, 4), (5, 86), (6, 6), (7, 7), (8, 90), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x111303) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 98) (by decide) rfl
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
