import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116d4e_1 [Bindings] (code : CodeMap) :
    Rest (n := 97) code lifted (codeRange 0x11126e bytes_l116d4e) [(0, 92), (1, 75), (2, 93), (3, 95), (4, 4), (5, 84), (6, 6), (7, 7), (8, 8), (9, 69), (10, 56), (11, 11), (12, 82), (13, 88), (14, 58), (15, 71), (22, 22), (39, 39), (51, 51)]
      2 0x1112af bytes_l116d4e_1 b_l116d4e_1 := by
  have f20 : InstrSpec 0x1112af [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x1112af) (movR64R64Effect 0x1112af 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1112af 1 2).toInstrSpec (mov_r64_r64_effect_step 0x1112af 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1112b2 [0x4D, 0x31, 0xC5] (fun s => s.RIP = 0x1112b2) (xorR64R64Effect 0x1112b2 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1112b2 13 8).toInstrSpec (xor_r64_r64_effect_step 0x1112b2 0x4d 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 92), (1, 97), (2, 93), (3, 95), (4, 4), (5, 84), (6, 6), (7, 7), (8, 8), (9, 69), (10, 56), (11, 11), (12, 82), (13, 88), (14, 58), (15, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112b2) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f21 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 92), (1, 97), (2, 93), (3, 95), (4, 4), (5, 84), (6, 6), (7, 7), (8, 8), (9, 69), (10, 56), (11, 11), (12, 82), (13, 99), (14, 58), (15, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112b5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 101) (by decide) rfl
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
