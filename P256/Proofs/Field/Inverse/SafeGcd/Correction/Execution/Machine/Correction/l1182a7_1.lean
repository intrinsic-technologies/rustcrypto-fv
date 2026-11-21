import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Correction.l118288

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1182a7_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x1127c7 bytes_l1182a7) [(0, 0), (1, 61), (2, 86), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 88), (22, 22), (39, 39), (51, 51)]
      3 0x11280f bytes_l1182a7_1 b_l1182a7_1 := by
  have f20 : InstrSpec 0x11280f [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x11280f) (negR64Effect 0x11280f 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x11280f 2).toInstrSpec (neg_r64_effect_step 0x11280f 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x112812 [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x112812) (andR64R64Effect 0x112812 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112812 2 15).toInstrSpec (and_r64_r64_effect_step 0x112812 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x112815 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x112815) (xorR64R64Effect 0x112815 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x112815 2 0).toInstrSpec (xor_r64_r64_effect_step 0x112815 0x48 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 61), (2, 90), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 88), (22, 22), (39, 39), (51, 51)]) (p' := 0x112812) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 61), (2, 92), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 88), (22, 22), (39, 39), (51, 51)]) (p' := 0x112815) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 61), (2, 94), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 88), (22, 22), (39, 39), (51, 51)]) (p' := 0x112818) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 96) (by decide) rfl

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
