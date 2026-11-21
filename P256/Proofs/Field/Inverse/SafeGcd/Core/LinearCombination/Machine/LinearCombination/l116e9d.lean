import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116e9d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1113bd bytes_l116e9d) (entryMap (live .l116e9d))
      8 0x1113bd bytes_l116e9d b_l116e9d := by
  have f0 : InstrSpec 0x1113bd [0x44, 0x88, 0x1C, 0x24] (StorePre 0x1113bd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113bd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1113bd 4 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1113bd 4 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x1113bd 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1113c1 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x1113c1) (xorR64R64Effect 0x1113c1 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1113c1 2 0).toInstrSpec (xor_r64_r64_effect_step 0x1113c1 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1113c4 [0x44, 0x0F, 0xB6, 0x3C, 0x24] (LoadPre 0x1113c4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113c4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1113c4 5 15 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1113c4 5 15 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1113c4 0x44 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1113c9 [0x49, 0xF7, 0xDF] (fun s => s.RIP = 0x1113c9) (negR64Effect 0x1113c9 15)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (negR64Effect_footprint 0x1113c9 15).toInstrSpec (neg_r64_effect_step 0x1113c9 0x49 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1113cc [0x49, 0x21, 0xD7] (fun s => s.RIP = 0x1113cc) (andR64R64Effect 0x1113cc 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1113cc 15 2).toInstrSpec (and_r64_r64_effect_step 0x1113cc 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1113cf [0x49, 0x31, 0xC7] (fun s => s.RIP = 0x1113cf) (xorR64R64Effect 0x1113cf 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1113cf 15 0).toInstrSpec (xor_r64_r64_effect_step 0x1113cf 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1113d2 [0x44, 0x88, 0x1C, 0x24] (StorePre 0x1113d2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113d2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1113d2 4 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1113d2 4 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x1113d2 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1113d6 [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x1113d6) (movR64R64Effect 0x1113d6 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1113d6 0 4).toInstrSpec (mov_r64_r64_effect_step 0x1113d6 0x48 0xe0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113cc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113cf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113d2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113d6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113d9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l116e9d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116e9d :=
  Rest.liftedBlock (rest_l116e9d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116e9d x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
