import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1173e1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111901 bytes_l1173e1) (entryMap (live .l1173e1))
      12 0x111901 bytes_l1173e1 b_l1173e1 := by
  have f0 : InstrSpec 0x111901 [0x4D, 0x31, 0xEA] (fun s => s.RIP = 0x111901) (xorR64R64Effect 0x111901 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111901 10 13).toInstrSpec (xor_r64_r64_effect_step 0x111901 0x4d 0xea (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111904 [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x111904) (negR64Effect 0x111904 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x111904 7).toInstrSpec (neg_r64_effect_step 0x111904 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111907 [0x4C, 0x21, 0xD7] (fun s => s.RIP = 0x111907) (andR64R64Effect 0x111907 7 10)
      [.gpr 7, .gpr 10] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111907 7 10).toInstrSpec (and_r64_r64_effect_step 0x111907 0x4c 0xd7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11190a [0x4C, 0x31, 0xEF] (fun s => s.RIP = 0x11190a) (xorR64R64Effect 0x11190a 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11190a 7 13).toInstrSpec (xor_r64_r64_effect_step 0x11190a 0x4c 0xef (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11190d [0x4C, 0x31, 0xDD] (fun s => s.RIP = 0x11190d) (xorR64R64Effect 0x11190d 5 11)
      [.gpr 5, .gpr 11] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11190d 5 11).toInstrSpec (xor_r64_r64_effect_step 0x11190d 0x4c 0xdd (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111910 [0x49, 0xF7, 0xDE] (fun s => s.RIP = 0x111910) (negR64Effect 0x111910 14)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (negR64Effect_footprint 0x111910 14).toInstrSpec (neg_r64_effect_step 0x111910 0x49 0xde (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111913 [0x49, 0x21, 0xEE] (fun s => s.RIP = 0x111913) (andR64R64Effect 0x111913 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111913 14 5).toInstrSpec (and_r64_r64_effect_step 0x111913 0x49 0xee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111916 [0x4D, 0x31, 0xDE] (fun s => s.RIP = 0x111916) (xorR64R64Effect 0x111916 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111916 14 11).toInstrSpec (xor_r64_r64_effect_step 0x111916 0x4d 0xde (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111919 [0x4D, 0x31, 0xE0] (fun s => s.RIP = 0x111919) (xorR64R64Effect 0x111919 8 12)
      [.gpr 8, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111919 8 12).toInstrSpec (xor_r64_r64_effect_step 0x111919 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11191c [0x49, 0xF7, 0xDF] (fun s => s.RIP = 0x11191c) (negR64Effect 0x11191c 15)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (negR64Effect_footprint 0x11191c 15).toInstrSpec (neg_r64_effect_step 0x11191c 0x49 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11191f [0x4D, 0x21, 0xC7] (fun s => s.RIP = 0x11191f) (andR64R64Effect 0x11191f 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11191f 15 8).toInstrSpec (and_r64_r64_effect_step 0x11191f 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111922 [0x4D, 0x31, 0xE7] (fun s => s.RIP = 0x111922) (xorR64R64Effect 0x111922 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111922 15 12).toInstrSpec (xor_r64_r64_effect_step 0x111922 0x4d 0xe7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111904) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111907) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11190a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11190d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111910) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111913) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111916) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111919) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11191c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x11191f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 73), (22, 22), (39, 39), (51, 51)]) (p' := 0x111922) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x111925) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l1173e1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1173e1 :=
  Rest.liftedBlock (rest_l1173e1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1173e1 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
