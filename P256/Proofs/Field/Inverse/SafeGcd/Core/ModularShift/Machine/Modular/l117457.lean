import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117457 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111977 bytes_l117457) (entryMap (live .l117457))
      12 0x111977 bytes_l117457 b_l117457 := by
  have f0 : InstrSpec 0x111977 [0x49, 0x09, 0xFC] (fun s => s.RIP = 0x111977) (orR64R64Effect 0x111977 12 7)
      [.gpr 12, .gpr 7] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111977 12 7).toInstrSpec (or_r64_r64_effect_step 0x111977 0x49 0xfc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11197a [0x89, 0xC1] (fun s => s.RIP = 0x11197a) (movR32R32Effect 0x11197a 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x11197a 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x11197a 0xc1 (by decide)) pre_rip
  have f2 : InstrSpec 0x11197c [0x49, 0xD3, 0xE6] (fun s => s.RIP = 0x11197c) (shlR64ClEffect 0x11197c 3 14)
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x11197c 3 14).toInstrSpec (shl_r64_cl_effect_step 0x11197c 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11197f [0x4C, 0x89, 0xFB] (fun s => s.RIP = 0x11197f) (movR64R64Effect 0x11197f 3 15)
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11197f 3 15).toInstrSpec (mov_r64_r64_effect_step 0x11197f 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111982 [0x89, 0xE9] (fun s => s.RIP = 0x111982) (movR32R32Effect 0x111982 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111982 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x111982 0xe9 (by decide)) pre_rip
  have f5 : InstrSpec 0x111984 [0x48, 0xD3, 0xEB] (fun s => s.RIP = 0x111984) (shrR64ClEffect 0x111984 3 3)
      [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x111984 3 3).toInstrSpec (shr_r64_cl_effect_step 0x111984 0x48 0xeb (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111987 [0x89, 0xC1] (fun s => s.RIP = 0x111987) (movR32R32Effect 0x111987 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111987 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x111987 0xc1 (by decide)) pre_rip
  have f7 : InstrSpec 0x111989 [0x49, 0xD3, 0xE7] (fun s => s.RIP = 0x111989) (shlR64ClEffect 0x111989 3 15)
      [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x111989 3 15).toInstrSpec (shl_r64_cl_effect_step 0x111989 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11198c [0x89, 0xE9] (fun s => s.RIP = 0x11198c) (movR32R32Effect 0x11198c 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x11198c 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x11198c 0xe9 (by decide)) pre_rip
  have f9 : InstrSpec 0x11198e [0x48, 0xD3, 0xEA] (fun s => s.RIP = 0x11198e) (shrR64ClEffect 0x11198e 3 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x11198e 3 2).toInstrSpec (shr_r64_cl_effect_step 0x11198e 0x48 0xea (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111991 [0x4C, 0x09, 0xF3] (fun s => s.RIP = 0x111991) (orR64R64Effect 0x111991 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111991 3 14).toInstrSpec (or_r64_r64_effect_step 0x111991 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111994 [0x4C, 0x09, 0xFA] (fun s => s.RIP = 0x111994) (orR64R64Effect 0x111994 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111994 2 15).toInstrSpec (or_r64_r64_effect_step 0x111994 0x4c 0xfa (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11197a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11197c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11197f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 59), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111982) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 59), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111984) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 63), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111987) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 63), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111989) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 63), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11198c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 63), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11198e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 71), (3, 63), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111991) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 69), (2, 71), (3, 73), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111994) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 69), (2, 75), (3, 73), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111997) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l117457 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117457 :=
  Rest.liftedBlock (rest_l117457 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117457 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
