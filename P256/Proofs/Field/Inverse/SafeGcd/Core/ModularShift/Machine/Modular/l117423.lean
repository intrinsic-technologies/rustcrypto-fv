import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117423 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111943 bytes_l117423) (entryMap (live .l117423))
      18 0x111943 bytes_l117423 b_l117423 := by
  have f0 : InstrSpec 0x111943 [0x89, 0xC8] (fun s => s.RIP = 0x111943) (movR32R32Effect 0x111943 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x111943 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x111943 0xc8 (by decide)) pre_rip
  have f1 : InstrSpec 0x111945 [0x4D, 0x89, 0xEA] (fun s => s.RIP = 0x111945) (movR64R64Effect 0x111945 10 13)
      [.gpr 13] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x111945 10 13).toInstrSpec (mov_r64_r64_effect_step 0x111945 0x4d 0xea (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111948 [0x89, 0xC1] (fun s => s.RIP = 0x111948) (movR32R32Effect 0x111948 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111948 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x111948 0xc1 (by decide)) pre_rip
  have f3 : InstrSpec 0x11194a [0x49, 0xD3, 0xE2] (fun s => s.RIP = 0x11194a) (shlR64ClEffect 0x11194a 3 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x11194a 3 10).toInstrSpec (shl_r64_cl_effect_step 0x11194a 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11194d [0x48, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x11194d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11194d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11194d 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11194d 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x11194d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x111952 [0x48, 0x31, 0xF3] (fun s => s.RIP = 0x111952) (xorR64R64Effect 0x111952 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111952 3 6).toInstrSpec (xor_r64_r64_effect_step 0x111952 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111955 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x111955) (negR64Effect 0x111955 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x111955 2).toInstrSpec (neg_r64_effect_step 0x111955 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111958 [0x49, 0x89, 0xFB] (fun s => s.RIP = 0x111958) (movR64R64Effect 0x111958 11 7)
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x111958 11 7).toInstrSpec (mov_r64_r64_effect_step 0x111958 0x49 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11195b [0x8B, 0x6C, 0x24, 0x44] (LoadPre 0x11195b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x11195b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11195b 5 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x11195b 5 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x11195b 5 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11195f [0x89, 0xE9] (fun s => s.RIP = 0x11195f) (movR32R32Effect 0x11195f 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x11195f 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x11195f 0xe9 (by decide)) pre_rip
  have f10 : InstrSpec 0x111961 [0x49, 0xD3, 0xEB] (fun s => s.RIP = 0x111961) (shrR64ClEffect 0x111961 3 11)
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x111961 3 11).toInstrSpec (shr_r64_cl_effect_step 0x111961 0x49 0xeb (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111964 [0x89, 0xC1] (fun s => s.RIP = 0x111964) (movR32R32Effect 0x111964 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111964 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x111964 0xc1 (by decide)) pre_rip
  have f12 : InstrSpec 0x111966 [0x48, 0xD3, 0xE7] (fun s => s.RIP = 0x111966) (shlR64ClEffect 0x111966 3 7)
      [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x111966 3 7).toInstrSpec (shl_r64_cl_effect_step 0x111966 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111969 [0x4D, 0x89, 0xF4] (fun s => s.RIP = 0x111969) (movR64R64Effect 0x111969 12 14)
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x111969 12 14).toInstrSpec (mov_r64_r64_effect_step 0x111969 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11196c [0x89, 0xE9] (fun s => s.RIP = 0x11196c) (movR32R32Effect 0x11196c 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x11196c 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x11196c 0xe9 (by decide)) pre_rip
  have f15 : InstrSpec 0x11196e [0x49, 0xD3, 0xEC] (fun s => s.RIP = 0x11196e) (shrR64ClEffect 0x11196e 3 12)
      [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x11196e 3 12).toInstrSpec (shr_r64_cl_effect_step 0x11196e 0x49 0xec (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x111971 [0x48, 0x21, 0xDA] (fun s => s.RIP = 0x111971) (andR64R64Effect 0x111971 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111971 2 3).toInstrSpec (and_r64_r64_effect_step 0x111971 0x48 0xda (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x111974 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x111974) (xorR64R64Effect 0x111974 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111974 2 6).toInstrSpec (xor_r64_r64_effect_step 0x111974 0x48 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111945) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111948) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11194a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11194d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (6, 61), (7, 7), (9, 9), (10, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111952) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 63), (4, 4), (6, 61), (7, 7), (9, 9), (10, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111955) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 57), (2, 65), (3, 63), (4, 4), (6, 61), (7, 7), (9, 9), (10, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111958) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 57), (2, 65), (3, 63), (4, 4), (6, 61), (7, 7), (9, 9), (10, 59), (11, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11195b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 57), (2, 65), (3, 63), (4, 4), (5, 69), (6, 61), (7, 7), (9, 9), (10, 59), (11, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11195f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 71), (2, 65), (3, 63), (4, 4), (5, 69), (6, 61), (7, 7), (9, 9), (10, 59), (11, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111961) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 71), (2, 65), (3, 63), (4, 4), (5, 69), (6, 61), (7, 7), (9, 9), (10, 59), (11, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111964) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 75), (2, 65), (3, 63), (4, 4), (5, 69), (6, 61), (7, 7), (9, 9), (10, 59), (11, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111966) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 75), (2, 65), (3, 63), (4, 4), (5, 69), (6, 61), (7, 77), (9, 9), (10, 59), (11, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111969) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 75), (2, 65), (3, 63), (4, 4), (5, 69), (6, 61), (7, 77), (9, 9), (10, 59), (11, 73), (12, 79), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11196c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 81), (2, 65), (3, 63), (4, 4), (5, 69), (6, 61), (7, 77), (9, 9), (10, 59), (11, 73), (12, 79), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11196e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 81), (2, 65), (3, 63), (4, 4), (5, 69), (6, 61), (7, 77), (9, 9), (10, 59), (11, 73), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111971) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 81), (2, 85), (3, 63), (4, 4), (5, 69), (6, 61), (7, 77), (9, 9), (10, 59), (11, 73), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111974) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 81), (2, 87), (3, 63), (4, 4), (5, 69), (6, 61), (7, 77), (9, 9), (10, 59), (11, 73), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111977) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 89) (by decide) rfl

theorem block_l117423 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117423 :=
  Rest.liftedBlock (rest_l117423 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117423 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
