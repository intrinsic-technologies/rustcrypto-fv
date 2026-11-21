import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Core.l117a59_1
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117a59 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111f79 bytes_l117a59) (entryMap (live .l117a59))
      21 0x111f79 bytes_l117a59 b_l117a59 := by
  have f0 : InstrSpec 0x111f79 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x111f79 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f79 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111f79 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x111f79 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x111f79 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x111f7e [0x4C, 0x21, 0xCE] (fun s => s.RIP = 0x111f7e) (andR64R64Effect 0x111f7e 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111f7e 6 9).toInstrSpec (and_r64_r64_effect_step 0x111f7e 0x4c 0xce (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111f81 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x111f81) (movR64R64Effect 0x111f81 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x111f81 7 6).toInstrSpec (mov_r64_r64_effect_step 0x111f81 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x111f84 [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x111f84) (negR64Effect 0x111f84 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x111f84 7).toInstrSpec (neg_r64_effect_step 0x111f84 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111f87 [0x48, 0x31, 0xF7] (fun s => s.RIP = 0x111f87) (xorR64R64Effect 0x111f87 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111f87 7 6).toInstrSpec (xor_r64_r64_effect_step 0x111f87 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111f8a [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x111f8a) (negR64Effect 0x111f8a 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x111f8a 0).toInstrSpec (neg_r64_effect_step 0x111f8a 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111f8d [0x48, 0x21, 0xF8] (fun s => s.RIP = 0x111f8d) (andR64R64Effect 0x111f8d 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111f8d 0 7).toInstrSpec (and_r64_r64_effect_step 0x111f8d 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111f90 [0x48, 0x31, 0xF0] (fun s => s.RIP = 0x111f90) (xorR64R64Effect 0x111f90 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111f90 0 6).toInstrSpec (xor_r64_r64_effect_step 0x111f90 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111f93 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x111f93) (andR64R64Effect 0x111f93 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111f93 1 9).toInstrSpec (and_r64_r64_effect_step 0x111f93 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111f96 [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x111f96) (movR64R64Effect 0x111f96 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x111f96 6 1).toInstrSpec (mov_r64_r64_effect_step 0x111f96 0x48 0xce (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111f99 [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x111f99) (negR64Effect 0x111f99 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x111f99 6).toInstrSpec (neg_r64_effect_step 0x111f99 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111f9c [0x48, 0x31, 0xCE] (fun s => s.RIP = 0x111f9c) (xorR64R64Effect 0x111f9c 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111f9c 6 1).toInstrSpec (xor_r64_r64_effect_step 0x111f9c 0x48 0xce (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111f9f [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x111f9f) (negR64Effect 0x111f9f 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x111f9f 2).toInstrSpec (neg_r64_effect_step 0x111f9f 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111fa2 [0x48, 0x21, 0xF2] (fun s => s.RIP = 0x111fa2) (andR64R64Effect 0x111fa2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111fa2 2 6).toInstrSpec (and_r64_r64_effect_step 0x111fa2 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111fa5 [0x48, 0x31, 0xCA] (fun s => s.RIP = 0x111fa5) (xorR64R64Effect 0x111fa5 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111fa5 2 1).toInstrSpec (xor_r64_r64_effect_step 0x111fa5 0x48 0xca (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x111fa8 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111fa8) (movR32Imm32Effect 0x111fa8 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x111fa8 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x111fa8 0xbf (by decide) 0x1) pre_rip
  have f16 : InstrSpec 0x111fad [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x111fad) (movR32R32Effect 0x111fad 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111fad 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x111fad 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x111fb0 [0x31, 0xF6] (fun s => s.RIP = 0x111fb0) (xorR32R32Effect 0x111fb0 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x111fb0 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x111fb0 0xf6 (by decide)) pre_rip
  have f18 : InstrSpec 0x111fb2 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x111fb2) (xorR32R32Effect 0x111fb2 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x111fb2 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x111fb2 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x111fb5 [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111fb5) (movR32Imm32Effect 0x111fb5 6 12 0x1)
      [] [] [.reg 12, .rip] :=
    (movR32Imm32Effect_footprint 0x111fb5 6 12 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x111fb5 0x41 0xbc (by decide) (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f81) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f84) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f87) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f8a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f8d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f90) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f93) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 69), (2, 2), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f96) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 69), (2, 2), (4, 4), (5, 5), (6, 71), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f99) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 69), (2, 2), (4, 4), (5, 5), (6, 73), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f9c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 67), (1, 69), (2, 2), (4, 4), (5, 5), (6, 75), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f9f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 67), (1, 69), (2, 77), (4, 4), (5, 5), (6, 75), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fa2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 67), (1, 69), (2, 79), (4, 4), (5, 5), (6, 75), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fa5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 67), (1, 69), (2, 81), (4, 4), (5, 5), (6, 75), (7, 61), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fa8) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 67), (1, 69), (2, 81), (4, 4), (5, 5), (6, 75), (7, 83), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fad) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 67), (1, 85), (2, 81), (4, 4), (5, 5), (6, 75), (7, 83), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fb0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 67), (1, 85), (2, 81), (4, 4), (5, 5), (6, 87), (7, 83), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fb2) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 67), (1, 85), (2, 81), (4, 4), (5, 5), (6, 87), (7, 83), (8, 8), (9, 9), (13, 13), (14, 89), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fb5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 67), (1, 85), (2, 81), (4, 4), (5, 5), (6, 87), (7, 83), (8, 8), (9, 9), (12, 91), (13, 13), (14, 89), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fbb) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l117a59_1 code

theorem block_l117a59 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117a59 :=
  Rest.liftedBlock (rest_l117a59 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117a59 x hx)

section Steps

variable (code : CodeMap)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64)
    (cf pf af zf sf of : Bool) (df : BitVec 1)
    (xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 : BitVec 128)
    (mxcsr : BitVec 32) (st0 st1 st2 st3 st4 st5 st6 st7 : BitVec 80) (fsw : BitVec 16)
    (fcc : BitVec 4) (ftw fcw : BitVec 16) (fpuPtr : BitVec 171) (mem : Ram)

set_option hygiene false in
local notation "args" =>
  (#v[⟨64, rax⟩, ⟨64, rcx⟩, ⟨64, rdx⟩, ⟨64, rbx⟩, ⟨64, rsp⟩, ⟨64, rbp⟩, ⟨64, rsi⟩, ⟨64, rdi⟩, ⟨64, r8⟩, ⟨64, r9⟩, ⟨64, r10⟩, ⟨64, r11⟩, ⟨64, r12⟩, ⟨64, r13⟩, ⟨64, r14⟩, ⟨64, r15⟩] : Vector Value 16) ++
  (#v[.ofBool cf, .ofBool pf, .ofBool af, .ofBool zf, .ofBool sf, .ofBool of, ⟨1, df⟩] : Vector Value 7) ++
  (#v[⟨128, xmm0⟩, ⟨128, xmm1⟩, ⟨128, xmm2⟩, ⟨128, xmm3⟩, ⟨128, xmm4⟩, ⟨128, xmm5⟩, ⟨128, xmm6⟩, ⟨128, xmm7⟩, ⟨128, xmm8⟩, ⟨128, xmm9⟩, ⟨128, xmm10⟩, ⟨128, xmm11⟩, ⟨128, xmm12⟩, ⟨128, xmm13⟩, ⟨128, xmm14⟩, ⟨128, xmm15⟩, ⟨32, mxcsr⟩, ⟨80, st0⟩, ⟨80, st1⟩, ⟨80, st2⟩, ⟨80, st3⟩, ⟨80, st4⟩, ⟨80, st5⟩, ⟨80, st6⟩, ⟨80, st7⟩, ⟨16, fsw⟩, ⟨4, fcc⟩, ⟨16, ftw⟩, ⟨16, fcw⟩, ⟨171, fpuPtr⟩] : Vector Value 30)

theorem_by block_l117a59_eval :
    program.runBlock (dialect code) ⟨.l117a59, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
