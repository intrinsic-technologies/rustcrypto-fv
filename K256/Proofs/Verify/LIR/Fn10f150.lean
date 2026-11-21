import K256.Proofs.Verify.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l10f150 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f150 bytes_l10f150) (entryMap (live .l10f150))
      15 0x10f150 bytes_l10f150 b_l10f150 := by
  have f0 : InstrSpec 0x10f150 [0x55] (PushPre 0x10f150 1) (pushR64Effect 0x10f150 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10f150 1 5).toInstrSpec (push_r64_effect_step 0x10f150 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10f151 [0x41, 0x57] (PushPre 0x10f151 2) (pushR64Effect 0x10f151 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10f151 2 15).toInstrSpec (push_r64_rex_effect_step 0x10f151 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10f153 [0x41, 0x56] (PushPre 0x10f153 2) (pushR64Effect 0x10f153 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10f153 2 14).toInstrSpec (push_r64_rex_effect_step 0x10f153 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10f155 [0x41, 0x55] (PushPre 0x10f155 2) (pushR64Effect 0x10f155 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10f155 2 13).toInstrSpec (push_r64_rex_effect_step 0x10f155 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10f157 [0x41, 0x54] (PushPre 0x10f157 2) (pushR64Effect 0x10f157 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10f157 2 12).toInstrSpec (push_r64_rex_effect_step 0x10f157 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10f159 [0x53] (PushPre 0x10f159 1) (pushR64Effect 0x10f159 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10f159 1 3).toInstrSpec (push_r64_effect_step 0x10f159 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10f15a [0x48, 0x81, 0xEC, 0x88, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10f15a) (subR64Imm32Effect 0x10f15a 4 0x288)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10f15a 4 0x288).toInstrSpec (sub_r64_imm32_effect_step 0x10f15a 0x48 0xec 0x288 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10f161 [0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x10f161 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10f161 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f161 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f161 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x10f161 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10f169 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x10f169) (movR64R64Effect 0x10f169 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10f169 3 2).toInstrSpec (mov_r64_r64_effect_step 0x10f169 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10f16c [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x10f16c) (movR64R64Effect 0x10f16c 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10f16c 12 6).toInstrSpec (mov_r64_r64_effect_step 0x10f16c 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10f16f [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x10f16f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10f16f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f16f 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f16f 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10f16f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10f174 [0x4C, 0x8D, 0x6C, 0x24, 0x38] (fun s => s.RIP = 0x10f174) (leaR64Effect 0x10f174 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10f174 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f174 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10f179 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x10f179) (movR64R64Effect 0x10f179 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f179 7 13).toInstrSpec (mov_r64_r64_effect_step 0x10f179 0x4c 0xef (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10f17c [0x48, 0xC7, 0xC2, 0x00, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x10f17c) (movR64Imm32Effect 0x10f17c 2 0x202200)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10f17c 2 0x202200).toInstrSpec (mov_r64_imm32_effect_step 0x10f17c 0x48 0xc2 (by decide) (by decide) (by decide) 0x202200) pre_rip
  have f14 : InstrSpec 0x10f183 [0xE8, 0x68, 0xC7, 0x00, 0x00] (PushPre 0x10f183 5) (callEffect (fun _ => 0x11b8f0) 0x10f188)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f183 0x11b8f0 0x10f188).toInstrSpec (call_rel32_effect_step 0x10f183 0xc768 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f151) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f153) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f155) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f157) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f159) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f15a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f161) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f169) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 68), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f16c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 68), (4, 65), (5, 5), (6, 6), (7, 7), (12, 70), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f16f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 68), (4, 65), (5, 5), (6, 6), (7, 7), (12, 70), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f174) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 68), (4, 65), (5, 5), (6, 6), (7, 7), (12, 70), (13, 73), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f179) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 68), (4, 65), (5, 5), (6, 6), (7, 75), (12, 70), (13, 73), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f17c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 77), (3, 68), (4, 65), (5, 5), (6, 6), (7, 75), (12, 70), (13, 73), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f183) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 1), (2, 77), (3, 68), (4, 79), (5, 5), (6, 6), (7, 75), (12, 70), (13, 73), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f0) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l10f150 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f150 :=
  Rest.liftedBlock (rest_l10f150 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f150 x hx)

theorem rest_l10f188 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f188 bytes_l10f188) (entryMap (live .l10f188))
      5 0x10f188 bytes_l10f188 b_l10f188 := by
  have f0 : InstrSpec 0x10f188 [0x48, 0x8D, 0xAC, 0x24, 0x68, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10f188) (leaR64Effect 0x10f188 5 (.sib 4 none 0 (.d32 0x268)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x10f188 5 (.sib 4 none 0 (.d32 0x268))).toInstrSpec (lea_r64_effect_step 0x10f188 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x268)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f190 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x10f190) (movR64R64Effect 0x10f190 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f190 7 5).toInstrSpec (mov_r64_r64_effect_step 0x10f190 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f193 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10f193) (movR64R64Effect 0x10f193 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f193 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10f193 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f196 [0x48, 0xC7, 0xC2, 0x20, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x10f196) (movR64Imm32Effect 0x10f196 2 0x202220)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10f196 2 0x202220).toInstrSpec (mov_r64_imm32_effect_step 0x10f196 0x48 0xc2 (by decide) (by decide) (by decide) 0x202220) pre_rip
  have f4 : InstrSpec 0x10f19d [0xE8, 0x1E, 0xA8, 0xFF, 0xFF] (PushPre 0x10f19d 5) (callEffect (fun _ => 0x1099c0) 0x10f1a2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f19d 0x1099c0 0x10f1a2).toInstrSpec (call_rel32_effect_step 0x10f19d 0xffffa81e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f190) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f193) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f196) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f19d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10f188 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f188 :=
  Rest.liftedBlock (rest_l10f188 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f188 x hx)

theorem rest_l10f1a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f1a2 bytes_l10f1a2) (entryMap (live .l10f1a2))
      5 0x10f1a2 bytes_l10f1a2 b_l10f1a2 := by
  have f0 : InstrSpec 0x10f1a2 [0x4C, 0x8D, 0x6C, 0x24, 0x38] (fun s => s.RIP = 0x10f1a2) (leaR64Effect 0x10f1a2 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10f1a2 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f1a2 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f1a7 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x10f1a7) (movR64R64Effect 0x10f1a7 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f1a7 7 13).toInstrSpec (mov_r64_r64_effect_step 0x10f1a7 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f1aa [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10f1aa) (movR64R64Effect 0x10f1aa 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f1aa 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10f1aa 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f1ad [0x48, 0xC7, 0xC2, 0x40, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x10f1ad) (movR64Imm32Effect 0x10f1ad 2 0x202240)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10f1ad 2 0x202240).toInstrSpec (mov_r64_imm32_effect_step 0x10f1ad 0x48 0xc2 (by decide) (by decide) (by decide) 0x202240) pre_rip
  have f4 : InstrSpec 0x10f1b4 [0xE8, 0x37, 0xC7, 0x00, 0x00] (PushPre 0x10f1b4 5) (callEffect (fun _ => 0x11b8f0) 0x10f1b9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f1b4 0x11b8f0 0x10f1b9).toInstrSpec (call_rel32_effect_step 0x10f1b4 0xc737 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1a7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1aa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1ad) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1b4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10f1a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f1a2 :=
  Rest.liftedBlock (rest_l10f1a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f1a2 x hx)

theorem rest_l10f1b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f1b9 bytes_l10f1b9) (entryMap (live .l10f1b9))
      5 0x10f1b9 bytes_l10f1b9 b_l10f1b9 := by
  have f0 : InstrSpec 0x10f1b9 [0x4C, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f1b9) (leaR64Effect 0x10f1b9 15 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10f1b9 15 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x10f1b9 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f1c1 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10f1c1) (movR64R64Effect 0x10f1c1 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f1c1 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10f1c1 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f1c4 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10f1c4) (movR64R64Effect 0x10f1c4 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f1c4 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10f1c4 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f1c7 [0x48, 0xC7, 0xC2, 0x60, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x10f1c7) (movR64Imm32Effect 0x10f1c7 2 0x202260)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10f1c7 2 0x202260).toInstrSpec (mov_r64_imm32_effect_step 0x10f1c7 0x48 0xc2 (by decide) (by decide) (by decide) 0x202260) pre_rip
  have f4 : InstrSpec 0x10f1ce [0xE8, 0xED, 0xA7, 0xFF, 0xFF] (PushPre 0x10f1ce 5) (callEffect (fun _ => 0x1099c0) 0x10f1d3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f1ce 0x1099c0 0x10f1d3).toInstrSpec (call_rel32_effect_step 0x10f1ce 0xffffa7ed (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1c7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1ce) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10f1b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f1b9 :=
  Rest.liftedBlock (rest_l10f1b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f1b9 x hx)

theorem rest_l10f1d3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f1d3 bytes_l10f1d3) (entryMap (live .l10f1d3))
      6 0x10f1d3 bytes_l10f1d3 b_l10f1d3 := by
  have f0 : InstrSpec 0x10f1d3 [0x4C, 0x8D, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f1d3) (leaR64Effect 0x10f1d3 13 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10f1d3 13 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x10f1d3 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f1db [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x10f1db) (movR64R64Effect 0x10f1db 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f1db 7 13).toInstrSpec (mov_r64_r64_effect_step 0x10f1db 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f1de [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x10f1de) (movR64R64Effect 0x10f1de 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f1de 6 5).toInstrSpec (mov_r64_r64_effect_step 0x10f1de 0x48 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f1e1 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x10f1e1) (movR64R64Effect 0x10f1e1 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10f1e1 2 15).toInstrSpec (mov_r64_r64_effect_step 0x10f1e1 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10f1e4 [0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10f1e4) (movR64Imm32Effect 0x10f1e4 1 0x2021a0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x10f1e4 1 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x10f1e4 0x48 0xc1 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f5 : InstrSpec 0x10f1eb [0xE8, 0xC0, 0x17, 0x00, 0x00] (PushPre 0x10f1eb 5) (callEffect (fun _ => 0x1109b0) 0x10f1f0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f1eb 0x1109b0 0x10f1f0).toInstrSpec (call_rel32_effect_step 0x10f1eb 0x17c0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1de) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1e1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1e4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1eb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b0) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l10f1d3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f1d3 :=
  Rest.liftedBlock (rest_l10f1d3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f1d3 x hx)

theorem rest_l10f1f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f1f0 bytes_l10f1f0) (entryMap (live .l10f1f0))
      5 0x10f1f0 bytes_l10f1f0 b_l10f1f0 := by
  have f0 : InstrSpec 0x10f1f0 [0x4C, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f1f0) (leaR64Effect 0x10f1f0 15 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10f1f0 15 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x10f1f0 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f1f8 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10f1f8) (movR64R64Effect 0x10f1f8 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f1f8 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10f1f8 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f1fb [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10f1fb) (movR64R64Effect 0x10f1fb 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f1fb 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10f1fb 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f1fe [0x48, 0xC7, 0xC2, 0x80, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x10f1fe) (movR64Imm32Effect 0x10f1fe 2 0x202280)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10f1fe 2 0x202280).toInstrSpec (mov_r64_imm32_effect_step 0x10f1fe 0x48 0xc2 (by decide) (by decide) (by decide) 0x202280) pre_rip
  have f4 : InstrSpec 0x10f205 [0xE8, 0xB6, 0xA7, 0xFF, 0xFF] (PushPre 0x10f205 5) (callEffect (fun _ => 0x1099c0) 0x10f20a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f205 0x1099c0 0x10f20a).toInstrSpec (call_rel32_effect_step 0x10f205 0xffffa7b6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1fb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f1fe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f205) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10f1f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f1f0 :=
  Rest.liftedBlock (rest_l10f1f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f1f0 x hx)

theorem rest_l10f20a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f20a bytes_l10f20a) (entryMap (live .l10f20a))
      5 0x10f20a bytes_l10f20a b_l10f20a := by
  have f0 : InstrSpec 0x10f20a [0x48, 0x8D, 0x7C, 0x24, 0x38] (fun s => s.RIP = 0x10f20a) (leaR64Effect 0x10f20a 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f20a 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f20a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f20f [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10f20f) (movR64R64Effect 0x10f20f 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f20f 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10f20f 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f212 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x10f212) (movR64R64Effect 0x10f212 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10f212 2 15).toInstrSpec (mov_r64_r64_effect_step 0x10f212 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f215 [0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10f215) (movR64Imm32Effect 0x10f215 1 0x2021a0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x10f215 1 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x10f215 0x48 0xc1 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f4 : InstrSpec 0x10f21c [0xE8, 0x8F, 0x17, 0x00, 0x00] (PushPre 0x10f21c 5) (callEffect (fun _ => 0x1109b0) 0x10f221)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f21c 0x1109b0 0x10f221).toInstrSpec (call_rel32_effect_step 0x10f21c 0x178f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f20f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f212) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f215) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f21c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10f20a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f20a :=
  Rest.liftedBlock (rest_l10f20a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f20a x hx)

theorem rest_l10f221_2 [Bindings] (code : CodeMap) :
    Rest (n := 122) code lifted (codeRange 0x10f221 bytes_l10f221) [(1, 111), (2, 120), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x10f2e2 bytes_l10f221_2 b_l10f221_2 := by
  have f40 : InstrSpec 0x10f2e2 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x10f2e2) (shrR64Effect 0x10f2e2 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f2e2 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x10f2e2 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10f2e6 [0x48, 0x89, 0x54, 0x24, 0x38] (StorePre 0x10f2e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f2e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f2e6 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f2e6 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f2e6 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x10f2eb [0x31, 0xC9] (fun s => s.RIP = 0x10f2eb) (xorR32R32Effect 0x10f2eb 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10f2eb 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x10f2eb 0xc9 (by decide)) pre_rip
  have f43 : InstrSpec 0x10f2ed [0x48, 0x2B, 0x4C, 0x24, 0x38] (LoadPre 0x10f2ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f2ed + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f2ed 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f2ed 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x10f2ed 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x10f2f2 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x10f2f2) (sarR64Effect 0x10f2f2 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x10f2f2 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x10f2f2 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10f2f6 [0x48, 0x29, 0xF1] (fun s => s.RIP = 0x10f2f6) (subR64R64Effect 0x10f2f6 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10f2f6 1 6).toInstrSpec (sub_r64_r64_effect_step 0x10f2f6 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10f2f9 [0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x10f2f9) (movR64Imm64Effect 0x10f2f9 2 0x7fffffffffffffff)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10f2f9 2 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10f2f9 0x48 0xba (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f47 : InstrSpec 0x10f303 [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x10f303) (addR64R64Effect 0x10f303 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f303 1 2).toInstrSpec (add_r64_r64_effect_step 0x10f303 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10f306 [0x48, 0x89, 0x74, 0x24, 0x20] (StorePre 0x10f306 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10f306 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f306 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f306 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10f306 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x10f30b [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x10f30b) (orR64R64Effect 0x10f30b 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10f30b 1 6).toInstrSpec (or_r64_r64_effect_step 0x10f30b 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10f30e [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x10f30e) (shrR64Effect 0x10f30e 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f30e 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x10f30e 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10f312 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x10f312 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f312 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f312 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f312 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f312 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x10f317 [0x0F, 0xB6, 0x44, 0x24, 0x38] (LoadPre 0x10f317 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f317 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10f317 5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10f317 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m8_effect_step 0x10f317 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x10f31c [0x24, 0x01] (fun s => s.RIP = 0x10f31c) (andAlImm8Effect 0x10f31c 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10f31c 0x1).toInstrSpec (and_al_imm8_effect_step 0x10f31c 0x1) pre_rip
  have f54 : InstrSpec 0x10f31e [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x10f31e) (movzxR32R8Effect 0x10f31e 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x10f31e 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x10f31e 0xf8 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10f321 [0xE8, 0x2A, 0x8A, 0x01, 0x00] (PushPre 0x10f321 5) (callEffect (fun _ => 0x127d50) 0x10f326)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f321 0x127d50 0x10f326).toInstrSpec (call_rel32_effect_step 0x10f321 0x18a2a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(1, 111), (2, 122), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2e6) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.exec (n := 124) (ρ' := [(1, 111), (2, 122), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2eb) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(1, 125), (2, 122), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2ed) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(1, 127), (2, 122), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2f2) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f44 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(1, 129), (2, 122), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2f6) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(1, 131), (2, 122), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2f9) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f46 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(1, 131), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f303) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(1, 135), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f306) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(1, 135), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f30b) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f49 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(1, 138), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f30e) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f50 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(1, 140), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f312) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(1, 140), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f317) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 143), (1, 140), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f31c) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 145), (1, 140), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f31e) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 145), (1, 140), (2, 133), (3, 3), (4, 4), (5, 57), (6, 72), (7, 147), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f321) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f55 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 145), (1, 140), (2, 133), (3, 3), (4, 149), (5, 57), (6, 72), (7, 147), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f55 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 151) (by decide) (by decide) rfl rfl

theorem rest_l10f221_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x10f221 bytes_l10f221) [(0, 83), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      36 0x10f292 bytes_l10f221_1 b_l10f221_1 := by
  have f20 : InstrSpec 0x10f292 [0x48, 0x8D, 0x44, 0x24, 0x38] (fun s => s.RIP = 0x10f292) (leaR64Effect 0x10f292 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10f292 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f292 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10f297 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x10f297) (xorR32R32Effect 0x10f297 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10f297 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x10f297 0x45 0xff (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10f29a [0x31, 0xC9] (fun s => s.RIP = 0x10f29a) (xorR32R32Effect 0x10f29a 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10f29a 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x10f29a 0xc9 (by decide)) pre_rip
  have f23 : InstrSpec 0x10f29c [0x48, 0x2B, 0x4C, 0x24, 0x38] (LoadPre 0x10f29c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f29c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f29c 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f29c 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x10f29c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10f2a1 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x10f2a1) (sarR64Effect 0x10f2a1 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x10f2a1 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x10f2a1 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10f2a5 [0x48, 0x29, 0xD1] (fun s => s.RIP = 0x10f2a5) (subR64R64Effect 0x10f2a5 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10f2a5 1 2).toInstrSpec (sub_r64_r64_effect_step 0x10f2a5 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10f2a8 [0x49, 0xB8, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57, 0x5D] (fun s => s.RIP = 0x10f2a8) (movR64Imm64Effect 0x10f2a8 8 0x5d576e7357a4501d)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x10f2a8 8 0x5d576e7357a4501d).toInstrSpec (mov_r64_imm64_effect_step 0x10f2a8 0x49 0xb8 (by decide) (by decide) 0x5d576e7357a4501d) pre_rip
  have f27 : InstrSpec 0x10f2b2 [0x4C, 0x01, 0xC1] (fun s => s.RIP = 0x10f2b2) (addR64R64Effect 0x10f2b2 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f2b2 1 8).toInstrSpec (add_r64_r64_effect_step 0x10f2b2 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10f2b5 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x10f2b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10f2b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f2b5 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f2b5 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10f2b5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x10f2ba [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x10f2ba) (orR64R64Effect 0x10f2ba 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10f2ba 1 2).toInstrSpec (or_r64_r64_effect_step 0x10f2ba 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10f2bd [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x10f2bd) (shrR64Effect 0x10f2bd 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f2bd 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x10f2bd 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10f2c1 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x10f2c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f2c1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f2c1 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f2c1 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f2c1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x10f2c6 [0x31, 0xC9] (fun s => s.RIP = 0x10f2c6) (xorR32R32Effect 0x10f2c6 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10f2c6 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x10f2c6 0xc9 (by decide)) pre_rip
  have f33 : InstrSpec 0x10f2c8 [0x48, 0x2B, 0x4C, 0x24, 0x38] (LoadPre 0x10f2c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f2c8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f2c8 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f2c8 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x10f2c8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x10f2cd [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x10f2cd) (sarR64Effect 0x10f2cd 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x10f2cd 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x10f2cd 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10f2d1 [0x48, 0x89, 0xFA] (fun s => s.RIP = 0x10f2d1) (movR64R64Effect 0x10f2d1 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10f2d1 2 7).toInstrSpec (mov_r64_r64_effect_step 0x10f2d1 0x48 0xfa (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10f2d4 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x10f2d4) (notR64Effect 0x10f2d4 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x10f2d4 2).toInstrSpec (not_r64_effect_step 0x10f2d4 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10f2d7 [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x10f2d7) (addR64R64Effect 0x10f2d7 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f2d7 2 1).toInstrSpec (add_r64_r64_effect_step 0x10f2d7 0x48 0xca (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x10f2da [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x10f2da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10f2da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f2da 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f2da 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10f2da 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x10f2df [0x48, 0x21, 0xFA] (fun s => s.RIP = 0x10f2df) (andR64R64Effect 0x10f2df 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f2df 2 7).toInstrSpec (and_r64_r64_effect_step 0x10f2df 0x48 0xfa (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f297) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f29a) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 89), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f29c) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 91), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2a1) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 93), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2a5) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 95), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2a8) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 95), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2b2) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 99), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2b5) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(1, 99), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2ba) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(1, 102), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2bd) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(1, 104), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2c1) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(1, 104), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2c6) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(1, 107), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2c8) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(1, 109), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2cd) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(1, 111), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2d1) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(1, 111), (2, 113), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2d4) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(1, 111), (2, 115), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2d7) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(1, 111), (2, 117), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2da) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(1, 111), (2, 117), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2df) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f39 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(1, 111), (2, 120), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f2e2) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10f221_2 code

theorem rest_l10f221 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f221 bytes_l10f221) (entryMap (live .l10f221))
      56 0x10f221 bytes_l10f221 b_l10f221 := by
  have f0 : InstrSpec 0x10f221 [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x10f221 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10f221 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f221 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f221 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x10f221 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10f229 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x10f229 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10f229 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f229 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f229 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x10f229 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10f231 [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x10f231 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10f231 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f231 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f231 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10f231 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10f236 [0x48, 0x8B, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x10f236 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10f236 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f236 5 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10f236 5 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x10f236 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10f23e [0x48, 0x89, 0x6C, 0x24, 0x68] (StorePre 0x10f23e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10f23e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f23e 5 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f23e 5 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x10f23e 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10f243 [0x4C, 0x8B, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x10f243 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10f243 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f243 14 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10f243 14 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x10f243 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10f24b [0x4C, 0x8B, 0xA4, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x10f24b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10f24b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f24b 12 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10f24b 12 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x10f24b 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10f253 [0x4C, 0x89, 0x64, 0x24, 0x60] (StorePre 0x10f253 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10f253 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f253 12 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f253 12 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10f253 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10f258 [0x4C, 0x89, 0x74, 0x24, 0x58] (StorePre 0x10f258 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10f258 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f258 14 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f258 14 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10f258 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10f25d [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x10f25d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f25d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f25d 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10f25d 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10f25d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10f262 [0x48, 0x8B, 0x54, 0x24, 0x40] (LoadPre 0x10f262 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10f262 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f262 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10f262 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10f262 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10f267 [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x10f267 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10f267 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f267 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10f267 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10f267 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10f26c [0x48, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x10f26c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10f26c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f26c 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10f26c 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10f26c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10f271 [0x49, 0xBD, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF] (fun s => s.RIP = 0x10f271) (movR64Imm64Effect 0x10f271 13 0xdfe92f46681b20a0)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x10f271 13 0xdfe92f46681b20a0).toInstrSpec (mov_r64_imm64_effect_step 0x10f271 0x49 0xbd (by decide) (by decide) 0xdfe92f46681b20a0) pre_rip
  have f14 : InstrSpec 0x10f27b [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10f27b) (movR64R64Effect 0x10f27b 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10f27b 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10f27b 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10f27e [0x48, 0x29, 0xC8] (fun s => s.RIP = 0x10f27e) (subR64R64Effect 0x10f27e 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10f27e 0 1).toInstrSpec (sub_r64_r64_effect_step 0x10f27e 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10f281 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x10f281 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10f281 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f281 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f281 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10f281 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10f286 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10f286) (andR64R64Effect 0x10f286 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f286 0 1).toInstrSpec (and_r64_r64_effect_step 0x10f286 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10f289 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x10f289) (shrR64Effect 0x10f289 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f289 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x10f289 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10f28d [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x10f28d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f28d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f28d 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f28d 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f28d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f229) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f231) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f236) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f23e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f243) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f24b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 62), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f253) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 62), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f258) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 62), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f25d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 66), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 62), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f262) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 62), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f267) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f26c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f271) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f27b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f27e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f281) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f286) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f289) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f28d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 83), (1, 66), (2, 68), (3, 3), (4, 4), (5, 57), (6, 72), (7, 70), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f292) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10f221_1 code

theorem block_l10f221 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f221 :=
  Rest.liftedBlock (rest_l10f221 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f221 x hx)

theorem rest_l10f326_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x10f326 bytes_l10f326) [(0, 0), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x10f37c bytes_l10f326_1 b_l10f326_1 := by
  have f20 : InstrSpec 0x10f37c [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x10f37c) (movR64R64Effect 0x10f37c 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10f37c 0 5).toInstrSpec (mov_r64_r64_effect_step 0x10f37c 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10f37f [0x48, 0xF7, 0xD0] (fun s => s.RIP = 0x10f37f) (notR64Effect 0x10f37f 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR64Effect_footprint 0x10f37f 0).toInstrSpec (not_r64_effect_step 0x10f37f 0x48 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10f382 [0x48, 0x01, 0xD0] (fun s => s.RIP = 0x10f382) (addR64R64Effect 0x10f382 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f382 0 2).toInstrSpec (add_r64_r64_effect_step 0x10f382 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10f385 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x10f385) (andR64R64Effect 0x10f385 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f385 0 5).toInstrSpec (and_r64_r64_effect_step 0x10f385 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x10f388 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x10f388) (shrR64Effect 0x10f388 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f388 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x10f388 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10f38c [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x10f38c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f38c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f38c 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f38c 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f38c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x10f391 [0x4C, 0x2B, 0x7C, 0x24, 0x38] (LoadPre 0x10f391 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f391 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f391 15 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f391 15 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x10f391 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x10f396 [0x49, 0xC1, 0xFF, 0x3F] (fun s => s.RIP = 0x10f396) (sarR64Effect 0x10f396 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (sarR64Effect_footprint 0x10f396 4 15 63).toInstrSpec (sar_r64_imm8_effect_step 0x10f396 0x49 0xff 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10f39a [0x4D, 0x29, 0xEF] (fun s => s.RIP = 0x10f39a) (subR64R64Effect 0x10f39a 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10f39a 15 13).toInstrSpec (sub_r64_r64_effect_step 0x10f39a 0x4d 0xef (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10f39d [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x10f39d) (movR64Imm64Effect 0x10f39d 0 0x7fffffffffffffff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10f39d 0 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10f39d 0x48 0xb8 (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f30 : InstrSpec 0x10f3a7 [0x49, 0x01, 0xC7] (fun s => s.RIP = 0x10f3a7) (addR64R64Effect 0x10f3a7 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f3a7 15 0).toInstrSpec (add_r64_r64_effect_step 0x10f3a7 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10f3aa [0x4D, 0x09, 0xEF] (fun s => s.RIP = 0x10f3aa) (orR64R64Effect 0x10f3aa 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10f3aa 15 13).toInstrSpec (or_r64_r64_effect_step 0x10f3aa 0x4d 0xef (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10f3ad [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x10f3ad) (shrR64Effect 0x10f3ad 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f3ad 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x10f3ad 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10f3b1 [0x4C, 0x89, 0x7C, 0x24, 0x38] (StorePre 0x10f3b1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f3b1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3b1 15 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f3b1 15 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f3b1 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x10f3b6 [0x0F, 0xB6, 0x44, 0x24, 0x38] (LoadPre 0x10f3b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f3b6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10f3b6 5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10f3b6 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m8_effect_step 0x10f3b6 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x10f3bb [0x24, 0x01] (fun s => s.RIP = 0x10f3bb) (andAlImm8Effect 0x10f3bb 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10f3bb 0x1).toInstrSpec (and_al_imm8_effect_step 0x10f3bb 0x1) pre_rip
  have f36 : InstrSpec 0x10f3bd [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x10f3bd) (movzxR32R8Effect 0x10f3bd 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x10f3bd 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x10f3bd 0xf8 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10f3c0 [0xE8, 0x8B, 0x89, 0x01, 0x00] (PushPre 0x10f3c0 5) (callEffect (fun _ => 0x127d50) 0x10f3c5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f3c0 0x127d50 0x10f3c5).toInstrSpec (call_rel32_effect_step 0x10f3c0 0x1898b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f37f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f382) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 94), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f385) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 96), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f388) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 98), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f38c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 98), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f391) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 98), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f396) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 98), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f39a) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f28 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 98), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f39d) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 107), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3a7) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 107), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3aa) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 107), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3ad) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 107), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3b1) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 107), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3b6) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 116), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3bb) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 118), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3bd) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f36 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 118), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (7, 120), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3c0) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f37 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 118), (1, 63), (2, 88), (3, 3), (4, 122), (5, 5), (6, 73), (7, 120), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f37 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 124) (by decide) (by decide) rfl rfl

theorem rest_l10f326 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f326 bytes_l10f326) (entryMap (live .l10f326))
      38 0x10f326 bytes_l10f326 b_l10f326 := by
  have f0 : InstrSpec 0x10f326 [0x4D, 0x29, 0xF5] (fun s => s.RIP = 0x10f326) (subR64R64Effect 0x10f326 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10f326 13 14).toInstrSpec (sub_r64_r64_effect_step 0x10f326 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f329 [0x4C, 0x89, 0x74, 0x24, 0x30] (StorePre 0x10f329 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10f329 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f329 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f329 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10f329 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10f32e [0x4D, 0x21, 0xF5] (fun s => s.RIP = 0x10f32e) (andR64R64Effect 0x10f32e 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f32e 13 14).toInstrSpec (and_r64_r64_effect_step 0x10f32e 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f331 [0x49, 0xC1, 0xED, 0x3F] (fun s => s.RIP = 0x10f331) (shrR64Effect 0x10f331 4 13 63)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f331 4 13 63).toInstrSpec (shr_r64_imm8_effect_step 0x10f331 0x49 0xed 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10f335 [0x4C, 0x89, 0x6C, 0x24, 0x38] (StorePre 0x10f335 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f335 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f335 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f335 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f335 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10f33a [0x4C, 0x8B, 0xAC, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x10f33a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10f33a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f33a 13 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10f33a 13 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x10f33a 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10f342 [0x48, 0x8D, 0x4C, 0x24, 0x38] (fun s => s.RIP = 0x10f342) (leaR64Effect 0x10f342 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x10f342 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f342 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10f347 [0x31, 0xD2] (fun s => s.RIP = 0x10f347) (xorR32R32Effect 0x10f347 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10f347 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x10f347 0xd2 (by decide)) pre_rip
  have f8 : InstrSpec 0x10f349 [0x48, 0x2B, 0x54, 0x24, 0x38] (LoadPre 0x10f349 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f349 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f349 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f349 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x10f349 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10f34e [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x10f34e) (sarR64Effect 0x10f34e 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x10f34e 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x10f34e 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10f352 [0x4C, 0x29, 0xE2] (fun s => s.RIP = 0x10f352) (subR64R64Effect 0x10f352 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10f352 2 12).toInstrSpec (sub_r64_r64_effect_step 0x10f352 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10f355 [0x48, 0xBE, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57, 0x5D] (fun s => s.RIP = 0x10f355) (movR64Imm64Effect 0x10f355 6 0x5d576e7357a4501d)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10f355 6 0x5d576e7357a4501d).toInstrSpec (mov_r64_imm64_effect_step 0x10f355 0x48 0xbe (by decide) (by decide) 0x5d576e7357a4501d) pre_rip
  have f12 : InstrSpec 0x10f35f [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x10f35f) (addR64R64Effect 0x10f35f 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f35f 2 6).toInstrSpec (add_r64_r64_effect_step 0x10f35f 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10f362 [0x4C, 0x09, 0xE2] (fun s => s.RIP = 0x10f362) (orR64R64Effect 0x10f362 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10f362 2 12).toInstrSpec (or_r64_r64_effect_step 0x10f362 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10f365 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x10f365) (shrR64Effect 0x10f365 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f365 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x10f365 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10f369 [0x48, 0x89, 0x54, 0x24, 0x38] (StorePre 0x10f369 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f369 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f369 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f369 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f369 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10f36e [0x31, 0xD2] (fun s => s.RIP = 0x10f36e) (xorR32R32Effect 0x10f36e 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10f36e 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x10f36e 0xd2 (by decide)) pre_rip
  have f17 : InstrSpec 0x10f370 [0x48, 0x2B, 0x54, 0x24, 0x38] (LoadPre 0x10f370 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f370 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f370 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f370 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x10f370 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10f375 [0x41, 0x89, 0xC6] (fun s => s.RIP = 0x10f375) (movR32R32Effect 0x10f375 3 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x10f375 3 14 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x10f375 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10f378 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x10f378) (sarR64Effect 0x10f378 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x10f378 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x10f378 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f329) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f32e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f331) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f335) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f33a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f342) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f347) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f349) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 67), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f34e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 63), (2, 69), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f352) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f355) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f35f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 63), (2, 75), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f362) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 63), (2, 77), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f365) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 63), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f369) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 63), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f36e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 63), (2, 82), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f370) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 63), (2, 84), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f375) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 63), (2, 84), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f378) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 63), (2, 88), (3, 3), (4, 4), (5, 5), (6, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f37c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10f326_1 code

theorem block_l10f326 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f326 :=
  Rest.liftedBlock (rest_l10f326 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f326 x hx)

theorem rest_l10f3c5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f3c5 bytes_l10f3c5) (entryMap (live .l10f3c5))
      3 0x10f3c5 bytes_l10f3c5 b_l10f3c5 := by
  have f0 : InstrSpec 0x10f3c5 [0x41, 0x89, 0xC7] (fun s => s.RIP = 0x10f3c5) (movR32R32Effect 0x10f3c5 3 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x10f3c5 3 15 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x10f3c5 0x41 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f3c8 [0x45, 0x84, 0xF6] (fun s => s.RIP = 0x10f3c8) (testR8R8Effect 0x10f3c8 3 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10f3c8 3 14 14).toInstrSpec (test_r8_r8_rex_effect_step 0x10f3c8 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3c8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3cb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x10f3cb 4 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10f3c5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f3c5 :=
  Rest.liftedBlock (rest_l10f3c5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f3c5 x hx)

theorem rest_l10f3cd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f3cd bytes_l10f3cd) (entryMap (live .l10f3cd))
      12 0x10f3cd bytes_l10f3cd b_l10f3cd := by
  have f0 : InstrSpec 0x10f3cd [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10f3cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10f3cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f3cd 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f3cd 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10f3cd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10f3d2 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x10f3d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f3d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3d2 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f3d2 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f3d2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10f3d7 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10f3d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10f3d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f3d7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f3d7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10f3d7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10f3dc [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x10f3dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10f3dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3dc 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f3dc 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10f3dc 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10f3e1 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10f3e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10f3e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f3e1 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f3e1 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10f3e1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10f3e6 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x10f3e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10f3e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3e6 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f3e6 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10f3e6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10f3eb [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10f3eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10f3eb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f3eb 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f3eb 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10f3eb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10f3f0 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x10f3f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10f3f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3f0 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f3f0 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10f3f0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10f3f5 [0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f3f5) (leaR64Effect 0x10f3f5 7 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f3f5 7 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x10f3f5 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10f3fd [0x48, 0x8D, 0x74, 0x24, 0x38] (fun s => s.RIP = 0x10f3fd) (leaR64Effect 0x10f3fd 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10f3fd 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f3fd 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10f402 [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10f402) (movR64Imm32Effect 0x10f402 2 0x2021a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10f402 2 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x10f402 0x48 0xc2 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f11 : InstrSpec 0x10f409 [0xE8, 0x72, 0x17, 0x00, 0x00] (PushPre 0x10f409 5) (callEffect (fun _ => 0x110b80) 0x10f40e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f409 0x110b80 0x10f40e).toInstrSpec (call_rel32_effect_step 0x10f409 0x1772 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3d7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3dc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3e1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3e6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3eb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3f0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3f5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f3fd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f402) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f409) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b80) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l10f3cd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f3cd :=
  Rest.liftedBlock (rest_l10f3cd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f3cd x hx)

theorem rest_l10f40e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f40e bytes_l10f40e) (entryMap (live .l10f40e))
      3 0x10f40e bytes_l10f40e b_l10f40e := by
  have f0 : InstrSpec 0x10f40e [0x45, 0x84, 0xFF] (fun s => s.RIP = 0x10f40e) (testR8R8Effect 0x10f40e 3 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10f40e 3 15 15).toInstrSpec (test_r8_r8_rex_effect_step 0x10f40e 0x45 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f411 [0x44, 0x88, 0x7C, 0x24, 0x07] (StorePre 0x10f411 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10f411 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10f411 5 15 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10f411 5 15 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10f411 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f411) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f416) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x10f416 4 0x72) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10f40e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f40e :=
  Rest.liftedBlock (rest_l10f40e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f40e x hx)

theorem rest_l10f418 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f418 bytes_l10f418) (entryMap (live .l10f418))
      9 0x10f418 bytes_l10f418 b_l10f418 := by
  have f0 : InstrSpec 0x10f418 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x10f418 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10f418 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f418 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f418 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10f418 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10f41d [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x10f41d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f41d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f41d 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f41d 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10f41d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10f422 [0x4C, 0x89, 0x64, 0x24, 0x40] (StorePre 0x10f422 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10f422 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f422 12 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f422 12 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10f422 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10f427 [0x48, 0x89, 0x6C, 0x24, 0x48] (StorePre 0x10f427 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10f427 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f427 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f427 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10f427 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10f42c [0x4C, 0x89, 0x6C, 0x24, 0x50] (StorePre 0x10f42c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10f42c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f42c 13 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f42c 13 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10f42c 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10f431 [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f431) (leaR64Effect 0x10f431 7 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f431 7 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x10f431 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f439 [0x48, 0x8D, 0x74, 0x24, 0x38] (fun s => s.RIP = 0x10f439) (leaR64Effect 0x10f439 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10f439 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f439 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10f43e [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10f43e) (movR64Imm32Effect 0x10f43e 2 0x2021a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10f43e 2 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x10f43e 0x48 0xc2 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f8 : InstrSpec 0x10f445 [0xE8, 0x36, 0x17, 0x00, 0x00] (PushPre 0x10f445 5) (callEffect (fun _ => 0x110b80) 0x10f44a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f445 0x110b80 0x10f44a).toInstrSpec (call_rel32_effect_step 0x10f445 0x1736 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f41d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f422) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f427) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f42c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f431) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f439) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f43e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (2, 63), (3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f445) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (2, 63), (3, 3), (4, 65), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b80) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l10f418 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f418 :=
  Rest.liftedBlock (rest_l10f418 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f418 x hx)

theorem rest_l10f44a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f44a bytes_l10f44a) (entryMap (live .l10f44a))
      1 0x10f44a bytes_l10f44a b_l10f44a := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x10f44a 0x63 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10f44a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f44a :=
  Rest.liftedBlock (rest_l10f44a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f44a x hx)

theorem rest_l10f44c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f44c bytes_l10f44c) (entryMap (live .l10f44c))
      11 0x10f44c bytes_l10f44c b_l10f44c := by
  have f0 : InstrSpec 0x10f44c [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10f44c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10f44c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f44c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f44c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10f44c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10f451 [0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x10f451 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10f451 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f451 0 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f451 0 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x10f451 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10f459 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10f459 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10f459 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f459 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f459 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10f459 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10f45e [0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x10f45e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10f45e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f45e 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f45e 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x10f45e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10f466 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10f466 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10f466 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f466 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f466 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10f466 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10f46b [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x10f46b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10f46b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f46b 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f46b 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x10f46b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10f473 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10f473 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10f473 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f473 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f473 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10f473 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10f478 [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x10f478 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10f478 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f478 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f478 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x10f478 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10f480 [0x45, 0x84, 0xFF] (fun s => s.RIP = 0x10f480) (testR8R8Effect 0x10f480 3 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10f480 3 15 15).toInstrSpec (test_r8_r8_rex_effect_step 0x10f480 0x45 0xff (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10f483 [0x44, 0x88, 0x7C, 0x24, 0x07] (StorePre 0x10f483 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10f483 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10f483 5 15 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10f483 5 15 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10f483 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f451) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f459) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f45e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f466) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f46b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f473) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f478) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f480) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f483) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f488) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x10f488 5 0x8e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10f44c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f44c :=
  Rest.liftedBlock (rest_l10f44c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f44c x hx)

theorem rest_l10f48a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f48a bytes_l10f48a) (entryMap (live .l10f48a))
      5 0x10f48a bytes_l10f48a b_l10f48a := by
  have f0 : InstrSpec 0x10f48a [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x10f48a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10f48a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f48a 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f48a 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10f48a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10f48f [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x10f48f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10f48f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f48f 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f48f 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x10f48f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10f497 [0x4C, 0x89, 0xA4, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x10f497 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10f497 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f497 12 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f497 12 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x10f497 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10f49f [0x48, 0x89, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x10f49f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10f49f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f49f 5 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f49f 5 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x10f49f 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10f4a7 [0x4C, 0x89, 0xAC, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x10f4a7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10f4a7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f4a7 13 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f4a7 13 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x10f4a7 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f48f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f497) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f49f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4a7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4af) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l10f48a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f48a :=
  Rest.liftedBlock (rest_l10f48a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f48a x hx)

theorem rest_l10f4af [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f4af bytes_l10f4af) (entryMap (live .l10f4af))
      4 0x10f4af bytes_l10f4af b_l10f4af := by
  have f0 : InstrSpec 0x10f4af [0x4C, 0x8D, 0x7C, 0x24, 0x38] (fun s => s.RIP = 0x10f4af) (leaR64Effect 0x10f4af 15 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10f4af 15 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f4af 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f4b4 [0x48, 0x8D, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f4b4) (leaR64Effect 0x10f4b4 6 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10f4b4 6 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x10f4b4 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f4bc [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10f4bc) (movR64R64Effect 0x10f4bc 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f4bc 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10f4bc 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f4bf [0xE8, 0x2C, 0xAE, 0xFF, 0xFF] (PushPre 0x10f4bf 5) (callEffect (fun _ => 0x10a2f0) 0x10f4c4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f4bf 0x10a2f0 0x10f4c4).toInstrSpec (call_rel32_effect_step 0x10f4bf 0xffffae2c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4bc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4bf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2f0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10f4af [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f4af :=
  Rest.liftedBlock (rest_l10f4af code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f4af x hx)

theorem rest_l10f4c4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f4c4 bytes_l10f4c4) (entryMap (live .l10f4c4))
      8 0x10f4c4 bytes_l10f4c4 b_l10f4c4 := by
  have f0 : InstrSpec 0x10f4c4 [0x48, 0x8B, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x10f4c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10f4c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f4c4 5 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10f4c4 5 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x10f4c4 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10f4cc [0x48, 0x8D, 0x7D, 0x08] (fun s => s.RIP = 0x10f4cc) (leaR64Effect 0x10f4cc 7 (.base 5 (.d8 0x8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f4cc 7 (.base 5 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10f4cc 0x48 (by decide) 7 (.base 5 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f4d0 [0xBE, 0x01, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f4d0) (movR32Imm32Effect 0x10f4d0 5 6 0x101)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10f4d0 5 6 0x101).toInstrSpec (mov_r32_imm32_effect_step 0x10f4d0 0xbe (by decide) 0x101) pre_rip
  have f3 : InstrSpec 0x10f4d5 [0xB9, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f4d5) (movR32Imm32Effect 0x10f4d5 5 1 0x10)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f4d5 5 1 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x10f4d5 0xb9 (by decide) 0x10) pre_rip
  have f4 : InstrSpec 0x10f4da [0x41, 0xB8, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f4da) (movR32Imm32Effect 0x10f4da 6 8 0x80)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x10f4da 6 8 0x80).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10f4da 0x41 0xb8 (by decide) (by decide) 0x80) pre_rip
  have f5 : InstrSpec 0x10f4e0 [0x41, 0xB9, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f4e0) (movR32Imm32Effect 0x10f4e0 6 9 0x5)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x10f4e0 6 9 0x5).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10f4e0 0x41 0xb9 (by decide) (by decide) 0x5) pre_rip
  have f6 : InstrSpec 0x10f4e6 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x10f4e6) (movR64R64Effect 0x10f4e6 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10f4e6 2 15).toInstrSpec (mov_r64_r64_effect_step 0x10f4e6 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10f4e9 [0xE8, 0xC2, 0x12, 0x00, 0x00] (PushPre 0x10f4e9 5) (callEffect (fun _ => 0x1107b0) 0x10f4ee)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f4e9 0x1107b0 0x10f4ee).toInstrSpec (call_rel32_effect_step 0x10f4e9 0x12c2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4cc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4d0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4d5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4da) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4e0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 59), (3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (8, 61), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4e6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 59), (2, 65), (3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (8, 61), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4e9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 59), (2, 65), (3, 3), (4, 67), (5, 53), (6, 57), (7, 55), (8, 61), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107b0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l10f4c4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f4c4 :=
  Rest.liftedBlock (rest_l10f4c4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f4c4 x hx)

theorem rest_l10f4ee [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f4ee bytes_l10f4ee) (entryMap (live .l10f4ee))
      5 0x10f4ee bytes_l10f4ee b_l10f4ee := by
  have f0 : InstrSpec 0x10f4ee [0x48, 0x89, 0x45, 0x00] (StorePre 0x10f4ee 4 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x10f4ee + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10f4ee 0 (.base 5 (.d8 0x0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f4ee 0 (.base 5 (.d8 0x0))).toInstrSpec (mov_m64_r64_effect_step 0x10f4ee 0x48 (by decide) 0 (.base 5 (.d8 0x0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10f4f2 [0x4C, 0x8D, 0x7C, 0x24, 0x38] (fun s => s.RIP = 0x10f4f2) (leaR64Effect 0x10f4f2 15 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10f4f2 15 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f4f2 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f4f7 [0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f4f7) (leaR64Effect 0x10f4f7 6 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10f4f7 6 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x10f4f7 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f4ff [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10f4ff) (movR64R64Effect 0x10f4ff 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f4ff 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10f4ff 0x4c 0xff (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10f502 [0xE8, 0xE9, 0xAD, 0xFF, 0xFF] (PushPre 0x10f502 5) (callEffect (fun _ => 0x10a2f0) 0x10f507)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f502 0x10a2f0 0x10f507).toInstrSpec (call_rel32_effect_step 0x10f502 0xffffade9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4f2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4f7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f4ff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 56), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f502) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (3, 3), (4, 60), (5, 5), (6, 56), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2f0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l10f4ee [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f4ee :=
  Rest.liftedBlock (rest_l10f4ee code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f4ee x hx)

theorem rest_l10f507 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f507 bytes_l10f507) (entryMap (live .l10f507))
      7 0x10f507 bytes_l10f507 b_l10f507 := by
  have f0 : InstrSpec 0x10f507 [0x48, 0x8D, 0xBD, 0x18, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f507) (leaR64Effect 0x10f507 7 (.base 5 (.d32 0x118)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f507 7 (.base 5 (.d32 0x118))).toInstrSpec (lea_r64_effect_step 0x10f507 0x48 (by decide) 7 (.base 5 (.d32 0x118)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f50e [0xBE, 0x01, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f50e) (movR32Imm32Effect 0x10f50e 5 6 0x101)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10f50e 5 6 0x101).toInstrSpec (mov_r32_imm32_effect_step 0x10f50e 0xbe (by decide) 0x101) pre_rip
  have f2 : InstrSpec 0x10f513 [0xB9, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f513) (movR32Imm32Effect 0x10f513 5 1 0x10)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f513 5 1 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x10f513 0xb9 (by decide) 0x10) pre_rip
  have f3 : InstrSpec 0x10f518 [0x41, 0xB8, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f518) (movR32Imm32Effect 0x10f518 6 8 0x80)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x10f518 6 8 0x80).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10f518 0x41 0xb8 (by decide) (by decide) 0x80) pre_rip
  have f4 : InstrSpec 0x10f51e [0x41, 0xB9, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f51e) (movR32Imm32Effect 0x10f51e 6 9 0x5)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x10f51e 6 9 0x5).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10f51e 0x41 0xb9 (by decide) (by decide) 0x5) pre_rip
  have f5 : InstrSpec 0x10f524 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x10f524) (movR64R64Effect 0x10f524 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10f524 2 15).toInstrSpec (mov_r64_r64_effect_step 0x10f524 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f527 [0xE8, 0x84, 0x12, 0x00, 0x00] (PushPre 0x10f527 5) (callEffect (fun _ => 0x1107b0) 0x10f52c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f527 0x1107b0 0x10f52c).toInstrSpec (call_rel32_effect_step 0x10f527 0x1284 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f50e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f513) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f518) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 59), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f51e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 59), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f524) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 59), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f527) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 57), (2, 63), (3, 3), (4, 65), (5, 5), (6, 55), (7, 53), (8, 59), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107b0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l10f507 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f507 :=
  Rest.liftedBlock (rest_l10f507 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f507 x hx)

theorem rest_l10f52c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f52c bytes_l10f52c) (entryMap (live .l10f52c))
      9 0x10f52c bytes_l10f52c b_l10f52c := by
  have f0 : InstrSpec 0x10f52c [0x49, 0xBD, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x10f52c) (movR64Imm64Effect 0x10f52c 13 0x3ffffffffffffc)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x10f52c 13 0x3ffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x10f52c 0x49 0xbd (by decide) (by decide) 0x3ffffffffffffc) pre_rip
  have f1 : InstrSpec 0x10f536 [0x48, 0xB9, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x10f536) (movR64Imm64Effect 0x10f536 1 0x3ffffbfffff0bc)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10f536 1 0x3ffffbfffff0bc).toInstrSpec (mov_r64_imm64_effect_step 0x10f536 0x48 0xb9 (by decide) (by decide) 0x3ffffbfffff0bc) pre_rip
  have f2 : InstrSpec 0x10f540 [0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10f540) (movR64Imm64Effect 0x10f540 15 0xfffffffffffff)
      [] [] [.reg 15, .rip] :=
    (movR64Imm64Effect_footprint 0x10f540 15 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10f540 0x49 0xbf (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f3 : InstrSpec 0x10f54a [0x49, 0xBC, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00] (fun s => s.RIP = 0x10f54a) (movR64Imm64Effect 0x10f54a 12 0x3fffffffffffc)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x10f54a 12 0x3fffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x10f54a 0x49 0xbc (by decide) (by decide) 0x3fffffffffffc) pre_rip
  have f4 : InstrSpec 0x10f554 [0x49, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x10f554) (movR64Imm64Effect 0x10f554 11 0xffffffffffff)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x10f554 11 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10f554 0x49 0xbb (by decide) (by decide) 0xffffffffffff) pre_rip
  have f5 : InstrSpec 0x10f55e [0x48, 0x89, 0x85, 0x10, 0x01, 0x00, 0x00] (StorePre 0x10f55e 7 (fun s => AddrMode.addr (.base 5 (.d32 0x110)) s (0x10f55e + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x10f55e 0 (.base 5 (.d32 0x110)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f55e 0 (.base 5 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x10f55e 0x48 (by decide) 0 (.base 5 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10f565 [0x48, 0xBE, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f565) (movR64Imm64Effect 0x10f565 6 0x1000003d1)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10f565 6 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x10f565 0x48 0xbe (by decide) (by decide) 0x1000003d1) pre_rip
  have f7 : InstrSpec 0x10f56f [0x45, 0x84, 0xF6] (fun s => s.RIP = 0x10f56f) (testR8R8Effect 0x10f56f 3 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10f56f 3 14 14).toInstrSpec (test_r8_r8_rex_effect_step 0x10f56f 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f536) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f540) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (13, 53), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f54a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (12, 59), (13, 53), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f554) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (11, 61), (12, 59), (13, 53), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f55e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (11, 61), (12, 59), (13, 53), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f565) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 64), (11, 61), (12, 59), (13, 53), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f56f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 64), (11, 61), (12, 59), (13, 53), (14, 14), (15, 57), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f572) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel32_effect_step 0x10f572 4 0x108) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10f52c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f52c :=
  Rest.liftedBlock (rest_l10f52c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f52c x hx)

theorem rest_l10f578_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x10f578 bytes_l10f578) [(0, 112), (1, 114), (2, 110), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x10f61b bytes_l10f578_2 b_l10f578_2 := by
  have f40 : InstrSpec 0x10f61b [0x49, 0x8B, 0x12] (LoadPre 0x10f61b (fun s => AddrMode.addr (.base 10 .none) s (0x10f61b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10f61b 2 (.base 10 .none))
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10f61b 2 (.base 10 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10f61b 0x49 (by decide) 2 (.base 10 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10f61e [0x4D, 0x8B, 0x4A, 0x08] (LoadPre 0x10f61e (fun s => AddrMode.addr (.base 10 (.d8 0x8)) s (0x10f61e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f61e 9 (.base 10 (.d8 0x8)))
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10f61e 9 (.base 10 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10f61e 0x4d (by decide) 1 (.base 10 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x10f622 [0x48, 0x89, 0x94, 0x24, 0x78, 0x01, 0x00, 0x00] (StorePre 0x10f622 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10f622 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f622 2 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f622 2 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_m64_r64_effect_step 0x10f622 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x10f62a [0x4C, 0x89, 0x8C, 0x24, 0x80, 0x01, 0x00, 0x00] (StorePre 0x10f62a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10f62a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f62a 9 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f62a 9 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_m64_r64_effect_step 0x10f62a 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x10f632 [0x49, 0x8B, 0x52, 0x10] (LoadPre 0x10f632 (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x10f632 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f632 2 (.base 10 (.d8 0x10)))
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10f632 2 (.base 10 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10f632 0x49 (by decide) 2 (.base 10 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x10f636 [0x48, 0x89, 0x94, 0x24, 0x88, 0x01, 0x00, 0x00] (StorePre 0x10f636 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10f636 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f636 2 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f636 2 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_m64_r64_effect_step 0x10f636 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x10f63e [0x49, 0x8B, 0x52, 0x18] (LoadPre 0x10f63e (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x10f63e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f63e 2 (.base 10 (.d8 0x18)))
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10f63e 2 (.base 10 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10f63e 0x49 (by decide) 2 (.base 10 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x10f642 [0x48, 0x89, 0x94, 0x24, 0x90, 0x01, 0x00, 0x00] (StorePre 0x10f642 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10f642 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f642 2 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f642 2 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (mov_m64_r64_effect_step 0x10f642 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x10f64a [0x49, 0x8B, 0x52, 0x20] (LoadPre 0x10f64a (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x10f64a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f64a 2 (.base 10 (.d8 0x20)))
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10f64a 2 (.base 10 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10f64a 0x49 (by decide) 2 (.base 10 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x10f64e [0x48, 0x89, 0x94, 0x24, 0x98, 0x01, 0x00, 0x00] (StorePre 0x10f64e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10f64e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f64e 2 (.sib 4 none 0 (.d32 0x198)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f64e 2 (.sib 4 none 0 (.d32 0x198))).toInstrSpec (mov_m64_r64_effect_step 0x10f64e 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x10f656 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x01, 0x00, 0x00] (StorePre 0x10f656 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10f656 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f656 0 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f656 0 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_m64_r64_effect_step 0x10f656 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x10f65e [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x01, 0x00, 0x00] (StorePre 0x10f65e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x10f65e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f65e 1 (.sib 4 none 0 (.d32 0x1a8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f65e 1 (.sib 4 none 0 (.d32 0x1a8))).toInstrSpec (mov_m64_r64_effect_step 0x10f65e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1a8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x10f666 [0x48, 0x89, 0xB4, 0x24, 0xB0, 0x01, 0x00, 0x00] (StorePre 0x10f666 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x10f666 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f666 6 (.sib 4 none 0 (.d32 0x1b0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f666 6 (.sib 4 none 0 (.d32 0x1b0))).toInstrSpec (mov_m64_r64_effect_step 0x10f666 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1b0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x10f66e [0x48, 0x89, 0xBC, 0x24, 0xB8, 0x01, 0x00, 0x00] (StorePre 0x10f66e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x10f66e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f66e 7 (.sib 4 none 0 (.d32 0x1b8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f66e 7 (.sib 4 none 0 (.d32 0x1b8))).toInstrSpec (mov_m64_r64_effect_step 0x10f66e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1b8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x10f676 [0x4C, 0x89, 0x84, 0x24, 0xC0, 0x01, 0x00, 0x00] (StorePre 0x10f676 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x10f676 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f676 8 (.sib 4 none 0 (.d32 0x1c0)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f676 8 (.sib 4 none 0 (.d32 0x1c0))).toInstrSpec (mov_m64_r64_effect_step 0x10f676 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x1c0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 112), (1, 114), (2, 128), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f61e) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 112), (1, 114), (2, 128), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f622) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.exec (n := 132) (ρ' := [(0, 112), (1, 114), (2, 128), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f62a) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 112), (1, 114), (2, 128), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f632) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 112), (1, 114), (2, 134), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f636) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 112), (1, 114), (2, 134), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f63e) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f46 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 112), (1, 114), (2, 137), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f642) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 112), (1, 114), (2, 137), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f64a) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 112), (1, 114), (2, 140), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f64e) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 112), (1, 114), (2, 140), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f656) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 112), (1, 114), (2, 140), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f65e) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 112), (1, 114), (2, 140), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f666) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 112), (1, 114), (2, 140), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f66e) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 112), (1, 114), (2, 140), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f676) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 112), (1, 114), (2, 140), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f67e) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 148) (jmp_rel8_effect_step 0x10f67e 0x1e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l10f578_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10f578 bytes_l10f578) [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 91), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      36 0x10f5c0 bytes_l10f578_1 b_l10f578_1 := by
  have f20 : InstrSpec 0x10f5c0 [0x49, 0x2B, 0x7A, 0x40] (LoadPre 0x10f5c0 (fun s => AddrMode.addr (.base 10 (.d8 0x40)) s (0x10f5c0 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f5c0 7 (.base 10 (.d8 0x40)))
      [.gpr 7, .gpr 10] [] [.reg 7, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f5c0 7 (.base 10 (.d8 0x40))).toInstrSpec (sub_r64_m64_effect_step 0x10f5c0 0x49 (by decide) 7 (.base 10 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10f5c4 [0x4C, 0x89, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x10f5c4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x10f5c4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5c4 8 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f5c4 8 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (mov_m64_r64_effect_step 0x10f5c4 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10f5cc [0x4D, 0x8B, 0x42, 0x68] (LoadPre 0x10f5cc (fun s => AddrMode.addr (.base 10 (.d8 0x68)) s (0x10f5cc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5cc 8 (.base 10 (.d8 0x68)))
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10f5cc 8 (.base 10 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10f5cc 0x4d (by decide) 0 (.base 10 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x10f5d0 [0x4C, 0x89, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00] (StorePre 0x10f5d0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x10f5d0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5d0 8 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f5d0 8 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_m64_r64_effect_step 0x10f5d0 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10f5d8 [0x4D, 0x8B, 0x42, 0x60] (LoadPre 0x10f5d8 (fun s => AddrMode.addr (.base 10 (.d8 0x60)) s (0x10f5d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5d8 8 (.base 10 (.d8 0x60)))
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10f5d8 8 (.base 10 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10f5d8 0x4d (by decide) 0 (.base 10 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x10f5dc [0x4C, 0x89, 0x84, 0x24, 0xD8, 0x01, 0x00, 0x00] (StorePre 0x10f5dc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x10f5dc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5dc 8 (.sib 4 none 0 (.d32 0x1d8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f5dc 8 (.sib 4 none 0 (.d32 0x1d8))).toInstrSpec (mov_m64_r64_effect_step 0x10f5dc 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x10f5e4 [0x4D, 0x8B, 0x42, 0x50] (LoadPre 0x10f5e4 (fun s => AddrMode.addr (.base 10 (.d8 0x50)) s (0x10f5e4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5e4 8 (.base 10 (.d8 0x50)))
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10f5e4 8 (.base 10 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10f5e4 0x4d (by decide) 0 (.base 10 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x10f5e8 [0x4D, 0x8B, 0x4A, 0x58] (LoadPre 0x10f5e8 (fun s => AddrMode.addr (.base 10 (.d8 0x58)) s (0x10f5e8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5e8 9 (.base 10 (.d8 0x58)))
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10f5e8 9 (.base 10 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10f5e8 0x4d (by decide) 1 (.base 10 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x10f5ec [0x4C, 0x89, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x10f5ec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x10f5ec + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5ec 9 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f5ec 9 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x10f5ec 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x10f5f4 [0x4C, 0x89, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00] (StorePre 0x10f5f4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x10f5f4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5f4 8 (.sib 4 none 0 (.d32 0x1c8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f5f4 8 (.sib 4 none 0 (.d32 0x1c8))).toInstrSpec (mov_m64_r64_effect_step 0x10f5f4 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x1c8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x10f5fc [0x4D, 0x89, 0xDE] (fun s => s.RIP = 0x10f5fc) (movR64R64Effect 0x10f5fc 14 11)
      [.gpr 11] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10f5fc 14 11).toInstrSpec (mov_r64_r64_effect_step 0x10f5fc 0x4d 0xde (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10f5ff [0x4C, 0x21, 0xDA] (fun s => s.RIP = 0x10f5ff) (andR64R64Effect 0x10f5ff 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f5ff 2 11).toInstrSpec (and_r64_r64_effect_step 0x10f5ff 0x4c 0xda (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10f602 [0x4C, 0x21, 0xF8] (fun s => s.RIP = 0x10f602) (andR64R64Effect 0x10f602 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f602 0 15).toInstrSpec (and_r64_r64_effect_step 0x10f602 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10f605 [0x4C, 0x21, 0xF9] (fun s => s.RIP = 0x10f605) (andR64R64Effect 0x10f605 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f605 1 15).toInstrSpec (and_r64_r64_effect_step 0x10f605 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10f608 [0x4C, 0x01, 0xEF] (fun s => s.RIP = 0x10f608) (addR64R64Effect 0x10f608 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f608 7 13).toInstrSpec (add_r64_r64_effect_step 0x10f608 0x4c 0xef (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10f60b [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x10f60b) (andR64R64Effect 0x10f60b 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f60b 6 15).toInstrSpec (and_r64_r64_effect_step 0x10f60b 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10f60e [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x10f60e) (movR64R64Effect 0x10f60e 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10f60e 8 7).toInstrSpec (mov_r64_r64_effect_step 0x10f60e 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10f611 [0x49, 0xC1, 0xE8, 0x34] (fun s => s.RIP = 0x10f611) (shrR64Effect 0x10f611 4 8 52)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f611 4 8 52).toInstrSpec (shr_r64_imm8_effect_step 0x10f611 0x49 0xe8 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x10f615 [0x49, 0x01, 0xD0] (fun s => s.RIP = 0x10f615) (addR64R64Effect 0x10f615 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f615 8 2).toInstrSpec (add_r64_r64_effect_step 0x10f615 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10f618 [0x4C, 0x21, 0xFF] (fun s => s.RIP = 0x10f618) (andR64R64Effect 0x10f618 7 15)
      [.gpr 7, .gpr 15] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f618 7 15).toInstrSpec (and_r64_r64_effect_step 0x10f618 0x4c 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5c4) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5cc) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 96), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5d0) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 96), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5d8) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 99), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5dc) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 99), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5e4) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 102), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5e8) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5ec) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5f4) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5fc) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f30 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5ff) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 69), (1, 79), (2, 110), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f602) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f32 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 112), (1, 79), (2, 110), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f605) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 112), (1, 114), (2, 110), (3, 3), (4, 4), (5, 63), (6, 87), (7, 93), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f608) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f34 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 112), (1, 114), (2, 110), (3, 3), (4, 4), (5, 63), (6, 87), (7, 116), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f60b) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f35 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 112), (1, 114), (2, 110), (3, 3), (4, 4), (5, 63), (6, 118), (7, 116), (8, 102), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f60e) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f36 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 112), (1, 114), (2, 110), (3, 3), (4, 4), (5, 63), (6, 118), (7, 116), (8, 120), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f611) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f37 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 112), (1, 114), (2, 110), (3, 3), (4, 4), (5, 63), (6, 118), (7, 116), (8, 122), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f615) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f38 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 112), (1, 114), (2, 110), (3, 3), (4, 4), (5, 63), (6, 118), (7, 116), (8, 124), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f618) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 112), (1, 114), (2, 110), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 104), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f61b) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10f578_2 code

theorem rest_l10f578 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f578 bytes_l10f578) (entryMap (live .l10f578))
      56 0x10f578 bytes_l10f578 b_l10f578 := by
  have f0 : InstrSpec 0x10f578 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x10f578) (movR64R64Effect 0x10f578 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10f578 2 12).toInstrSpec (mov_r64_r64_effect_step 0x10f578 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f57b [0x4C, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x10f57b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10f57b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f57b 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10f57b 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10f57b 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10f580 [0x49, 0x2B, 0x52, 0x48] (LoadPre 0x10f580 (fun s => AddrMode.addr (.base 10 (.d8 0x48)) s (0x10f580 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f580 2 (.base 10 (.d8 0x48)))
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f580 2 (.base 10 (.d8 0x48))).toInstrSpec (sub_r64_m64_effect_step 0x10f580 0x49 (by decide) 2 (.base 10 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10f584 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x10f584) (movR64R64Effect 0x10f584 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10f584 0 2).toInstrSpec (mov_r64_r64_effect_step 0x10f584 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10f587 [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x10f587) (shrR64Effect 0x10f587 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f587 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x10f587 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f58b [0x48, 0x89, 0xF5] (fun s => s.RIP = 0x10f58b) (movR64R64Effect 0x10f58b 5 6)
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10f58b 5 6).toInstrSpec (mov_r64_r64_effect_step 0x10f58b 0x48 0xf5 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f58e [0x48, 0x0F, 0xAF, 0xC6] (fun s => s.RIP = 0x10f58e) (imulR64R64Effect 0x10f58e 4 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10f58e 4 0 6).toInstrSpec (imul_r64_r64_effect_step 0x10f58e 0x48 (by decide) 0xc6 (by decide)) pre_rip
  have f7 : InstrSpec 0x10f592 [0x49, 0x2B, 0x42, 0x28] (LoadPre 0x10f592 (fun s => AddrMode.addr (.base 10 (.d8 0x28)) s (0x10f592 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f592 0 (.base 10 (.d8 0x28)))
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f592 0 (.base 10 (.d8 0x28))).toInstrSpec (sub_r64_m64_effect_step 0x10f592 0x49 (by decide) 0 (.base 10 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10f596 [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x10f596) (addR64R64Effect 0x10f596 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f596 0 1).toInstrSpec (add_r64_r64_effect_step 0x10f596 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10f599 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10f599) (movR64R64Effect 0x10f599 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10f599 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10f599 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10f59c [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x10f59c) (shrR64Effect 0x10f59c 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f59c 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x10f59c 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10f5a0 [0x49, 0x2B, 0x4A, 0x30] (LoadPre 0x10f5a0 (fun s => AddrMode.addr (.base 10 (.d8 0x30)) s (0x10f5a0 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f5a0 1 (.base 10 (.d8 0x30)))
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f5a0 1 (.base 10 (.d8 0x30))).toInstrSpec (sub_r64_m64_effect_step 0x10f5a0 0x49 (by decide) 1 (.base 10 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10f5a4 [0x4D, 0x8B, 0x42, 0x70] (LoadPre 0x10f5a4 (fun s => AddrMode.addr (.base 10 (.d8 0x70)) s (0x10f5a4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5a4 8 (.base 10 (.d8 0x70)))
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10f5a4 8 (.base 10 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10f5a4 0x4d (by decide) 0 (.base 10 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10f5a8 [0x4C, 0x01, 0xE9] (fun s => s.RIP = 0x10f5a8) (addR64R64Effect 0x10f5a8 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f5a8 1 13).toInstrSpec (add_r64_r64_effect_step 0x10f5a8 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10f5ab [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x10f5ab) (movR64R64Effect 0x10f5ab 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f5ab 6 1).toInstrSpec (mov_r64_r64_effect_step 0x10f5ab 0x48 0xce (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10f5ae [0x48, 0xC1, 0xEE, 0x34] (fun s => s.RIP = 0x10f5ae) (shrR64Effect 0x10f5ae 4 6 52)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f5ae 4 6 52).toInstrSpec (shr_r64_imm8_effect_step 0x10f5ae 0x48 0xee 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10f5b2 [0x49, 0x2B, 0x72, 0x38] (LoadPre 0x10f5b2 (fun s => AddrMode.addr (.base 10 (.d8 0x38)) s (0x10f5b2 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f5b2 6 (.base 10 (.d8 0x38)))
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f5b2 6 (.base 10 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x10f5b2 0x49 (by decide) 6 (.base 10 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10f5b6 [0x4C, 0x01, 0xEE] (fun s => s.RIP = 0x10f5b6) (addR64R64Effect 0x10f5b6 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f5b6 6 13).toInstrSpec (add_r64_r64_effect_step 0x10f5b6 0x4c 0xee (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10f5b9 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x10f5b9) (movR64R64Effect 0x10f5b9 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f5b9 7 6).toInstrSpec (mov_r64_r64_effect_step 0x10f5b9 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10f5bc [0x48, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x10f5bc) (shrR64Effect 0x10f5bc 4 7 52)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f5bc 4 7 52).toInstrSpec (shr_r64_imm8_effect_step 0x10f5bc 0x48 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f57b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f580) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f584) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 57), (3, 3), (4, 4), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f587) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 57), (3, 3), (4, 4), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f58b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f58e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f592) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f596) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f599) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 71), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f59c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 73), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5a0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 75), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5a4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 75), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5a8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5ab) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 81), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5ae) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 83), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5b2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 85), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5b6) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5b9) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 89), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5bc) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 69), (1, 79), (2, 57), (3, 3), (4, 4), (5, 63), (6, 87), (7, 91), (8, 77), (10, 55), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f5c0) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10f578_1 code

theorem block_l10f578 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f578 :=
  Rest.liftedBlock (rest_l10f578 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f578 x hx)

theorem rest_l10f680 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f680 bytes_l10f680) (entryMap (live .l10f680))
      7 0x10f680 bytes_l10f680 b_l10f680 := by
  have f0 : InstrSpec 0x10f680 [0x48, 0x89, 0xF5] (fun s => s.RIP = 0x10f680) (movR64R64Effect 0x10f680 5 6)
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10f680 5 6).toInstrSpec (mov_r64_r64_effect_step 0x10f680 0x48 0xf5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f683 [0x4D, 0x89, 0xDE] (fun s => s.RIP = 0x10f683) (movR64R64Effect 0x10f683 14 11)
      [.gpr 11] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10f683 14 11).toInstrSpec (mov_r64_r64_effect_step 0x10f683 0x4d 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f686 [0x48, 0x8D, 0xBC, 0x24, 0x78, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f686) (leaR64Effect 0x10f686 7 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f686 7 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (lea_r64_effect_step 0x10f686 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f68e [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f68e) (movR32Imm32Effect 0x10f68e 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f68e 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f68e 0xb9 (by decide) 0xf) pre_rip
  have f4 : InstrSpec 0x10f693 [0x4C, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x10f693 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10f693 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f693 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10f693 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10f693 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10f698 [0x4C, 0x89, 0xD6] (fun s => s.RIP = 0x10f698) (movR64R64Effect 0x10f698 6 10)
      [.gpr 10] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f698 6 10).toInstrSpec (mov_r64_r64_effect_step 0x10f698 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f69b [0xF3, 0x48, 0xA5] (RepPre 0x10f69b (RepMovsqPre 0x10f69b)) (repMovsqEffect 0x10f69b)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f69b).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f69b 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (6, 6), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f683) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 53), (6, 6), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f686) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 53), (6, 6), (7, 57), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f68e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (3, 3), (4, 4), (5, 53), (6, 6), (7, 57), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f693) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (3, 3), (4, 4), (5, 53), (6, 6), (7, 57), (10, 61), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f698) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 59), (3, 3), (4, 4), (5, 53), (6, 63), (7, 57), (10, 61), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f69b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 4), (5, 53), (10, 61), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f69e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l10f680 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f680 :=
  Rest.liftedBlock (rest_l10f680 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f680 x hx)

theorem rest_l10f69e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f69e bytes_l10f69e) (entryMap (live .l10f69e))
      3 0x10f69e bytes_l10f69e b_l10f69e := by
  have f0 : InstrSpec 0x10f69e [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f69e) (leaR64Effect 0x10f69e 7 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f69e 7 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x10f69e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f6a6 [0x4C, 0x89, 0xD6] (fun s => s.RIP = 0x10f6a6) (movR64R64Effect 0x10f6a6 6 10)
      [.gpr 10] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f6a6 6 10).toInstrSpec (mov_r64_r64_effect_step 0x10f6a6 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f6a9 [0xE8, 0x62, 0xE9, 0xFF, 0xFF] (PushPre 0x10f6a9 5) (callEffect (fun _ => 0x10e010) 0x10f6ae)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f6a9 0x10e010 0x10f6ae).toInstrSpec (call_rel32_effect_step 0x10f6a9 0xffffe962 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6a6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e010) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10f69e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f69e :=
  Rest.liftedBlock (rest_l10f69e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f69e x hx)

theorem rest_l10f6ae [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f6ae bytes_l10f6ae) (entryMap (live .l10f6ae))
      2 0x10f6ae bytes_l10f6ae b_l10f6ae := by
  have f0 : InstrSpec 0x10f6ae [0x80, 0x7C, 0x24, 0x07, 0x00] (LoadPre 0x10f6ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10f6ae + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x10f6ae 5 (.sib 4 none 0 (.d8 0x7)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10f6ae 5 (.sib 4 none 0 (.d8 0x7)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x10f6ae (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6b3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10f6b3 4 0x141) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10f6ae [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f6ae :=
  Rest.liftedBlock (rest_l10f6ae code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f6ae x hx)

theorem rest_l10f6b9_2 [Bindings] (code : CodeMap) :
    Rest (n := 123) code lifted (codeRange 0x10f6b9 bytes_l10f6b9) [(0, 107), (1, 105), (2, 115), (3, 3), (4, 4), (5, 5), (6, 121), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x10f7ba bytes_l10f6b9_2 b_l10f6b9_2 := by
  have f40 : InstrSpec 0x10f7ba [0x4C, 0x21, 0xF9] (fun s => s.RIP = 0x10f7ba) (andR64R64Effect 0x10f7ba 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f7ba 1 15).toInstrSpec (and_r64_r64_effect_step 0x10f7ba 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10f7bd [0x4C, 0x01, 0xEE] (fun s => s.RIP = 0x10f7bd) (addR64R64Effect 0x10f7bd 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f7bd 6 13).toInstrSpec (add_r64_r64_effect_step 0x10f7bd 0x4c 0xee (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x10f7c0 [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x10f7c0) (andR64R64Effect 0x10f7c0 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f7c0 2 15).toInstrSpec (and_r64_r64_effect_step 0x10f7c0 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x10f7c3 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x10f7c3) (movR64R64Effect 0x10f7c3 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f7c3 7 6).toInstrSpec (mov_r64_r64_effect_step 0x10f7c3 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x10f7c6 [0x48, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x10f7c6) (shrR64Effect 0x10f7c6 4 7 52)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f7c6 4 7 52).toInstrSpec (shr_r64_imm8_effect_step 0x10f7c6 0x48 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10f7ca [0x4C, 0x01, 0xE7] (fun s => s.RIP = 0x10f7ca) (addR64R64Effect 0x10f7ca 7 12)
      [.gpr 7, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f7ca 7 12).toInstrSpec (add_r64_r64_effect_step 0x10f7ca 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10f7cd [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x10f7cd) (andR64R64Effect 0x10f7cd 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f7cd 6 15).toInstrSpec (and_r64_r64_effect_step 0x10f7cd 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10f7d0 [0x48, 0x89, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00] (StorePre 0x10f7d0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x10f7d0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7d0 0 (.sib 4 none 0 (.d32 0x218)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f7d0 0 (.sib 4 none 0 (.d32 0x218))).toInstrSpec (mov_m64_r64_effect_step 0x10f7d0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x218)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x10f7d8 [0x48, 0x89, 0x8C, 0x24, 0x20, 0x02, 0x00, 0x00] (StorePre 0x10f7d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x10f7d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7d8 1 (.sib 4 none 0 (.d32 0x220)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f7d8 1 (.sib 4 none 0 (.d32 0x220))).toInstrSpec (mov_m64_r64_effect_step 0x10f7d8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x220)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x10f7e0 [0x48, 0x89, 0x94, 0x24, 0x28, 0x02, 0x00, 0x00] (StorePre 0x10f7e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x10f7e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7e0 2 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f7e0 2 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (mov_m64_r64_effect_step 0x10f7e0 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x10f7e8 [0x48, 0x89, 0xB4, 0x24, 0x30, 0x02, 0x00, 0x00] (StorePre 0x10f7e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x230)) s (0x10f7e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7e8 6 (.sib 4 none 0 (.d32 0x230)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f7e8 6 (.sib 4 none 0 (.d32 0x230))).toInstrSpec (mov_m64_r64_effect_step 0x10f7e8 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x230)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x10f7f0 [0x48, 0x89, 0xBC, 0x24, 0x38, 0x02, 0x00, 0x00] (StorePre 0x10f7f0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x238)) s (0x10f7f0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7f0 7 (.sib 4 none 0 (.d32 0x238)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f7f0 7 (.sib 4 none 0 (.d32 0x238))).toInstrSpec (mov_m64_r64_effect_step 0x10f7f0 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x238)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 107), (1, 123), (2, 115), (3, 3), (4, 4), (5, 5), (6, 121), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7bd) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f41 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 107), (1, 123), (2, 115), (3, 3), (4, 4), (5, 5), (6, 125), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7c0) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 125), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7c3) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f43 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 125), (7, 129), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7c6) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f44 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 125), (7, 131), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7ca) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f45 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 125), (7, 133), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7cd) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 135), (7, 133), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7d0) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 135), (7, 133), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7d8) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 135), (7, 133), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7e0) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 135), (7, 133), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7e8) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 135), (7, 133), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7f0) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 135), (7, 133), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7f8) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 142) (jmp_rel8_effect_step 0x10f7f8 0x18 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l10f6b9_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x10f6b9 bytes_l10f6b9) [(0, 80), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x10f759 bytes_l10f6b9_1 b_l10f6b9_1 := by
  have f20 : InstrSpec 0x10f759 [0x4C, 0x2B, 0xA4, 0x24, 0x48, 0x01, 0x00, 0x00] (LoadPre 0x10f759 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10f759 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f759 12 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 12, .gpr 4] [] [.reg 12, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f759 12 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (sub_r64_m64_effect_step 0x10f759 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10f761 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x10f761) (movR64R64Effect 0x10f761 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10f761 0 12).toInstrSpec (mov_r64_r64_effect_step 0x10f761 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10f764 [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x10f764) (shrR64Effect 0x10f764 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f764 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x10f764 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10f768 [0x48, 0x0F, 0xAF, 0xC5] (fun s => s.RIP = 0x10f768) (imulR64R64Effect 0x10f768 4 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10f768 4 0 5).toInstrSpec (imul_r64_r64_effect_step 0x10f768 0x48 (by decide) 0xc5 (by decide)) pre_rip
  have f24 : InstrSpec 0x10f76c [0x48, 0x2B, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x10f76c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10f76c + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f76c 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f76c 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (sub_r64_m64_effect_step 0x10f76c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x10f774 [0x48, 0xB9, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x10f774) (movR64Imm64Effect 0x10f774 1 0x3ffffbfffff0bc)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10f774 1 0x3ffffbfffff0bc).toInstrSpec (mov_r64_imm64_effect_step 0x10f774 0x48 0xb9 (by decide) (by decide) 0x3ffffbfffff0bc) pre_rip
  have f26 : InstrSpec 0x10f77e [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x10f77e) (addR64R64Effect 0x10f77e 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f77e 0 1).toInstrSpec (add_r64_r64_effect_step 0x10f77e 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10f781 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10f781) (movR64R64Effect 0x10f781 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10f781 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10f781 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10f784 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x10f784) (shrR64Effect 0x10f784 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f784 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x10f784 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10f788 [0x48, 0x2B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x10f788 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10f788 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f788 1 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f788 1 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (sub_r64_m64_effect_step 0x10f788 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x10f790 [0x4D, 0x21, 0xF4] (fun s => s.RIP = 0x10f790) (andR64R64Effect 0x10f790 12 14)
      [.gpr 12, .gpr 14] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f790 12 14).toInstrSpec (and_r64_r64_effect_step 0x10f790 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10f793 [0x4C, 0x01, 0xE9] (fun s => s.RIP = 0x10f793) (addR64R64Effect 0x10f793 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f793 1 13).toInstrSpec (add_r64_r64_effect_step 0x10f793 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10f796 [0x4C, 0x21, 0xF8] (fun s => s.RIP = 0x10f796) (andR64R64Effect 0x10f796 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10f796 0 15).toInstrSpec (and_r64_r64_effect_step 0x10f796 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10f799 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10f799) (movR64R64Effect 0x10f799 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10f799 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10f799 0x48 0xca (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10f79c [0x48, 0xC1, 0xEA, 0x34] (fun s => s.RIP = 0x10f79c) (shrR64Effect 0x10f79c 4 2 52)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f79c 4 2 52).toInstrSpec (shr_r64_imm8_effect_step 0x10f79c 0x48 0xea 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10f7a0 [0x48, 0x2B, 0x94, 0x24, 0x38, 0x01, 0x00, 0x00] (LoadPre 0x10f7a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10f7a0 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f7a0 2 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f7a0 2 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (sub_r64_m64_effect_step 0x10f7a0 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x10f7a8 [0x4C, 0x01, 0xEA] (fun s => s.RIP = 0x10f7a8) (addR64R64Effect 0x10f7a8 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10f7a8 2 13).toInstrSpec (add_r64_r64_effect_step 0x10f7a8 0x4c 0xea (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10f7ab [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x10f7ab) (movR64R64Effect 0x10f7ab 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f7ab 6 2).toInstrSpec (mov_r64_r64_effect_step 0x10f7ab 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x10f7ae [0x48, 0xC1, 0xEE, 0x34] (fun s => s.RIP = 0x10f7ae) (shrR64Effect 0x10f7ae 4 6 52)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10f7ae 4 6 52).toInstrSpec (shr_r64_imm8_effect_step 0x10f7ae 0x48 0xee 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10f7b2 [0x48, 0x2B, 0xB4, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x10f7b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10f7b2 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f7b2 6 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10f7b2 6 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (sub_r64_m64_effect_step 0x10f7b2 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f20 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 80), (1, 64), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f761) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 64), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f764) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 64), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f768) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 64), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f76c) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 91), (1, 64), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f774) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 91), (1, 93), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f77e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 93), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f781) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 97), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f784) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 99), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f788) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 95), (1, 101), (3, 3), (4, 4), (5, 5), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f790) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f30 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 95), (1, 101), (3, 3), (4, 4), (5, 5), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f793) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 95), (1, 105), (3, 3), (4, 4), (5, 5), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f796) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f32 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 107), (1, 105), (3, 3), (4, 4), (5, 5), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f799) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 107), (1, 105), (2, 109), (3, 3), (4, 4), (5, 5), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f79c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 107), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7a0) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 107), (1, 105), (2, 113), (3, 3), (4, 4), (5, 5), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7a8) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 107), (1, 105), (2, 115), (3, 3), (4, 4), (5, 5), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7ab) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f37 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 107), (1, 105), (2, 115), (3, 3), (4, 4), (5, 5), (6, 117), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7ae) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f38 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 107), (1, 105), (2, 115), (3, 3), (4, 4), (5, 5), (6, 119), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7b2) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f39 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 107), (1, 105), (2, 115), (3, 3), (4, 4), (5, 5), (6, 121), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f7ba) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10f6b9_2 code

theorem rest_l10f6b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f6b9 bytes_l10f6b9) (entryMap (live .l10f6b9))
      53 0x10f6b9 bytes_l10f6b9 b_l10f6b9 := by
  have f0 : InstrSpec 0x10f6b9 [0x48, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (LoadPre 0x10f6b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10f6b9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6b9 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f6b9 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_r64_m64_effect_step 0x10f6b9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10f6c1 [0x48, 0x89, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00] (StorePre 0x10f6c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x10f6c1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f6c1 0 (.sib 4 none 0 (.d32 0x210)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f6c1 0 (.sib 4 none 0 (.d32 0x210))).toInstrSpec (mov_m64_r64_effect_step 0x10f6c1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x210)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10f6c9 [0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (LoadPre 0x10f6c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10f6c9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6c9 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f6c9 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_r64_m64_effect_step 0x10f6c9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10f6d1 [0x48, 0x89, 0x84, 0x24, 0x08, 0x02, 0x00, 0x00] (StorePre 0x10f6d1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x208)) s (0x10f6d1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f6d1 0 (.sib 4 none 0 (.d32 0x208)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f6d1 0 (.sib 4 none 0 (.d32 0x208))).toInstrSpec (mov_m64_r64_effect_step 0x10f6d1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x208)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10f6d9 [0x48, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x10f6d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10f6d9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6d9 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f6d9 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_r64_m64_effect_step 0x10f6d9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10f6e1 [0x48, 0x89, 0x84, 0x24, 0x00, 0x02, 0x00, 0x00] (StorePre 0x10f6e1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x200)) s (0x10f6e1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f6e1 0 (.sib 4 none 0 (.d32 0x200)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f6e1 0 (.sib 4 none 0 (.d32 0x200))).toInstrSpec (mov_m64_r64_effect_step 0x10f6e1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x200)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10f6e9 [0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x10f6e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10f6e9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6e9 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f6e9 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_r64_m64_effect_step 0x10f6e9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10f6f1 [0x48, 0x8B, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00] (LoadPre 0x10f6f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10f6f1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6f1 1 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10f6f1 1 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_r64_m64_effect_step 0x10f6f1 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10f6f9 [0x48, 0x89, 0x8C, 0x24, 0xF8, 0x01, 0x00, 0x00] (StorePre 0x10f6f9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f8)) s (0x10f6f9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f6f9 1 (.sib 4 none 0 (.d32 0x1f8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f6f9 1 (.sib 4 none 0 (.d32 0x1f8))).toInstrSpec (mov_m64_r64_effect_step 0x10f6f9 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1f8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10f701 [0x48, 0x89, 0x84, 0x24, 0xF0, 0x01, 0x00, 0x00] (StorePre 0x10f701 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x10f701 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f701 0 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f701 0 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (mov_m64_r64_effect_step 0x10f701 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10f709 [0x48, 0x8B, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] (LoadPre 0x10f709 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10f709 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f709 0 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f709 0 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_r64_m64_effect_step 0x10f709 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10f711 [0x48, 0x89, 0x84, 0x24, 0x40, 0x02, 0x00, 0x00] (StorePre 0x10f711 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x240)) s (0x10f711 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f711 0 (.sib 4 none 0 (.d32 0x240)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f711 0 (.sib 4 none 0 (.d32 0x240))).toInstrSpec (mov_m64_r64_effect_step 0x10f711 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x240)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10f719 [0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x10f719 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10f719 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f719 0 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f719 0 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_r64_m64_effect_step 0x10f719 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10f721 [0x48, 0x89, 0x84, 0x24, 0x48, 0x02, 0x00, 0x00] (StorePre 0x10f721 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x10f721 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f721 0 (.sib 4 none 0 (.d32 0x248)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f721 0 (.sib 4 none 0 (.d32 0x248))).toInstrSpec (mov_m64_r64_effect_step 0x10f721 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x248)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10f729 [0x48, 0x8B, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (LoadPre 0x10f729 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10f729 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f729 0 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f729 0 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_r64_m64_effect_step 0x10f729 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10f731 [0x48, 0x89, 0x84, 0x24, 0x50, 0x02, 0x00, 0x00] (StorePre 0x10f731 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x10f731 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f731 0 (.sib 4 none 0 (.d32 0x250)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f731 0 (.sib 4 none 0 (.d32 0x250))).toInstrSpec (mov_m64_r64_effect_step 0x10f731 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x250)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10f739 [0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00] (LoadPre 0x10f739 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10f739 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f739 0 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f739 0 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_r64_m64_effect_step 0x10f739 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10f741 [0x48, 0x89, 0x84, 0x24, 0x58, 0x02, 0x00, 0x00] (StorePre 0x10f741 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x258)) s (0x10f741 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f741 0 (.sib 4 none 0 (.d32 0x258)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f741 0 (.sib 4 none 0 (.d32 0x258))).toInstrSpec (mov_m64_r64_effect_step 0x10f741 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x258)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10f749 [0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (LoadPre 0x10f749 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10f749 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f749 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10f749 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_r64_m64_effect_step 0x10f749 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10f751 [0x48, 0x89, 0x84, 0x24, 0x60, 0x02, 0x00, 0x00] (StorePre 0x10f751 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x10f751 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f751 0 (.sib 4 none 0 (.d32 0x260)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10f751 0 (.sib 4 none 0 (.d32 0x260))).toInstrSpec (mov_m64_r64_effect_step 0x10f751 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x260)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6c9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6d1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6d9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6e1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6e9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6f1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f6f9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f701) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f709) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f711) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f719) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f721) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f729) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f731) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f739) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f741) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f749) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f751) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f759) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10f6b9_1 code

theorem block_l10f6b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f6b9 :=
  Rest.liftedBlock (rest_l10f6b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f6b9 x hx)

theorem rest_l10f7fa [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f7fa bytes_l10f7fa) (entryMap (live .l10f7fa))
      4 0x10f7fa bytes_l10f7fa b_l10f7fa := by
  have f0 : InstrSpec 0x10f7fa [0x48, 0x8D, 0xBC, 0x24, 0xF0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f7fa) (leaR64Effect 0x10f7fa 7 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f7fa 7 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (lea_r64_effect_step 0x10f7fa 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f802 [0x48, 0x8D, 0xB4, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f802) (leaR64Effect 0x10f802 6 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10f802 6 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x10f802 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f80a [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f80a) (movR32Imm32Effect 0x10f80a 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f80a 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f80a 0xb9 (by decide) 0xf) pre_rip
  have f3 : InstrSpec 0x10f80f [0xF3, 0x48, 0xA5] (RepPre 0x10f80f (RepMovsqPre 0x10f80f)) (repMovsqEffect 0x10f80f)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f80f).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f80f 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f802) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f80a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f80f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f812) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l10f7fa [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f7fa :=
  Rest.liftedBlock (rest_l10f7fa hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f7fa x hx)

theorem rest_l10f812 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f812 bytes_l10f812) (entryMap (live .l10f812))
      5 0x10f812 bytes_l10f812 b_l10f812 := by
  have f0 : InstrSpec 0x10f812 [0x4C, 0x8D, 0x7C, 0x24, 0x38] (fun s => s.RIP = 0x10f812) (leaR64Effect 0x10f812 15 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10f812 15 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f812 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f817 [0x4C, 0x8D, 0xB4, 0x24, 0x78, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f817) (leaR64Effect 0x10f817 14 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10f817 14 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (lea_r64_effect_step 0x10f817 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f81f [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10f81f) (movR64R64Effect 0x10f81f 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f81f 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10f81f 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f822 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f822) (movR64R64Effect 0x10f822 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f822 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f822 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10f825 [0xE8, 0xA6, 0x14, 0x00, 0x00] (PushPre 0x10f825 5) (callEffect (fun _ => 0x110cd0) 0x10f82a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f825 0x110cd0 0x10f82a).toInstrSpec (call_rel32_effect_step 0x10f825 0x14a6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f817) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 55), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f81f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 55), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f822) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 55), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f825) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 55), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cd0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10f812 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f812 :=
  Rest.liftedBlock (rest_l10f812 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f812 x hx)

theorem rest_l10f82a [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f82a bytes_l10f82a) (entryMap (live .l10f82a))
      7 0x10f82a bytes_l10f82a b_l10f82a := by
  have f0 : InstrSpec 0x10f82a [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f82a) (movR32Imm32Effect 0x10f82a 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f82a 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f82a 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x10f82f [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10f82f) (movR64R64Effect 0x10f82f 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f82f 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10f82f 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f832 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f832) (movR64R64Effect 0x10f832 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f832 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f832 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f835 [0xF3, 0x48, 0xA5] (RepPre 0x10f835 (RepMovsqPre 0x10f835)) (repMovsqEffect 0x10f835)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f835).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f835 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f838 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f838) (movR64R64Effect 0x10f838 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f838 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f838 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f83b [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f83b) (movR64R64Effect 0x10f83b 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f83b 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f83b 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f83e [0xE8, 0xCD, 0xAB, 0xFF, 0xFF] (PushPre 0x10f83e 5) (callEffect (fun _ => 0x10a410) 0x10f843)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f83e 0x10a410 0x10f843).toInstrSpec (call_rel32_effect_step 0x10f83e 0xffffabcd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f82f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f832) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f835) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f838) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f83b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f83e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f82a [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f82a :=
  Rest.liftedBlock (rest_l10f82a hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f82a x hx)

theorem rest_l10f843 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f843 bytes_l10f843) (entryMap (live .l10f843))
      7 0x10f843 bytes_l10f843 b_l10f843 := by
  have f0 : InstrSpec 0x10f843 [0x48, 0x8D, 0x7B, 0x78] (fun s => s.RIP = 0x10f843) (leaR64Effect 0x10f843 7 (.base 3 (.d8 0x78)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f843 7 (.base 3 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x10f843 0x48 (by decide) 7 (.base 3 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f847 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f847) (movR32Imm32Effect 0x10f847 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f847 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f847 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f84c [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f84c) (movR64R64Effect 0x10f84c 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f84c 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f84c 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f84f [0xF3, 0x48, 0xA5] (RepPre 0x10f84f (RepMovsqPre 0x10f84f)) (repMovsqEffect 0x10f84f)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f84f).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f84f 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f852 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f852) (movR64R64Effect 0x10f852 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f852 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f852 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f855 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f855) (movR64R64Effect 0x10f855 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f855 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f855 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f858 [0xE8, 0xB3, 0xAB, 0xFF, 0xFF] (PushPre 0x10f858 5) (callEffect (fun _ => 0x10a410) 0x10f85d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f858 0x10a410 0x10f85d).toInstrSpec (call_rel32_effect_step 0x10f858 0xffffabb3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f847) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f84c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f84f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f852) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f855) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f858) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f843 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f843 :=
  Rest.liftedBlock (rest_l10f843 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f843 x hx)

theorem rest_l10f85d [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f85d bytes_l10f85d) (entryMap (live .l10f85d))
      7 0x10f85d bytes_l10f85d b_l10f85d := by
  have f0 : InstrSpec 0x10f85d [0x48, 0x8D, 0xBB, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f85d) (leaR64Effect 0x10f85d 7 (.base 3 (.d32 0xf0)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f85d 7 (.base 3 (.d32 0xf0))).toInstrSpec (lea_r64_effect_step 0x10f85d 0x48 (by decide) 7 (.base 3 (.d32 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f864 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f864) (movR32Imm32Effect 0x10f864 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f864 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f864 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f869 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f869) (movR64R64Effect 0x10f869 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f869 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f869 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f86c [0xF3, 0x48, 0xA5] (RepPre 0x10f86c (RepMovsqPre 0x10f86c)) (repMovsqEffect 0x10f86c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f86c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f86c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f86f [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f86f) (movR64R64Effect 0x10f86f 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f86f 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f86f 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f872 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f872) (movR64R64Effect 0x10f872 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f872 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f872 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f875 [0xE8, 0x96, 0xAB, 0xFF, 0xFF] (PushPre 0x10f875 5) (callEffect (fun _ => 0x10a410) 0x10f87a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f875 0x10a410 0x10f87a).toInstrSpec (call_rel32_effect_step 0x10f875 0xffffab96 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f864) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f869) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f86c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f86f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f872) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f875) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f85d [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f85d :=
  Rest.liftedBlock (rest_l10f85d hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f85d x hx)

theorem rest_l10f87a [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f87a bytes_l10f87a) (entryMap (live .l10f87a))
      7 0x10f87a bytes_l10f87a b_l10f87a := by
  have f0 : InstrSpec 0x10f87a [0x48, 0x8D, 0xBB, 0x68, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f87a) (leaR64Effect 0x10f87a 7 (.base 3 (.d32 0x168)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f87a 7 (.base 3 (.d32 0x168))).toInstrSpec (lea_r64_effect_step 0x10f87a 0x48 (by decide) 7 (.base 3 (.d32 0x168)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f881 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f881) (movR32Imm32Effect 0x10f881 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f881 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f881 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f886 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f886) (movR64R64Effect 0x10f886 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f886 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f886 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f889 [0xF3, 0x48, 0xA5] (RepPre 0x10f889 (RepMovsqPre 0x10f889)) (repMovsqEffect 0x10f889)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f889).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f889 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f88c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f88c) (movR64R64Effect 0x10f88c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f88c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f88c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f88f [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f88f) (movR64R64Effect 0x10f88f 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f88f 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f88f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f892 [0xE8, 0x79, 0xAB, 0xFF, 0xFF] (PushPre 0x10f892 5) (callEffect (fun _ => 0x10a410) 0x10f897)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f892 0x10a410 0x10f897).toInstrSpec (call_rel32_effect_step 0x10f892 0xffffab79 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f881) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f886) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f889) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f88c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f88f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f892) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f87a [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f87a :=
  Rest.liftedBlock (rest_l10f87a hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f87a x hx)

theorem rest_l10f897 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f897 bytes_l10f897) (entryMap (live .l10f897))
      7 0x10f897 bytes_l10f897 b_l10f897 := by
  have f0 : InstrSpec 0x10f897 [0x48, 0x8D, 0xBB, 0xE0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f897) (leaR64Effect 0x10f897 7 (.base 3 (.d32 0x1e0)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f897 7 (.base 3 (.d32 0x1e0))).toInstrSpec (lea_r64_effect_step 0x10f897 0x48 (by decide) 7 (.base 3 (.d32 0x1e0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f89e [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f89e) (movR32Imm32Effect 0x10f89e 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f89e 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f89e 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f8a3 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f8a3) (movR64R64Effect 0x10f8a3 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f8a3 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f8a3 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f8a6 [0xF3, 0x48, 0xA5] (RepPre 0x10f8a6 (RepMovsqPre 0x10f8a6)) (repMovsqEffect 0x10f8a6)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f8a6).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f8a6 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f8a9 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f8a9) (movR64R64Effect 0x10f8a9 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f8a9 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f8a9 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f8ac [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f8ac) (movR64R64Effect 0x10f8ac 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f8ac 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f8ac 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f8af [0xE8, 0x5C, 0xAB, 0xFF, 0xFF] (PushPre 0x10f8af 5) (callEffect (fun _ => 0x10a410) 0x10f8b4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f8af 0x10a410 0x10f8b4).toInstrSpec (call_rel32_effect_step 0x10f8af 0xffffab5c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f89e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8a9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8ac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8af) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f897 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f897 :=
  Rest.liftedBlock (rest_l10f897 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f897 x hx)

theorem rest_l10f8b4 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f8b4 bytes_l10f8b4) (entryMap (live .l10f8b4))
      7 0x10f8b4 bytes_l10f8b4 b_l10f8b4 := by
  have f0 : InstrSpec 0x10f8b4 [0x48, 0x8D, 0xBB, 0x58, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10f8b4) (leaR64Effect 0x10f8b4 7 (.base 3 (.d32 0x258)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f8b4 7 (.base 3 (.d32 0x258))).toInstrSpec (lea_r64_effect_step 0x10f8b4 0x48 (by decide) 7 (.base 3 (.d32 0x258)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f8bb [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f8bb) (movR32Imm32Effect 0x10f8bb 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f8bb 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f8bb 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f8c0 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f8c0) (movR64R64Effect 0x10f8c0 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f8c0 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f8c0 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f8c3 [0xF3, 0x48, 0xA5] (RepPre 0x10f8c3 (RepMovsqPre 0x10f8c3)) (repMovsqEffect 0x10f8c3)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f8c3).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f8c3 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f8c6 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f8c6) (movR64R64Effect 0x10f8c6 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f8c6 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f8c6 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f8c9 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f8c9) (movR64R64Effect 0x10f8c9 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f8c9 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f8c9 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f8cc [0xE8, 0x3F, 0xAB, 0xFF, 0xFF] (PushPre 0x10f8cc 5) (callEffect (fun _ => 0x10a410) 0x10f8d1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f8cc 0x10a410 0x10f8d1).toInstrSpec (call_rel32_effect_step 0x10f8cc 0xffffab3f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8bb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8c0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8c6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8cc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f8b4 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f8b4 :=
  Rest.liftedBlock (rest_l10f8b4 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f8b4 x hx)

theorem rest_l10f8d1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f8d1 bytes_l10f8d1) (entryMap (live .l10f8d1))
      7 0x10f8d1 bytes_l10f8d1 b_l10f8d1 := by
  have f0 : InstrSpec 0x10f8d1 [0x48, 0x8D, 0xBB, 0xD0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10f8d1) (leaR64Effect 0x10f8d1 7 (.base 3 (.d32 0x2d0)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f8d1 7 (.base 3 (.d32 0x2d0))).toInstrSpec (lea_r64_effect_step 0x10f8d1 0x48 (by decide) 7 (.base 3 (.d32 0x2d0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f8d8 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f8d8) (movR32Imm32Effect 0x10f8d8 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f8d8 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f8d8 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f8dd [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f8dd) (movR64R64Effect 0x10f8dd 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f8dd 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f8dd 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f8e0 [0xF3, 0x48, 0xA5] (RepPre 0x10f8e0 (RepMovsqPre 0x10f8e0)) (repMovsqEffect 0x10f8e0)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f8e0).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f8e0 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f8e3 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f8e3) (movR64R64Effect 0x10f8e3 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f8e3 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f8e3 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f8e6 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f8e6) (movR64R64Effect 0x10f8e6 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f8e6 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f8e6 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f8e9 [0xE8, 0x22, 0xAB, 0xFF, 0xFF] (PushPre 0x10f8e9 5) (callEffect (fun _ => 0x10a410) 0x10f8ee)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f8e9 0x10a410 0x10f8ee).toInstrSpec (call_rel32_effect_step 0x10f8e9 0xffffab22 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8dd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8e0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8e3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8e6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8e9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f8d1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f8d1 :=
  Rest.liftedBlock (rest_l10f8d1 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f8d1 x hx)

theorem rest_l10f8ee [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f8ee bytes_l10f8ee) (entryMap (live .l10f8ee))
      9 0x10f8ee bytes_l10f8ee b_l10f8ee := by
  have f0 : InstrSpec 0x10f8ee [0x48, 0x8D, 0xBB, 0x48, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x10f8ee) (leaR64Effect 0x10f8ee 7 (.base 3 (.d32 0x348)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f8ee 7 (.base 3 (.d32 0x348))).toInstrSpec (lea_r64_effect_step 0x10f8ee 0x48 (by decide) 7 (.base 3 (.d32 0x348)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f8f5 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f8f5) (movR32Imm32Effect 0x10f8f5 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f8f5 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f8f5 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f8fa [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f8fa) (movR64R64Effect 0x10f8fa 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f8fa 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f8fa 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f8fd [0xF3, 0x48, 0xA5] (RepPre 0x10f8fd (RepMovsqPre 0x10f8fd)) (repMovsqEffect 0x10f8fd)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f8fd).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f8fd 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f900 [0x4C, 0x8D, 0x7C, 0x24, 0x38] (fun s => s.RIP = 0x10f900) (leaR64Effect 0x10f900 15 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10f900 15 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10f900 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f905 [0x4C, 0x8D, 0xB4, 0x24, 0xF0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10f905) (leaR64Effect 0x10f905 14 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10f905 14 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (lea_r64_effect_step 0x10f905 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f90d [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10f90d) (movR64R64Effect 0x10f90d 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f90d 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10f90d 0x4c 0xff (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10f910 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f910) (movR64R64Effect 0x10f910 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f910 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f910 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10f913 [0xE8, 0xB8, 0x13, 0x00, 0x00] (PushPre 0x10f913 5) (callEffect (fun _ => 0x110cd0) 0x10f918)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f913 0x110cd0 0x10f918).toInstrSpec (call_rel32_effect_step 0x10f913 0x13b8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f8fd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f900) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f905) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 62), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f90d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 62), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f910) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 62), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f913) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 68), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 62), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cd0) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l10f8ee [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f8ee :=
  Rest.liftedBlock (rest_l10f8ee hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f8ee x hx)

theorem rest_l10f918 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f918 bytes_l10f918) (entryMap (live .l10f918))
      7 0x10f918 bytes_l10f918 b_l10f918 := by
  have f0 : InstrSpec 0x10f918 [0x48, 0x8D, 0xBB, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x10f918) (leaR64Effect 0x10f918 7 (.base 3 (.d32 0x3c0)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f918 7 (.base 3 (.d32 0x3c0))).toInstrSpec (lea_r64_effect_step 0x10f918 0x48 (by decide) 7 (.base 3 (.d32 0x3c0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f91f [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f91f) (movR32Imm32Effect 0x10f91f 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f91f 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f91f 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f924 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f924) (movR64R64Effect 0x10f924 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f924 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f924 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f927 [0xF3, 0x48, 0xA5] (RepPre 0x10f927 (RepMovsqPre 0x10f927)) (repMovsqEffect 0x10f927)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f927).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f927 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f92a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f92a) (movR64R64Effect 0x10f92a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f92a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f92a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f92d [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f92d) (movR64R64Effect 0x10f92d 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f92d 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f92d 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f930 [0xE8, 0xDB, 0xAA, 0xFF, 0xFF] (PushPre 0x10f930 5) (callEffect (fun _ => 0x10a410) 0x10f935)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f930 0x10a410 0x10f935).toInstrSpec (call_rel32_effect_step 0x10f930 0xffffaadb (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f91f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f924) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f927) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f92a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f92d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f930) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f918 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f918 :=
  Rest.liftedBlock (rest_l10f918 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f918 x hx)

theorem rest_l10f935 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f935 bytes_l10f935) (entryMap (live .l10f935))
      7 0x10f935 bytes_l10f935 b_l10f935 := by
  have f0 : InstrSpec 0x10f935 [0x48, 0x8D, 0xBB, 0x38, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x10f935) (leaR64Effect 0x10f935 7 (.base 3 (.d32 0x438)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f935 7 (.base 3 (.d32 0x438))).toInstrSpec (lea_r64_effect_step 0x10f935 0x48 (by decide) 7 (.base 3 (.d32 0x438)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f93c [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f93c) (movR32Imm32Effect 0x10f93c 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f93c 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f93c 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f941 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f941) (movR64R64Effect 0x10f941 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f941 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f941 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f944 [0xF3, 0x48, 0xA5] (RepPre 0x10f944 (RepMovsqPre 0x10f944)) (repMovsqEffect 0x10f944)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f944).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f944 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f947 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f947) (movR64R64Effect 0x10f947 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f947 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f947 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f94a [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f94a) (movR64R64Effect 0x10f94a 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f94a 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f94a 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f94d [0xE8, 0xBE, 0xAA, 0xFF, 0xFF] (PushPre 0x10f94d 5) (callEffect (fun _ => 0x10a410) 0x10f952)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f94d 0x10a410 0x10f952).toInstrSpec (call_rel32_effect_step 0x10f94d 0xffffaabe (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f93c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f941) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f944) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f947) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f94a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f94d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f935 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f935 :=
  Rest.liftedBlock (rest_l10f935 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f935 x hx)

theorem rest_l10f952 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f952 bytes_l10f952) (entryMap (live .l10f952))
      7 0x10f952 bytes_l10f952 b_l10f952 := by
  have f0 : InstrSpec 0x10f952 [0x48, 0x8D, 0xBB, 0xB0, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x10f952) (leaR64Effect 0x10f952 7 (.base 3 (.d32 0x4b0)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f952 7 (.base 3 (.d32 0x4b0))).toInstrSpec (lea_r64_effect_step 0x10f952 0x48 (by decide) 7 (.base 3 (.d32 0x4b0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f959 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f959) (movR32Imm32Effect 0x10f959 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f959 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f959 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f95e [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f95e) (movR64R64Effect 0x10f95e 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f95e 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f95e 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f961 [0xF3, 0x48, 0xA5] (RepPre 0x10f961 (RepMovsqPre 0x10f961)) (repMovsqEffect 0x10f961)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f961).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f961 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f964 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f964) (movR64R64Effect 0x10f964 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f964 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f964 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f967 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f967) (movR64R64Effect 0x10f967 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f967 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f967 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f96a [0xE8, 0xA1, 0xAA, 0xFF, 0xFF] (PushPre 0x10f96a 5) (callEffect (fun _ => 0x10a410) 0x10f96f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f96a 0x10a410 0x10f96f).toInstrSpec (call_rel32_effect_step 0x10f96a 0xffffaaa1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f959) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f95e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f961) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f964) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f967) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f96a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f952 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f952 :=
  Rest.liftedBlock (rest_l10f952 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f952 x hx)

theorem rest_l10f96f [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f96f bytes_l10f96f) (entryMap (live .l10f96f))
      7 0x10f96f bytes_l10f96f b_l10f96f := by
  have f0 : InstrSpec 0x10f96f [0x48, 0x8D, 0xBB, 0x28, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x10f96f) (leaR64Effect 0x10f96f 7 (.base 3 (.d32 0x528)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f96f 7 (.base 3 (.d32 0x528))).toInstrSpec (lea_r64_effect_step 0x10f96f 0x48 (by decide) 7 (.base 3 (.d32 0x528)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f976 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f976) (movR32Imm32Effect 0x10f976 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f976 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f976 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f97b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f97b) (movR64R64Effect 0x10f97b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f97b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f97b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f97e [0xF3, 0x48, 0xA5] (RepPre 0x10f97e (RepMovsqPre 0x10f97e)) (repMovsqEffect 0x10f97e)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f97e).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f97e 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f981 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f981) (movR64R64Effect 0x10f981 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f981 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f981 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f984 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f984) (movR64R64Effect 0x10f984 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f984 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f984 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f987 [0xE8, 0x84, 0xAA, 0xFF, 0xFF] (PushPre 0x10f987 5) (callEffect (fun _ => 0x10a410) 0x10f98c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f987 0x10a410 0x10f98c).toInstrSpec (call_rel32_effect_step 0x10f987 0xffffaa84 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f976) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f97b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f97e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f981) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f984) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f987) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f96f [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f96f :=
  Rest.liftedBlock (rest_l10f96f hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f96f x hx)

theorem rest_l10f98c [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f98c bytes_l10f98c) (entryMap (live .l10f98c))
      7 0x10f98c bytes_l10f98c b_l10f98c := by
  have f0 : InstrSpec 0x10f98c [0x48, 0x8D, 0xBB, 0xA0, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x10f98c) (leaR64Effect 0x10f98c 7 (.base 3 (.d32 0x5a0)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f98c 7 (.base 3 (.d32 0x5a0))).toInstrSpec (lea_r64_effect_step 0x10f98c 0x48 (by decide) 7 (.base 3 (.d32 0x5a0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f993 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f993) (movR32Imm32Effect 0x10f993 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f993 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f993 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f998 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f998) (movR64R64Effect 0x10f998 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f998 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f998 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f99b [0xF3, 0x48, 0xA5] (RepPre 0x10f99b (RepMovsqPre 0x10f99b)) (repMovsqEffect 0x10f99b)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f99b).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f99b 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f99e [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f99e) (movR64R64Effect 0x10f99e 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f99e 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f99e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f9a1 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f9a1) (movR64R64Effect 0x10f9a1 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f9a1 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f9a1 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f9a4 [0xE8, 0x67, 0xAA, 0xFF, 0xFF] (PushPre 0x10f9a4 5) (callEffect (fun _ => 0x10a410) 0x10f9a9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f9a4 0x10a410 0x10f9a9).toInstrSpec (call_rel32_effect_step 0x10f9a4 0xffffaa67 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f993) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f998) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f99b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f99e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9a1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9a4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f98c [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f98c :=
  Rest.liftedBlock (rest_l10f98c hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f98c x hx)

theorem rest_l10f9a9 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f9a9 bytes_l10f9a9) (entryMap (live .l10f9a9))
      7 0x10f9a9 bytes_l10f9a9 b_l10f9a9 := by
  have f0 : InstrSpec 0x10f9a9 [0x48, 0x8D, 0xBB, 0x18, 0x06, 0x00, 0x00] (fun s => s.RIP = 0x10f9a9) (leaR64Effect 0x10f9a9 7 (.base 3 (.d32 0x618)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f9a9 7 (.base 3 (.d32 0x618))).toInstrSpec (lea_r64_effect_step 0x10f9a9 0x48 (by decide) 7 (.base 3 (.d32 0x618)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f9b0 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f9b0) (movR32Imm32Effect 0x10f9b0 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f9b0 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f9b0 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f9b5 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f9b5) (movR64R64Effect 0x10f9b5 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f9b5 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f9b5 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f9b8 [0xF3, 0x48, 0xA5] (RepPre 0x10f9b8 (RepMovsqPre 0x10f9b8)) (repMovsqEffect 0x10f9b8)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f9b8).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f9b8 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f9bb [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f9bb) (movR64R64Effect 0x10f9bb 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f9bb 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f9bb 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f9be [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f9be) (movR64R64Effect 0x10f9be 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f9be 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f9be 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f9c1 [0xE8, 0x4A, 0xAA, 0xFF, 0xFF] (PushPre 0x10f9c1 5) (callEffect (fun _ => 0x10a410) 0x10f9c6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f9c1 0x10a410 0x10f9c6).toInstrSpec (call_rel32_effect_step 0x10f9c1 0xffffaa4a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9b8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9bb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9be) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9c1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f9a9 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f9a9 :=
  Rest.liftedBlock (rest_l10f9a9 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f9a9 x hx)

theorem rest_l10f9c6 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f9c6 bytes_l10f9c6) (entryMap (live .l10f9c6))
      7 0x10f9c6 bytes_l10f9c6 b_l10f9c6 := by
  have f0 : InstrSpec 0x10f9c6 [0x48, 0x8D, 0xBB, 0x90, 0x06, 0x00, 0x00] (fun s => s.RIP = 0x10f9c6) (leaR64Effect 0x10f9c6 7 (.base 3 (.d32 0x690)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f9c6 7 (.base 3 (.d32 0x690))).toInstrSpec (lea_r64_effect_step 0x10f9c6 0x48 (by decide) 7 (.base 3 (.d32 0x690)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f9cd [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f9cd) (movR32Imm32Effect 0x10f9cd 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f9cd 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f9cd 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f9d2 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f9d2) (movR64R64Effect 0x10f9d2 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f9d2 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f9d2 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f9d5 [0xF3, 0x48, 0xA5] (RepPre 0x10f9d5 (RepMovsqPre 0x10f9d5)) (repMovsqEffect 0x10f9d5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f9d5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f9d5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x10f9d8 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10f9d8) (movR64R64Effect 0x10f9d8 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f9d8 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10f9d8 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10f9db [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f9db) (movR64R64Effect 0x10f9db 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f9db 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f9db 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f9de [0xE8, 0x2D, 0xAA, 0xFF, 0xFF] (PushPre 0x10f9de 5) (callEffect (fun _ => 0x10a410) 0x10f9e3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f9de 0x10a410 0x10f9e3).toInstrSpec (call_rel32_effect_step 0x10f9de 0xffffaa2d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9cd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9d2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9d5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9d8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9db) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9de) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l10f9c6 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f9c6 :=
  Rest.liftedBlock (rest_l10f9c6 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f9c6 x hx)

theorem rest_l10f9e3 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f9e3 bytes_l10f9e3) (entryMap (live .l10f9e3))
      13 0x10f9e3 bytes_l10f9e3 b_l10f9e3 := by
  have f0 : InstrSpec 0x10f9e3 [0x48, 0x81, 0xC3, 0x08, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x10f9e3) (addR64Imm32Effect 0x10f9e3 3 0x708)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10f9e3 3 0x708).toInstrSpec (add_r64_imm32_effect_step 0x10f9e3 0x48 0xc3 0x708 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f9ea [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f9ea) (movR32Imm32Effect 0x10f9ea 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f9ea 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f9ea 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10f9ef [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10f9ef) (movR64R64Effect 0x10f9ef 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f9ef 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10f9ef 0x48 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f9f2 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f9f2) (movR64R64Effect 0x10f9f2 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f9f2 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f9f2 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10f9f5 [0xF3, 0x48, 0xA5] (RepPre 0x10f9f5 (RepMovsqPre 0x10f9f5)) (repMovsqEffect 0x10f9f5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f9f5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f9f5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x10f9f8 [0x48, 0x81, 0xC4, 0x88, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10f9f8) (addR64Imm32Effect 0x10f9f8 4 0x288)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10f9f8 4 0x288).toInstrSpec (add_r64_imm32_effect_step 0x10f9f8 0x48 0xc4 0x288 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10f9ff [0x5B] (PopPre 0x10f9ff) (popR64Effect 0x10f9ff 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10f9ff 1 3).toInstrSpec (pop_r64_effect_step 0x10f9ff 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10fa00 [0x41, 0x5C] (PopPre 0x10fa00) (popR64Effect 0x10fa00 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fa00 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10fa00 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10fa02 [0x41, 0x5D] (PopPre 0x10fa02) (popR64Effect 0x10fa02 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fa02 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10fa02 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x10fa04 [0x41, 0x5E] (PopPre 0x10fa04) (popR64Effect 0x10fa04 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fa04 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10fa04 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x10fa06 [0x41, 0x5F] (PopPre 0x10fa06) (popR64Effect 0x10fa06 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fa06 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10fa06 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x10fa08 [0x5D] (PopPre 0x10fa08) (popR64Effect 0x10fa08 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fa08 1 5).toInstrSpec (pop_r64_effect_step 0x10fa08 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x10fa09 [0xC3] (RetPre 0x10fa09) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10fa09).toInstrSpec (ret_effect_step 0x10fa09) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 53), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 53), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9ef) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 53), (4, 4), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9f2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 53), (4, 4), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9f5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 63) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 53), (4, 4), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9f8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 53), (4, 65), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f9ff) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 67), (4, 68), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa00) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 67), (4, 71), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa02) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 67), (4, 74), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa04) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 67), (4, 77), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa06) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 67), (4, 80), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa08) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 67), (4, 83), (5, 82), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa09) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f12 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 87) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 67), (4, 86), (5, 82), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) f12 (by decide) rfl rfl rfl (by decide)

theorem block_l10f9e3 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f9e3 :=
  Rest.liftedBlock (rest_l10f9e3 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f9e3 x hx)

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

theorem_by block_l10f150_eval :
    program.runBlock (dialect code) ⟨.l10f150, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f188_eval :
    program.runBlock (dialect code) ⟨.l10f188, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f1a2_eval :
    program.runBlock (dialect code) ⟨.l10f1a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f1b9_eval :
    program.runBlock (dialect code) ⟨.l10f1b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f1d3_eval :
    program.runBlock (dialect code) ⟨.l10f1d3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f1f0_eval :
    program.runBlock (dialect code) ⟨.l10f1f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f20a_eval :
    program.runBlock (dialect code) ⟨.l10f20a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f221_eval :
    program.runBlock (dialect code) ⟨.l10f221, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f326_eval :
    program.runBlock (dialect code) ⟨.l10f326, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f3c5_eval :
    program.runBlock (dialect code) ⟨.l10f3c5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f3cd_eval :
    program.runBlock (dialect code) ⟨.l10f3cd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f40e_eval :
    program.runBlock (dialect code) ⟨.l10f40e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f418_eval :
    program.runBlock (dialect code) ⟨.l10f418, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f44a_eval :
    program.runBlock (dialect code) ⟨.l10f44a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f44c_eval :
    program.runBlock (dialect code) ⟨.l10f44c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f48a_eval :
    program.runBlock (dialect code) ⟨.l10f48a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f4af_eval :
    program.runBlock (dialect code) ⟨.l10f4af, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f4c4_eval :
    program.runBlock (dialect code) ⟨.l10f4c4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f4ee_eval :
    program.runBlock (dialect code) ⟨.l10f4ee, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f507_eval :
    program.runBlock (dialect code) ⟨.l10f507, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f52c_eval :
    program.runBlock (dialect code) ⟨.l10f52c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f578_eval :
    program.runBlock (dialect code) ⟨.l10f578, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f680_eval :
    program.runBlock (dialect code) ⟨.l10f680, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f69e_eval :
    program.runBlock (dialect code) ⟨.l10f69e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f6ae_eval :
    program.runBlock (dialect code) ⟨.l10f6ae, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f6b9_eval :
    program.runBlock (dialect code) ⟨.l10f6b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f7fa_eval :
    program.runBlock (dialect code) ⟨.l10f7fa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f812_eval :
    program.runBlock (dialect code) ⟨.l10f812, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f82a_eval :
    program.runBlock (dialect code) ⟨.l10f82a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f843_eval :
    program.runBlock (dialect code) ⟨.l10f843, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f85d_eval :
    program.runBlock (dialect code) ⟨.l10f85d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f87a_eval :
    program.runBlock (dialect code) ⟨.l10f87a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f897_eval :
    program.runBlock (dialect code) ⟨.l10f897, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f8b4_eval :
    program.runBlock (dialect code) ⟨.l10f8b4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f8d1_eval :
    program.runBlock (dialect code) ⟨.l10f8d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f8ee_eval :
    program.runBlock (dialect code) ⟨.l10f8ee, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f918_eval :
    program.runBlock (dialect code) ⟨.l10f918, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f935_eval :
    program.runBlock (dialect code) ⟨.l10f935, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f952_eval :
    program.runBlock (dialect code) ⟨.l10f952, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f96f_eval :
    program.runBlock (dialect code) ⟨.l10f96f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f98c_eval :
    program.runBlock (dialect code) ⟨.l10f98c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f9a9_eval :
    program.runBlock (dialect code) ⟨.l10f9a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f9c6_eval :
    program.runBlock (dialect code) ⟨.l10f9c6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f9e3_eval :
    program.runBlock (dialect code) ⟨.l10f9e3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
