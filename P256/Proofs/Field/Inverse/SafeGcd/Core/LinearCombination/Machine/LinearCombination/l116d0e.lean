import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116d0e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11122e bytes_l116d0e) (entryMap (live .l116d0e))
      19 0x11122e bytes_l116d0e b_l116d0e := by
  have f0 : InstrSpec 0x11122e [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x11122e) (movR64R64Effect 0x11122e 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x11122e 11 2).toInstrSpec (mov_r64_r64_effect_step 0x11122e 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111231 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x111231) (movR64R64Effect 0x111231 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111231 2 1).toInstrSpec (mov_r64_r64_effect_step 0x111231 0x48 0xca (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111234 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x111234) (shrR64Effect 0x111234 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x111234 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x111234 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x111238 [0x48, 0x89, 0x54, 0x24, 0x20] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111238 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111238 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111238 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111238 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111238 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11123d [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11123d) (movR64R64Effect 0x11123d 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11123d 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11123d 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111240 [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x111240) (negR64Effect 0x111240 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x111240 0).toInstrSpec (neg_r64_effect_step 0x111240 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111243 [0x88, 0x14, 0x24] (StorePre 0x111243 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111243 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111243 3 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111243 3 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x111243 2 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x111246 [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x111246) (movR64R64Effect 0x111246 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111246 2 4).toInstrSpec (mov_r64_r64_effect_step 0x111246 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111249 [0x0F, 0xB6, 0x1C, 0x24] (LoadPre 0x111249 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111249 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111249 4 3 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x111249 4 3 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x111249 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11124d [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x11124d) (xorR64R64Effect 0x11124d 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11124d 0 1).toInstrSpec (xor_r64_r64_effect_step 0x11124d 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111250 [0x48, 0xF7, 0xDB] (fun s => s.RIP = 0x111250) (negR64Effect 0x111250 3)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (negR64Effect_footprint 0x111250 3).toInstrSpec (neg_r64_effect_step 0x111250 0x48 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111253 [0x48, 0x21, 0xC3] (fun s => s.RIP = 0x111253) (andR64R64Effect 0x111253 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111253 3 0).toInstrSpec (and_r64_r64_effect_step 0x111253 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111256 [0x48, 0x31, 0xCB] (fun s => s.RIP = 0x111256) (xorR64R64Effect 0x111256 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111256 3 1).toInstrSpec (xor_r64_r64_effect_step 0x111256 0x48 0xcb (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111259 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x111259) (movR64R64Effect 0x111259 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x111259 0 8).toInstrSpec (mov_r64_r64_effect_step 0x111259 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11125c [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x11125c) (shrR64Effect 0x11125c 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11125c 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x11125c 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x111260 [0x48, 0x89, 0x44, 0x24, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111260 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111260 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111260 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111260 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111260 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f16 : InstrSpec 0x111265 [0x88, 0x04, 0x24] (StorePre 0x111265 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111265 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111265 3 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111265 3 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x111265 0 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x111268 [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x111268) (movR64R64Effect 0x111268 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x111268 0 4).toInstrSpec (mov_r64_r64_effect_step 0x111268 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11126b [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x11126b) (movR64R64Effect 0x11126b 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11126b 0 3).toInstrSpec (mov_r64_r64_effect_step 0x11126b 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111231) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111234) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111238) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 57), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11123d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 57), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111240) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 57), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111243) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 1), (2, 57), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111246) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 1), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111249) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 1), (3, 66), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11124d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 1), (3, 66), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111250) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 1), (3, 70), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111253) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 68), (1, 1), (3, 72), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111256) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 68), (1, 1), (3, 74), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111259) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (3, 74), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11125c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (3, 74), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111260) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 1), (3, 74), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111265) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 1), (3, 74), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111268) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(1, 1), (3, 74), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11126b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (3, 74), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11126e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 85) (by decide) rfl

theorem block_l116d0e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116d0e :=
  Rest.liftedBlock (rest_l116d0e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116d0e x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
