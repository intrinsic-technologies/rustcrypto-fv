import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l101230 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101230 bytes_l101230) (entryMap (live .l101230))
      1 0x101230 bytes_l101230 b_l101230 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x101230 0xfe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l101230 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101230 :=
  Rest.liftedBlock (rest_l101230 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101230 x hx)

theorem rest_l101240 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101240 bytes_l101240) (entryMap (live .l101240))
      16 0x101240 bytes_l101240 b_l101240 := by
  have f0 : InstrSpec 0x101240 [0x55] (PushPre 0x101240 1) (pushR64Effect 0x101240 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101240 1 5).toInstrSpec (push_r64_effect_step 0x101240 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101241 [0x41, 0x57] (PushPre 0x101241 2) (pushR64Effect 0x101241 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101241 2 15).toInstrSpec (push_r64_rex_effect_step 0x101241 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101243 [0x41, 0x56] (PushPre 0x101243 2) (pushR64Effect 0x101243 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101243 2 14).toInstrSpec (push_r64_rex_effect_step 0x101243 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101245 [0x41, 0x55] (PushPre 0x101245 2) (pushR64Effect 0x101245 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101245 2 13).toInstrSpec (push_r64_rex_effect_step 0x101245 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101247 [0x41, 0x54] (PushPre 0x101247 2) (pushR64Effect 0x101247 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101247 2 12).toInstrSpec (push_r64_rex_effect_step 0x101247 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101249 [0x53] (PushPre 0x101249 1) (pushR64Effect 0x101249 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101249 1 3).toInstrSpec (push_r64_effect_step 0x101249 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10124a [0x48, 0x81, 0xEC, 0x98, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10124a) (subR64Imm32Effect 0x10124a 4 0x198)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10124a 4 0x198).toInstrSpec (sub_r64_imm32_effect_step 0x10124a 0x48 0xec 0x198 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101251 [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x101251) (movR64R64Effect 0x101251 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101251 13 9).toInstrSpec (mov_r64_r64_effect_step 0x101251 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101254 [0x4D, 0x89, 0xC4] (fun s => s.RIP = 0x101254) (movR64R64Effect 0x101254 12 8)
      [.gpr 8] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x101254 12 8).toInstrSpec (mov_r64_r64_effect_step 0x101254 0x4d 0xc4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101257 [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x101257) (movR64R64Effect 0x101257 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101257 3 1).toInstrSpec (mov_r64_r64_effect_step 0x101257 0x48 0xcb (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10125a [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x10125a) (movR64R64Effect 0x10125a 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10125a 14 2).toInstrSpec (mov_r64_r64_effect_step 0x10125a 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10125d [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x10125d) (movR64R64Effect 0x10125d 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10125d 15 6).toInstrSpec (mov_r64_r64_effect_step 0x10125d 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101260 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x101260) (movR64R64Effect 0x101260 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101260 6 7).toInstrSpec (mov_r64_r64_effect_step 0x101260 0x48 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101263 [0x48, 0x8D, 0x6C, 0x24, 0x10] (fun s => s.RIP = 0x101263) (leaR64Effect 0x101263 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x101263 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101263 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101268 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x101268) (movR64R64Effect 0x101268 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101268 7 5).toInstrSpec (mov_r64_r64_effect_step 0x101268 0x48 0xef (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10126b [0xE8, 0x00, 0x31, 0x00, 0x00] (PushPre 0x10126b 5) (callEffect (fun _ => 0x104370) 0x101270)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10126b 0x104370 0x101270).toInstrSpec (call_rel32_effect_step 0x10126b 0x3100 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101241) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101243) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101245) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101247) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101249) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10124a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101251) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101254) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101257) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10125a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10125d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101260) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 5), (6, 77), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101263) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 79), (6, 77), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101268) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10126b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 83), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104370) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l101240 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101240 :=
  Rest.liftedBlock (rest_l101240 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101240 x hx)

theorem rest_l101270 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101270 bytes_l101270) (entryMap (live .l101270))
      3 0x101270 bytes_l101270 b_l101270 := by
  have f0 : InstrSpec 0x101270 [0x48, 0x8D, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101270) (leaR64Effect 0x101270 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101270 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x101270 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101278 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x101278) (movR64R64Effect 0x101278 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101278 6 5).toInstrSpec (mov_r64_r64_effect_step 0x101278 0x48 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10127b [0xE8, 0xC0, 0x0D, 0x00, 0x00] (PushPre 0x10127b 5) (callEffect (fun _ => 0x102040) 0x101280)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10127b 0x102040 0x101280).toInstrSpec (call_rel32_effect_step 0x10127b 0xdc0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101278) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10127b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102040) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l101270 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101270 :=
  Rest.liftedBlock (rest_l101270 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101270 x hx)

theorem rest_l101280 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101280 bytes_l101280) (entryMap (live .l101280))
      3 0x101280 bytes_l101280 b_l101280 := by
  have f0 : InstrSpec 0x101280 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101280) (movR32Imm32Effect 0x101280 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x101280 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x101280 0xb8 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x101285 [0x49, 0x83, 0xFD, 0x10] (fun s => s.RIP = 0x101285) (cmpR64Imm8Effect 0x101285 13 0x10)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101285 13 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x101285 0x49 0xfd 0x10 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101285) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101289) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x101289 2 0x47) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101280 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101280 :=
  Rest.liftedBlock (rest_l101280 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101280 x hx)

theorem rest_l10128b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10128b bytes_l10128b) (entryMap (live .l10128b))
      15 0x10128b bytes_l10128b b_l10128b := by
  have f0 : InstrSpec 0x10128b [0x49, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x10128b) (leaR64Effect 0x10128b 0 (.base 13 (.d8 0xf0)))
      [.gpr 13] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10128b 0 (.base 13 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x10128b 0x49 (by decide) 0 (.base 13 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10128f [0x4B, 0x8B, 0x4C, 0x2C, 0xF0] (LoadPre 0x10128f (fun s => AddrMode.addr (.sib 12 (some 13) 0 (.d8 0xf0)) s (0x10128f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10128f 1 (.sib 12 (some 13) 0 (.d8 0xf0)))
      [.gpr 12, .gpr 13] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10128f 1 (.sib 12 (some 13) 0 (.d8 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x10128f 0x4b (by decide) 1 (.sib 12 (some 13) 0 (.d8 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101294 [0x4B, 0x8B, 0x54, 0x2C, 0xF8] (LoadPre 0x101294 (fun s => AddrMode.addr (.sib 12 (some 13) 0 (.d8 0xf8)) s (0x101294 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101294 2 (.sib 12 (some 13) 0 (.d8 0xf8)))
      [.gpr 12, .gpr 13] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101294 2 (.sib 12 (some 13) 0 (.d8 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x101294 0x4b (by decide) 2 (.sib 12 (some 13) 0 (.d8 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101299 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x101299 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101299 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101299 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101299 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101299 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10129e [0x48, 0x89, 0x0C, 0x24] (StorePre 0x10129e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10129e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10129e 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10129e 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10129e 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1012a2 [0x4C, 0x89, 0x64, 0x24, 0x10] (StorePre 0x1012a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1012a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012a2 12 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012a2 12 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1012a2 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1012a7 [0x4C, 0x89, 0x64, 0x24, 0x18] (StorePre 0x1012a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1012a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012a7 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012a7 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1012a7 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1012ac [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1012ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1012ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012ac 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012ac 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1012ac 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1012b1 [0x48, 0x8D, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1012b1) (leaR64Effect 0x1012b1 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1012b1 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x1012b1 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1012b9 [0x4C, 0x8D, 0x44, 0x24, 0x10] (fun s => s.RIP = 0x1012b9) (leaR64Effect 0x1012b9 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1012b9 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1012b9 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1012be [0x49, 0x89, 0xE1] (fun s => s.RIP = 0x1012be) (movR64R64Effect 0x1012be 9 4)
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1012be 9 4).toInstrSpec (mov_r64_r64_effect_step 0x1012be 0x49 0xe1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1012c1 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1012c1) (movR64R64Effect 0x1012c1 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1012c1 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1012c1 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1012c4 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1012c4) (movR64R64Effect 0x1012c4 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1012c4 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1012c4 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1012c7 [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x1012c7) (movR64R64Effect 0x1012c7 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1012c7 1 3).toInstrSpec (mov_r64_r64_effect_step 0x1012c7 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1012ca [0xE8, 0xF1, 0x0F, 0x00, 0x00] (PushPre 0x1012ca 5) (callEffect (fun _ => 0x1022c0) 0x1012cf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1012ca 0x1022c0 0x1012cf).toInstrSpec (call_rel32_effect_step 0x1012ca 0xff1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10128f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101294) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101299) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10129e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012a2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012a7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012ac) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012b1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (7, 64), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012b9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (7, 64), (8, 66), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012be) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012c1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012c4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 55), (2, 72), (3, 3), (4, 4), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012c7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 74), (2, 72), (3, 3), (4, 4), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012ca) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 74), (2, 72), (3, 3), (4, 76), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022c0) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 78) (by decide) (by decide) rfl rfl

theorem block_l10128b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10128b :=
  Rest.liftedBlock (rest_l10128b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10128b x hx)

theorem rest_l1012cf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1012cf bytes_l1012cf) (entryMap (live .l1012cf))
      1 0x1012cf bytes_l1012cf b_l1012cf := by
  have f0 : InstrSpec 0x1012cf [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x1012cf) (movzxR32R8Effect 0x1012cf 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x1012cf 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x1012cf 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1012cf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1012cf :=
  Rest.liftedBlock (rest_l1012cf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1012cf x hx)

theorem rest_l1012d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1012d2 bytes_l1012d2) (entryMap (live .l1012d2))
      8 0x1012d2 bytes_l1012d2 b_l1012d2 := by
  have f0 : InstrSpec 0x1012d2 [0x48, 0x81, 0xC4, 0x98, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1012d2) (addR64Imm32Effect 0x1012d2 4 0x198)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1012d2 4 0x198).toInstrSpec (add_r64_imm32_effect_step 0x1012d2 0x48 0xc4 0x198 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1012d9 [0x5B] (PopPre 0x1012d9) (popR64Effect 0x1012d9 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1012d9 1 3).toInstrSpec (pop_r64_effect_step 0x1012d9 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1012da [0x41, 0x5C] (PopPre 0x1012da) (popR64Effect 0x1012da 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1012da 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1012da 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1012dc [0x41, 0x5D] (PopPre 0x1012dc) (popR64Effect 0x1012dc 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1012dc 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1012dc 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1012de [0x41, 0x5E] (PopPre 0x1012de) (popR64Effect 0x1012de 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1012de 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1012de 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1012e0 [0x41, 0x5F] (PopPre 0x1012e0) (popR64Effect 0x1012e0 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1012e0 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1012e0 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1012e2 [0x5D] (PopPre 0x1012e2) (popR64Effect 0x1012e2 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1012e2 1 5).toInstrSpec (pop_r64_effect_step 0x1012e2 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1012e3 [0xC3] (RetPre 0x1012e3) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1012e3).toInstrSpec (ret_effect_step 0x1012e3) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012d9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012da) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012dc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012de) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012e0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012e2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012e3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l1012d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1012d2 :=
  Rest.liftedBlock (rest_l1012d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1012d2 x hx)

theorem rest_l1012f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1012f0 bytes_l1012f0) (entryMap (live .l1012f0))
      16 0x1012f0 bytes_l1012f0 b_l1012f0 := by
  have f0 : InstrSpec 0x1012f0 [0x55] (PushPre 0x1012f0 1) (pushR64Effect 0x1012f0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1012f0 1 5).toInstrSpec (push_r64_effect_step 0x1012f0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1012f1 [0x41, 0x57] (PushPre 0x1012f1 2) (pushR64Effect 0x1012f1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1012f1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1012f1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1012f3 [0x41, 0x56] (PushPre 0x1012f3 2) (pushR64Effect 0x1012f3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1012f3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1012f3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1012f5 [0x41, 0x55] (PushPre 0x1012f5 2) (pushR64Effect 0x1012f5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1012f5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1012f5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1012f7 [0x41, 0x54] (PushPre 0x1012f7 2) (pushR64Effect 0x1012f7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1012f7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1012f7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1012f9 [0x53] (PushPre 0x1012f9 1) (pushR64Effect 0x1012f9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1012f9 1 3).toInstrSpec (push_r64_effect_step 0x1012f9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1012fa [0x48, 0x81, 0xEC, 0x98, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1012fa) (subR64Imm32Effect 0x1012fa 4 0x198)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1012fa 4 0x198).toInstrSpec (sub_r64_imm32_effect_step 0x1012fa 0x48 0xec 0x198 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101301 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x101301) (movR64R64Effect 0x101301 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101301 3 9).toInstrSpec (mov_r64_r64_effect_step 0x101301 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101304 [0x4D, 0x89, 0xC6] (fun s => s.RIP = 0x101304) (movR64R64Effect 0x101304 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101304 14 8).toInstrSpec (mov_r64_r64_effect_step 0x101304 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101307 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x101307 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101307 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101307 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101307 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101307 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10130c [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10130c) (movR64R64Effect 0x10130c 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10130c 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10130c 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10130f [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x10130f) (movR64R64Effect 0x10130f 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10130f 13 6).toInstrSpec (mov_r64_r64_effect_step 0x10130f 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101312 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x101312) (movR64R64Effect 0x101312 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101312 6 7).toInstrSpec (mov_r64_r64_effect_step 0x101312 0x48 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101315 [0x48, 0x8D, 0x6C, 0x24, 0x10] (fun s => s.RIP = 0x101315) (leaR64Effect 0x101315 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x101315 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101315 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10131a [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x10131a) (movR64R64Effect 0x10131a 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10131a 7 5).toInstrSpec (mov_r64_r64_effect_step 0x10131a 0x48 0xef (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10131d [0xE8, 0x4E, 0x30, 0x00, 0x00] (PushPre 0x10131d 5) (callEffect (fun _ => 0x104370) 0x101322)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10131d 0x104370 0x101322).toInstrSpec (call_rel32_effect_step 0x10131d 0x304e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012f7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012f9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012fa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101301) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101304) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101307) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10130c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10130f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101312) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 76), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101315) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 78), (6, 76), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10131a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10131d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 82), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104370) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l1012f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1012f0 :=
  Rest.liftedBlock (rest_l1012f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1012f0 x hx)

theorem rest_l101322 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101322 bytes_l101322) (entryMap (live .l101322))
      4 0x101322 bytes_l101322 b_l101322 := by
  have f0 : InstrSpec 0x101322 [0x4C, 0x8D, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101322) (leaR64Effect 0x101322 15 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x101322 15 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x101322 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10132a [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10132a) (movR64R64Effect 0x10132a 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10132a 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10132a 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10132d [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x10132d) (movR64R64Effect 0x10132d 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10132d 6 5).toInstrSpec (mov_r64_r64_effect_step 0x10132d 0x48 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101330 [0xE8, 0x0B, 0x0D, 0x00, 0x00] (PushPre 0x101330 5) (callEffect (fun _ => 0x102040) 0x101335)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101330 0x102040 0x101335).toInstrSpec (call_rel32_effect_step 0x101330 0xd0b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10132a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10132d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101330) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102040) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101322 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101322 :=
  Rest.liftedBlock (rest_l101322 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101322 x hx)

theorem rest_l101335 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101335 bytes_l101335) (entryMap (live .l101335))
      12 0x101335 bytes_l101335 b_l101335 := by
  have f0 : InstrSpec 0x101335 [0x4C, 0x89, 0x74, 0x24, 0x10] (StorePre 0x101335 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101335 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101335 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101335 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101335 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10133a [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x10133a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x10133a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10133a 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10133a 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_r64_m64_effect_step 0x10133a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101342 [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x101342) (addR64R64Effect 0x101342 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101342 14 0).toInstrSpec (add_r64_r64_effect_step 0x101342 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101345 [0x48, 0x89, 0x5C, 0x24, 0x18] (StorePre 0x101345 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101345 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101345 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101345 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101345 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10134a [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10134a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10134a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10134a 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10134a 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10134a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10134f [0x4C, 0x8D, 0x44, 0x24, 0x10] (fun s => s.RIP = 0x10134f) (leaR64Effect 0x10134f 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x10134f 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x10134f 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101354 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101354) (movR64R64Effect 0x101354 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101354 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101354 0x4c 0xff (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101357 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x101357) (movR64R64Effect 0x101357 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101357 6 13).toInstrSpec (mov_r64_r64_effect_step 0x101357 0x4c 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10135a [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x10135a) (movR64R64Effect 0x10135a 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10135a 2 12).toInstrSpec (mov_r64_r64_effect_step 0x10135a 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10135d [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x10135d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10135d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10135d 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10135d 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10135d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101362 [0x4D, 0x89, 0xF1] (fun s => s.RIP = 0x101362) (movR64R64Effect 0x101362 9 14)
      [.gpr 14] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x101362 9 14).toInstrSpec (mov_r64_r64_effect_step 0x101362 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101365 [0xE8, 0x56, 0x0F, 0x00, 0x00] (PushPre 0x101365 5) (callEffect (fun _ => 0x1022c0) 0x10136a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101365 0x1022c0 0x10136a).toInstrSpec (call_rel32_effect_step 0x101365 0xf56 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10133a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101342) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101345) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10134a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10134f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101354) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (7, 62), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101357) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10135a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 54), (2, 66), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10135d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 68), (2, 66), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101362) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 54), (1, 68), (2, 66), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 60), (9, 70), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101365) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 54), (1, 68), (2, 66), (3, 3), (4, 72), (5, 5), (6, 64), (7, 62), (8, 60), (9, 70), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022c0) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 74) (by decide) (by decide) rfl rfl

theorem block_l101335 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101335 :=
  Rest.liftedBlock (rest_l101335 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101335 x hx)

theorem rest_l10136a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10136a bytes_l10136a) (entryMap (live .l10136a))
      9 0x10136a bytes_l10136a b_l10136a := by
  have f0 : InstrSpec 0x10136a [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x10136a) (movzxR32R8Effect 0x10136a 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x10136a 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x10136a 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10136d [0x48, 0x81, 0xC4, 0x98, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10136d) (addR64Imm32Effect 0x10136d 4 0x198)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10136d 4 0x198).toInstrSpec (add_r64_imm32_effect_step 0x10136d 0x48 0xc4 0x198 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101374 [0x5B] (PopPre 0x101374) (popR64Effect 0x101374 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101374 1 3).toInstrSpec (pop_r64_effect_step 0x101374 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101375 [0x41, 0x5C] (PopPre 0x101375) (popR64Effect 0x101375 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101375 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101375 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101377 [0x41, 0x5D] (PopPre 0x101377) (popR64Effect 0x101377 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101377 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101377 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101379 [0x41, 0x5E] (PopPre 0x101379) (popR64Effect 0x101379 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101379 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101379 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10137b [0x41, 0x5F] (PopPre 0x10137b) (popR64Effect 0x10137b 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10137b 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10137b 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10137d [0x5D] (PopPre 0x10137d) (popR64Effect 0x10137d 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10137d 1 5).toInstrSpec (pop_r64_effect_step 0x10137d 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10137e [0xC3] (RetPre 0x10137e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10137e).toInstrSpec (ret_effect_step 0x10137e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10136d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101374) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101375) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101377) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101379) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10137b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10137d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10137e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l10136a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10136a :=
  Rest.liftedBlock (rest_l10136a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10136a x hx)

theorem rest_l101380 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101380 bytes_l101380) (entryMap (live .l101380))
      16 0x101380 bytes_l101380 b_l101380 := by
  have f0 : InstrSpec 0x101380 [0x55] (PushPre 0x101380 1) (pushR64Effect 0x101380 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101380 1 5).toInstrSpec (push_r64_effect_step 0x101380 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101381 [0x41, 0x57] (PushPre 0x101381 2) (pushR64Effect 0x101381 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101381 2 15).toInstrSpec (push_r64_rex_effect_step 0x101381 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101383 [0x41, 0x56] (PushPre 0x101383 2) (pushR64Effect 0x101383 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101383 2 14).toInstrSpec (push_r64_rex_effect_step 0x101383 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101385 [0x41, 0x55] (PushPre 0x101385 2) (pushR64Effect 0x101385 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101385 2 13).toInstrSpec (push_r64_rex_effect_step 0x101385 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101387 [0x41, 0x54] (PushPre 0x101387 2) (pushR64Effect 0x101387 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101387 2 12).toInstrSpec (push_r64_rex_effect_step 0x101387 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101389 [0x53] (PushPre 0x101389 1) (pushR64Effect 0x101389 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101389 1 3).toInstrSpec (push_r64_effect_step 0x101389 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10138a [0x48, 0x81, 0xEC, 0xA8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10138a) (subR64Imm32Effect 0x10138a 4 0x1a8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10138a 4 0x1a8).toInstrSpec (sub_r64_imm32_effect_step 0x10138a 0x48 0xec 0x1a8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101391 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x101391) (movR64R64Effect 0x101391 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101391 3 9).toInstrSpec (mov_r64_r64_effect_step 0x101391 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101394 [0x4D, 0x89, 0xC6] (fun s => s.RIP = 0x101394) (movR64R64Effect 0x101394 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101394 14 8).toInstrSpec (mov_r64_r64_effect_step 0x101394 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101397 [0x49, 0x89, 0xCF] (fun s => s.RIP = 0x101397) (movR64R64Effect 0x101397 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x101397 15 1).toInstrSpec (mov_r64_r64_effect_step 0x101397 0x49 0xcf (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10139a [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10139a) (movR64R64Effect 0x10139a 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10139a 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10139a 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10139d [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x10139d) (movR64R64Effect 0x10139d 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10139d 13 6).toInstrSpec (mov_r64_r64_effect_step 0x10139d 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1013a0 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x1013a0) (movR64R64Effect 0x1013a0 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1013a0 6 7).toInstrSpec (mov_r64_r64_effect_step 0x1013a0 0x48 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1013a3 [0x48, 0x8D, 0x6C, 0x24, 0x20] (fun s => s.RIP = 0x1013a3) (leaR64Effect 0x1013a3 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x1013a3 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1013a3 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1013a8 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x1013a8) (movR64R64Effect 0x1013a8 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1013a8 7 5).toInstrSpec (mov_r64_r64_effect_step 0x1013a8 0x48 0xef (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1013ab [0xE8, 0xC0, 0x2F, 0x00, 0x00] (PushPre 0x1013ab 5) (callEffect (fun _ => 0x104370) 0x1013b0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1013ab 0x104370 0x1013b0).toInstrSpec (call_rel32_effect_step 0x1013ab 0x2fc0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101381) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101383) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101385) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101387) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101389) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10138a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101391) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101394) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101397) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10139a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 73), (13, 13), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10139d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013a0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 77), (7, 7), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013a3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 79), (6, 77), (7, 7), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013a8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013ab) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 83), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104370) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l101380 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101380 :=
  Rest.liftedBlock (rest_l101380 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101380 x hx)

theorem rest_l1013b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1013b0 bytes_l1013b0) (entryMap (live .l1013b0))
      4 0x1013b0 bytes_l1013b0 b_l1013b0 := by
  have f0 : InstrSpec 0x1013b0 [0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1013b0) (leaR64Effect 0x1013b0 7 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1013b0 7 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x1013b0 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1013b8 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x1013b8) (movR64R64Effect 0x1013b8 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1013b8 6 5).toInstrSpec (mov_r64_r64_effect_step 0x1013b8 0x48 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1013bb [0x48, 0x8B, 0xAC, 0x24, 0xE0, 0x01, 0x00, 0x00] (LoadPre 0x1013bb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x1013bb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013bb 5 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x1013bb 5 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_r64_m64_effect_step 0x1013bb 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1013c3 [0xE8, 0x78, 0x0C, 0x00, 0x00] (PushPre 0x1013c3 5) (callEffect (fun _ => 0x102040) 0x1013c8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1013c3 0x102040 0x1013c8).toInstrSpec (call_rel32_effect_step 0x1013c3 0xc78 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013bb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 57), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 57), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102040) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1013b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1013b0 :=
  Rest.liftedBlock (rest_l1013b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1013b0 x hx)

theorem rest_l1013c8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1013c8 bytes_l1013c8) (entryMap (live .l1013c8))
      15 0x1013c8 bytes_l1013c8 b_l1013c8 := by
  have f0 : InstrSpec 0x1013c8 [0x31, 0xC0] (fun s => s.RIP = 0x1013c8) (xorR32R32Effect 0x1013c8 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1013c8 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1013c8 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x1013ca [0x48, 0x39, 0xEB] (fun s => s.RIP = 0x1013ca) (cmpR64R64Effect 0x1013ca 3 5)
      [.gpr 3, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1013ca 3 5).toInstrSpec (cmp_r64_r64_effect_step 0x1013ca 0x48 0xeb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1013cd [0x48, 0x0F, 0x46, 0xC3] (fun s => s.RIP = 0x1013cd) (atFlags (condHolds 6) (cmovR64R64Effect 0x1013cd 4 0 3))
      [.gpr 0, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (cmovR64R64Effect_footprint 0x1013cd 4 0 3 6).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1013cd 6 0x48 (by decide) 0xc3 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1013d1 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1013d1) (movR32Imm32Effect 0x1013d1 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1013d1 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1013d1 0xb9 (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x1013d6 [0x49, 0x0F, 0x46, 0xCE] (fun s => s.RIP = 0x1013d6) (atFlags (condHolds 6) (cmovR64R64Effect 0x1013d6 4 1 14))
      [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x1013d6 4 1 14 6).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1013d6 6 0x49 (by decide) 0xce (by decide) c)) pre_rip
  have f5 : InstrSpec 0x1013da [0x48, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x1013da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1013da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1013da 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1013da 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1013da 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1013df [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x1013df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1013df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1013df 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1013df 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1013df 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1013e4 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x1013e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1013e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1013e4 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1013e4 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1013e4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1013e9 [0x48, 0x8D, 0x7C, 0x24, 0x0F] (fun s => s.RIP = 0x1013e9) (leaR64Effect 0x1013e9 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1013e9 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x1013e9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1013ee [0x4C, 0x8D, 0x4C, 0x24, 0x20] (fun s => s.RIP = 0x1013ee) (leaR64Effect 0x1013ee 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x1013ee 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1013ee 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1013f3 [0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1013f3) (leaR64Effect 0x1013f3 6 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1013f3 6 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x1013f3 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1013fb [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1013fb) (movR64R64Effect 0x1013fb 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1013fb 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1013fb 0x4c 0xea (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1013fe [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x1013fe) (movR64R64Effect 0x1013fe 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1013fe 1 12).toInstrSpec (mov_r64_r64_effect_step 0x1013fe 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101401 [0x4D, 0x89, 0xF8] (fun s => s.RIP = 0x101401) (movR64R64Effect 0x101401 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x101401 8 15).toInstrSpec (mov_r64_r64_effect_step 0x101401 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101404 [0xE8, 0x17, 0x11, 0x00, 0x00] (PushPre 0x101404 5) (callEffect (fun _ => 0x102520) 0x101409)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101404 0x102520 0x101409).toInstrSpec (call_rel32_effect_step 0x101404 0x1117 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013ca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013cd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013d1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 60), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013d6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013da) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013df) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013e4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013e9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (7, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013ee) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (7, 67), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013f3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013fb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 58), (1, 62), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013fe) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 58), (1, 75), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101401) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 58), (1, 75), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (8, 77), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101404) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 58), (1, 75), (2, 73), (3, 3), (4, 79), (5, 5), (6, 71), (7, 67), (8, 77), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102520) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l1013c8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1013c8 :=
  Rest.liftedBlock (rest_l1013c8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1013c8 x hx)

theorem rest_l101409 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101409 bytes_l101409) (entryMap (live .l101409))
      2 0x101409 bytes_l101409 b_l101409 := by
  have f0 : InstrSpec 0x101409 [0x80, 0x7C, 0x24, 0x0F, 0x01] (LoadPre 0x101409 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101409 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x101409 5 (.sib 4 none 0 (.d8 0xf)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x101409 5 (.sib 4 none 0 (.d8 0xf)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x101409 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10140e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x10140e 5 0x7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101409 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101409 :=
  Rest.liftedBlock (rest_l101409 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101409 x hx)

theorem rest_l101410 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101410 bytes_l101410) (entryMap (live .l101410))
      2 0x101410 bytes_l101410 b_l101410 := by
  have f0 : InstrSpec 0x101410 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101410) (movR32Imm32Effect 0x101410 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x101410 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x101410 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101415) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x101415 0x42 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l101410 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101410 :=
  Rest.liftedBlock (rest_l101410 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101410 x hx)

theorem rest_l101417 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101417 bytes_l101417) (entryMap (live .l101417))
      12 0x101417 bytes_l101417 b_l101417 := by
  have f0 : InstrSpec 0x101417 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x101417 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101417 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101417 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101417 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101417 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10141c [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x10141c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10141c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10141c 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10141c 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10141c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101421 [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x101421 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101421 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101421 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101421 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x101421 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101426 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x101426 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101426 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101426 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101426 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101426 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10142b [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10142b) (movR64R64Effect 0x10142b 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10142b 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10142b 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10142e [0x48, 0x83, 0xE8, 0xF0] (fun s => s.RIP = 0x10142e) (subR64Imm8Effect 0x10142e 0 0xf0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10142e 0 0xf0).toInstrSpec (sub_r64_imm8_effect_step 0x10142e 0x48 0xe8 0xf0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101432 [0x0F, 0x93, 0xC1] (fun s => s.RIP = 0x101432) (atFlags (condHolds 3) (setccR8Effect 0x101432 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x101432 3 1 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x101432 3 0xc1 (by decide) (by decide) c)) pre_rip
  have f7 : InstrSpec 0x101435 [0x48, 0x39, 0xE8] (fun s => s.RIP = 0x101435) (cmpR64R64Effect 0x101435 0 5)
      [.gpr 0, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x101435 0 5).toInstrSpec (cmp_r64_r64_effect_step 0x101435 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101438 [0x0F, 0x97, 0xC0] (fun s => s.RIP = 0x101438) (atFlags (condHolds 7) (setccR8Effect 0x101438 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x101438 3 0 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x101438 7 0xc0 (by decide) (by decide) c)) pre_rip
  have f9 : InstrSpec 0x10143b [0x08, 0xC8] (fun s => s.RIP = 0x10143b) (orR8R8Effect 0x10143b 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR8R8Effect_footprint 0x10143b 2 0 1).toInstrSpec (or_r8_r8_effect_step 0x10143b 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10143d [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10143d) (movR32Imm32Effect 0x10143d 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x10143d 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10143d 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10141c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101421) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101426) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10142b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10142e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101432) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101435) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (16, 66), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101438) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (16, 66), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10143b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10143d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101442) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 75) (jcc_rel8_effect_step 0x101442 5 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101417 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101417 :=
  Rest.liftedBlock (rest_l101417 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101417 x hx)

theorem rest_l101444 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101444 bytes_l101444) (entryMap (live .l101444))
      5 0x101444 bytes_l101444 b_l101444 := by
  have f0 : InstrSpec 0x101444 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x101444 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101444 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101444 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101444 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x101444 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101449 [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x101449 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101449 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101449 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101449 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x101449 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10144e [0x49, 0x89, 0x4C, 0x1E, 0x08] (StorePre 0x10144e 5 (fun s => AddrMode.addr (.sib 14 (some 3) 0 (.d8 0x8)) s (0x10144e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10144e 1 (.sib 14 (some 3) 0 (.d8 0x8)))
      [.gpr 1, .gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10144e 1 (.sib 14 (some 3) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10144e 0x49 (by decide) 1 (.sib 14 (some 3) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101453 [0x49, 0x89, 0x04, 0x1E] (StorePre 0x101453 4 (fun s => AddrMode.addr (.sib 14 (some 3) 0 .none) s (0x101453 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101453 0 (.sib 14 (some 3) 0 .none))
      [.gpr 0, .gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101453 0 (.sib 14 (some 3) 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101453 0x49 (by decide) 0 (.sib 14 (some 3) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101457 [0x31, 0xC0] (fun s => s.RIP = 0x101457) (xorR32R32Effect 0x101457 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101457 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x101457 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101449) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10144e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101453) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101457) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101459) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l101444 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101444 :=
  Rest.liftedBlock (rest_l101444 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101444 x hx)

theorem rest_l101459 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101459 bytes_l101459) (entryMap (live .l101459))
      8 0x101459 bytes_l101459 b_l101459 := by
  have f0 : InstrSpec 0x101459 [0x48, 0x81, 0xC4, 0xA8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101459) (addR64Imm32Effect 0x101459 4 0x1a8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101459 4 0x1a8).toInstrSpec (add_r64_imm32_effect_step 0x101459 0x48 0xc4 0x1a8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101460 [0x5B] (PopPre 0x101460) (popR64Effect 0x101460 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101460 1 3).toInstrSpec (pop_r64_effect_step 0x101460 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101461 [0x41, 0x5C] (PopPre 0x101461) (popR64Effect 0x101461 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101461 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101461 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101463 [0x41, 0x5D] (PopPre 0x101463) (popR64Effect 0x101463 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101463 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101463 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101465 [0x41, 0x5E] (PopPre 0x101465) (popR64Effect 0x101465 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101465 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101465 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101467 [0x41, 0x5F] (PopPre 0x101467) (popR64Effect 0x101467 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101467 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101467 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101469 [0x5D] (PopPre 0x101469) (popR64Effect 0x101469 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101469 1 5).toInstrSpec (pop_r64_effect_step 0x101469 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10146a [0xC3] (RetPre 0x10146a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10146a).toInstrSpec (ret_effect_step 0x10146a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101460) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101461) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101463) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101465) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101467) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101469) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10146a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l101459 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101459 :=
  Rest.liftedBlock (rest_l101459 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101459 x hx)

theorem rest_l101470 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101470 bytes_l101470) (entryMap (live .l101470))
      16 0x101470 bytes_l101470 b_l101470 := by
  have f0 : InstrSpec 0x101470 [0x55] (PushPre 0x101470 1) (pushR64Effect 0x101470 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101470 1 5).toInstrSpec (push_r64_effect_step 0x101470 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101471 [0x41, 0x57] (PushPre 0x101471 2) (pushR64Effect 0x101471 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101471 2 15).toInstrSpec (push_r64_rex_effect_step 0x101471 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101473 [0x41, 0x56] (PushPre 0x101473 2) (pushR64Effect 0x101473 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101473 2 14).toInstrSpec (push_r64_rex_effect_step 0x101473 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101475 [0x41, 0x55] (PushPre 0x101475 2) (pushR64Effect 0x101475 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101475 2 13).toInstrSpec (push_r64_rex_effect_step 0x101475 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101477 [0x41, 0x54] (PushPre 0x101477 2) (pushR64Effect 0x101477 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101477 2 12).toInstrSpec (push_r64_rex_effect_step 0x101477 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101479 [0x53] (PushPre 0x101479 1) (pushR64Effect 0x101479 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101479 1 3).toInstrSpec (push_r64_effect_step 0x101479 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10147a [0x48, 0x81, 0xEC, 0xA8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10147a) (subR64Imm32Effect 0x10147a 4 0x1a8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10147a 4 0x1a8).toInstrSpec (sub_r64_imm32_effect_step 0x10147a 0x48 0xec 0x1a8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101481 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x101481) (movR64R64Effect 0x101481 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101481 3 9).toInstrSpec (mov_r64_r64_effect_step 0x101481 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101484 [0x4D, 0x89, 0xC6] (fun s => s.RIP = 0x101484) (movR64R64Effect 0x101484 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101484 14 8).toInstrSpec (mov_r64_r64_effect_step 0x101484 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101487 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x101487 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101487 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101487 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101487 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101487 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10148b [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10148b) (movR64R64Effect 0x10148b 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10148b 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10148b 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10148e [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x10148e) (movR64R64Effect 0x10148e 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10148e 13 6).toInstrSpec (mov_r64_r64_effect_step 0x10148e 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101491 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x101491) (movR64R64Effect 0x101491 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101491 6 7).toInstrSpec (mov_r64_r64_effect_step 0x101491 0x48 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101494 [0x48, 0x8D, 0x6C, 0x24, 0x20] (fun s => s.RIP = 0x101494) (leaR64Effect 0x101494 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x101494 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x101494 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101499 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x101499) (movR64R64Effect 0x101499 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101499 7 5).toInstrSpec (mov_r64_r64_effect_step 0x101499 0x48 0xef (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10149c [0xE8, 0xCF, 0x2E, 0x00, 0x00] (PushPre 0x10149c 5) (callEffect (fun _ => 0x104370) 0x1014a1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10149c 0x104370 0x1014a1).toInstrSpec (call_rel32_effect_step 0x10149c 0x2ecf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101471) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101473) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101475) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101477) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101479) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10147a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101481) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101484) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101487) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10148b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10148e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101491) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 76), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101494) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 78), (6, 76), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101499) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10149c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 82), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104370) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l101470 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101470 :=
  Rest.liftedBlock (rest_l101470 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101470 x hx)

theorem rest_l1014a1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014a1 bytes_l1014a1) (entryMap (live .l1014a1))
      4 0x1014a1 bytes_l1014a1 b_l1014a1 := by
  have f0 : InstrSpec 0x1014a1 [0x4C, 0x8D, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1014a1) (leaR64Effect 0x1014a1 15 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1014a1 15 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x1014a1 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1014a9 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x1014a9) (movR64R64Effect 0x1014a9 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1014a9 7 15).toInstrSpec (mov_r64_r64_effect_step 0x1014a9 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1014ac [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x1014ac) (movR64R64Effect 0x1014ac 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1014ac 6 5).toInstrSpec (mov_r64_r64_effect_step 0x1014ac 0x48 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1014af [0xE8, 0x8C, 0x0B, 0x00, 0x00] (PushPre 0x1014af 5) (callEffect (fun _ => 0x102040) 0x1014b4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1014af 0x102040 0x1014b4).toInstrSpec (call_rel32_effect_step 0x1014af 0xb8c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014a9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014ac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014af) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102040) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1014a1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014a1 :=
  Rest.liftedBlock (rest_l1014a1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014a1 x hx)

theorem rest_l1014b4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014b4 bytes_l1014b4) (entryMap (live .l1014b4))
      11 0x1014b4 bytes_l1014b4 b_l1014b4 := by
  have f0 : InstrSpec 0x1014b4 [0x4C, 0x89, 0x74, 0x24, 0x20] (StorePre 0x1014b4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1014b4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014b4 14 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1014b4 14 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1014b4 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1014b9 [0x4C, 0x8B, 0xB4, 0x24, 0xE0, 0x01, 0x00, 0x00] (LoadPre 0x1014b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x1014b9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1014b9 14 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1014b9 14 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_r64_m64_effect_step 0x1014b9 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1014c1 [0x48, 0x89, 0x5C, 0x24, 0x28] (StorePre 0x1014c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1014c1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014c1 3 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1014c1 3 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1014c1 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1014c6 [0x4C, 0x89, 0x74, 0x24, 0x30] (StorePre 0x1014c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1014c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014c6 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1014c6 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1014c6 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1014cb [0x48, 0x8D, 0x7C, 0x24, 0x0F] (fun s => s.RIP = 0x1014cb) (leaR64Effect 0x1014cb 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1014cb 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x1014cb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1014d0 [0x4C, 0x8D, 0x4C, 0x24, 0x20] (fun s => s.RIP = 0x1014d0) (leaR64Effect 0x1014d0 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x1014d0 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1014d0 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1014d5 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1014d5) (movR64R64Effect 0x1014d5 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1014d5 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1014d5 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1014d8 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1014d8) (movR64R64Effect 0x1014d8 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1014d8 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1014d8 0x4c 0xea (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1014db [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x1014db) (movR64R64Effect 0x1014db 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1014db 1 12).toInstrSpec (mov_r64_r64_effect_step 0x1014db 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1014de [0x4C, 0x8B, 0x04, 0x24] (LoadPre 0x1014de (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1014de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1014de 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1014de 8 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1014de 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1014e2 [0xE8, 0x39, 0x10, 0x00, 0x00] (PushPre 0x1014e2 5) (callEffect (fun _ => 0x102520) 0x1014e7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1014e2 0x102520 0x1014e7).toInstrSpec (call_rel32_effect_step 0x1014e2 0x1039 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014cb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 58), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014d0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 58), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014d5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 58), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014d8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 4), (5, 5), (6, 62), (7, 58), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014db) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 62), (7, 58), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014de) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 62), (7, 58), (8, 68), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014e2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 70), (5, 5), (6, 62), (7, 58), (8, 68), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102520) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 72) (by decide) (by decide) rfl rfl

theorem block_l1014b4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014b4 :=
  Rest.liftedBlock (rest_l1014b4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014b4 x hx)

theorem rest_l1014e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014e7 bytes_l1014e7) (entryMap (live .l1014e7))
      3 0x1014e7 bytes_l1014e7 b_l1014e7 := by
  have f0 : InstrSpec 0x1014e7 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1014e7) (movR32Imm32Effect 0x1014e7 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1014e7 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1014e7 0xb8 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x1014ec [0x80, 0x7C, 0x24, 0x0F, 0x00] (LoadPre 0x1014ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1014ec + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1014ec 5 (.sib 4 none 0 (.d8 0xf)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1014ec 5 (.sib 4 none 0 (.d8 0xf)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x1014ec (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014ec) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014f1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1014f1 5 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1014e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014e7 :=
  Rest.liftedBlock (rest_l1014e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014e7 x hx)

theorem rest_l1014f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014f3 bytes_l1014f3) (entryMap (live .l1014f3))
      5 0x1014f3 bytes_l1014f3 b_l1014f3 := by
  have f0 : InstrSpec 0x1014f3 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1014f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1014f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1014f3 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1014f3 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1014f3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1014f8 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1014f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1014f8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1014f8 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1014f8 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1014f8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1014fd [0x4A, 0x89, 0x4C, 0x33, 0x08] (StorePre 0x1014fd 5 (fun s => AddrMode.addr (.sib 3 (some 14) 0 (.d8 0x8)) s (0x1014fd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014fd 1 (.sib 3 (some 14) 0 (.d8 0x8)))
      [.gpr 1, .gpr 3, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1014fd 1 (.sib 3 (some 14) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1014fd 0x4a (by decide) 1 (.sib 3 (some 14) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101502 [0x4A, 0x89, 0x04, 0x33] (StorePre 0x101502 4 (fun s => AddrMode.addr (.sib 3 (some 14) 0 .none) s (0x101502 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101502 0 (.sib 3 (some 14) 0 .none))
      [.gpr 0, .gpr 3, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x101502 0 (.sib 3 (some 14) 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101502 0x4a (by decide) 0 (.sib 3 (some 14) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101506 [0x31, 0xC0] (fun s => s.RIP = 0x101506) (xorR32R32Effect 0x101506 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101506 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x101506 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014fd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101502) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101506) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101508) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l1014f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014f3 :=
  Rest.liftedBlock (rest_l1014f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014f3 x hx)

theorem rest_l101508 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101508 bytes_l101508) (entryMap (live .l101508))
      8 0x101508 bytes_l101508 b_l101508 := by
  have f0 : InstrSpec 0x101508 [0x48, 0x81, 0xC4, 0xA8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101508) (addR64Imm32Effect 0x101508 4 0x1a8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101508 4 0x1a8).toInstrSpec (add_r64_imm32_effect_step 0x101508 0x48 0xc4 0x1a8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10150f [0x5B] (PopPre 0x10150f) (popR64Effect 0x10150f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10150f 1 3).toInstrSpec (pop_r64_effect_step 0x10150f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101510 [0x41, 0x5C] (PopPre 0x101510) (popR64Effect 0x101510 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101510 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101510 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101512 [0x41, 0x5D] (PopPre 0x101512) (popR64Effect 0x101512 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101512 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101512 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101514 [0x41, 0x5E] (PopPre 0x101514) (popR64Effect 0x101514 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101514 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101514 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101516 [0x41, 0x5F] (PopPre 0x101516) (popR64Effect 0x101516 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101516 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101516 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101518 [0x5D] (PopPre 0x101518) (popR64Effect 0x101518 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101518 1 5).toInstrSpec (pop_r64_effect_step 0x101518 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x101519 [0xC3] (RetPre 0x101519) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101519).toInstrSpec (ret_effect_step 0x101519) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10150f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101510) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101512) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101514) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101516) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101518) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101519) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l101508 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101508 :=
  Rest.liftedBlock (rest_l101508 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101508 x hx)

theorem rest_l101520 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101520 bytes_l101520) (entryMap (live .l101520))
      16 0x101520 bytes_l101520 b_l101520 := by
  have f0 : InstrSpec 0x101520 [0x55] (PushPre 0x101520 1) (pushR64Effect 0x101520 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101520 1 5).toInstrSpec (push_r64_effect_step 0x101520 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101521 [0x41, 0x57] (PushPre 0x101521 2) (pushR64Effect 0x101521 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101521 2 15).toInstrSpec (push_r64_rex_effect_step 0x101521 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101523 [0x41, 0x56] (PushPre 0x101523 2) (pushR64Effect 0x101523 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101523 2 14).toInstrSpec (push_r64_rex_effect_step 0x101523 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101525 [0x41, 0x55] (PushPre 0x101525 2) (pushR64Effect 0x101525 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101525 2 13).toInstrSpec (push_r64_rex_effect_step 0x101525 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101527 [0x41, 0x54] (PushPre 0x101527 2) (pushR64Effect 0x101527 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101527 2 12).toInstrSpec (push_r64_rex_effect_step 0x101527 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101529 [0x53] (PushPre 0x101529 1) (pushR64Effect 0x101529 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101529 1 3).toInstrSpec (push_r64_effect_step 0x101529 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10152a [0x48, 0x81, 0xEC, 0x18, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10152a) (subR64Imm32Effect 0x10152a 4 0x218)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10152a 4 0x218).toInstrSpec (sub_r64_imm32_effect_step 0x10152a 0x48 0xec 0x218 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101531 [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x101531) (movR64R64Effect 0x101531 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101531 13 9).toInstrSpec (mov_r64_r64_effect_step 0x101531 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101534 [0x4D, 0x89, 0xC4] (fun s => s.RIP = 0x101534) (movR64R64Effect 0x101534 12 8)
      [.gpr 8] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x101534 12 8).toInstrSpec (mov_r64_r64_effect_step 0x101534 0x4d 0xc4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101537 [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x101537) (movR64R64Effect 0x101537 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101537 3 1).toInstrSpec (mov_r64_r64_effect_step 0x101537 0x48 0xcb (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10153a [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x10153a) (movR64R64Effect 0x10153a 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10153a 14 2).toInstrSpec (mov_r64_r64_effect_step 0x10153a 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10153d [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x10153d) (movR64R64Effect 0x10153d 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10153d 15 6).toInstrSpec (mov_r64_r64_effect_step 0x10153d 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101540 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x101540) (movR64R64Effect 0x101540 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101540 6 7).toInstrSpec (mov_r64_r64_effect_step 0x101540 0x48 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101543 [0x48, 0x8D, 0x6C, 0x24, 0x10] (fun s => s.RIP = 0x101543) (leaR64Effect 0x101543 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x101543 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101543 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101548 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x101548) (movR64R64Effect 0x101548 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101548 7 5).toInstrSpec (mov_r64_r64_effect_step 0x101548 0x48 0xef (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10154b [0xE8, 0x70, 0x42, 0x00, 0x00] (PushPre 0x10154b 5) (callEffect (fun _ => 0x1057c0) 0x101550)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10154b 0x1057c0 0x101550).toInstrSpec (call_rel32_effect_step 0x10154b 0x4270 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101521) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101523) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101525) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101527) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101529) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10152a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101531) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101534) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101537) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10153a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10153d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101540) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 5), (6, 77), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101543) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 79), (6, 77), (7, 7), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101548) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 65), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10154b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 1), (2, 2), (3, 71), (4, 83), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 69), (13, 67), (14, 73), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c0) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l101520 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101520 :=
  Rest.liftedBlock (rest_l101520 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101520 x hx)

theorem rest_l101550 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101550 bytes_l101550) (entryMap (live .l101550))
      3 0x101550 bytes_l101550 b_l101550 := by
  have f0 : InstrSpec 0x101550 [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101550) (leaR64Effect 0x101550 7 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101550 7 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x101550 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101558 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x101558) (movR64R64Effect 0x101558 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101558 6 5).toInstrSpec (mov_r64_r64_effect_step 0x101558 0x48 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10155b [0xE8, 0x20, 0x0C, 0x00, 0x00] (PushPre 0x10155b 5) (callEffect (fun _ => 0x102180) 0x101560)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10155b 0x102180 0x101560).toInstrSpec (call_rel32_effect_step 0x10155b 0xc20 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101558) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10155b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102180) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l101550 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101550 :=
  Rest.liftedBlock (rest_l101550 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101550 x hx)

theorem rest_l101560 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101560 bytes_l101560) (entryMap (live .l101560))
      3 0x101560 bytes_l101560 b_l101560 := by
  have f0 : InstrSpec 0x101560 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101560) (movR32Imm32Effect 0x101560 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x101560 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x101560 0xb8 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x101565 [0x49, 0x83, 0xFD, 0x10] (fun s => s.RIP = 0x101565) (cmpR64Imm8Effect 0x101565 13 0x10)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101565 13 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x101565 0x49 0xfd 0x10 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101565) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101569) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x101569 2 0x47) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101560 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101560 :=
  Rest.liftedBlock (rest_l101560 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101560 x hx)

theorem rest_l10156b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10156b bytes_l10156b) (entryMap (live .l10156b))
      15 0x10156b bytes_l10156b b_l10156b := by
  have f0 : InstrSpec 0x10156b [0x49, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x10156b) (leaR64Effect 0x10156b 0 (.base 13 (.d8 0xf0)))
      [.gpr 13] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10156b 0 (.base 13 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x10156b 0x49 (by decide) 0 (.base 13 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10156f [0x4B, 0x8B, 0x4C, 0x2C, 0xF0] (LoadPre 0x10156f (fun s => AddrMode.addr (.sib 12 (some 13) 0 (.d8 0xf0)) s (0x10156f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10156f 1 (.sib 12 (some 13) 0 (.d8 0xf0)))
      [.gpr 12, .gpr 13] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10156f 1 (.sib 12 (some 13) 0 (.d8 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x10156f 0x4b (by decide) 1 (.sib 12 (some 13) 0 (.d8 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101574 [0x4B, 0x8B, 0x54, 0x2C, 0xF8] (LoadPre 0x101574 (fun s => AddrMode.addr (.sib 12 (some 13) 0 (.d8 0xf8)) s (0x101574 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101574 2 (.sib 12 (some 13) 0 (.d8 0xf8)))
      [.gpr 12, .gpr 13] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101574 2 (.sib 12 (some 13) 0 (.d8 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x101574 0x4b (by decide) 2 (.sib 12 (some 13) 0 (.d8 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101579 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x101579 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101579 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101579 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101579 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101579 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10157e [0x48, 0x89, 0x0C, 0x24] (StorePre 0x10157e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10157e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10157e 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10157e 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10157e 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x101582 [0x4C, 0x89, 0x64, 0x24, 0x10] (StorePre 0x101582 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101582 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101582 12 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101582 12 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101582 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101587 [0x4C, 0x89, 0x64, 0x24, 0x18] (StorePre 0x101587 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101587 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101587 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101587 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101587 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10158c [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10158c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10158c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10158c 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10158c 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10158c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101591 [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101591) (leaR64Effect 0x101591 7 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101591 7 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x101591 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101599 [0x4C, 0x8D, 0x44, 0x24, 0x10] (fun s => s.RIP = 0x101599) (leaR64Effect 0x101599 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x101599 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101599 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10159e [0x49, 0x89, 0xE1] (fun s => s.RIP = 0x10159e) (movR64R64Effect 0x10159e 9 4)
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10159e 9 4).toInstrSpec (mov_r64_r64_effect_step 0x10159e 0x49 0xe1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1015a1 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1015a1) (movR64R64Effect 0x1015a1 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1015a1 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1015a1 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1015a4 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1015a4) (movR64R64Effect 0x1015a4 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1015a4 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1015a4 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1015a7 [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x1015a7) (movR64R64Effect 0x1015a7 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1015a7 1 3).toInstrSpec (mov_r64_r64_effect_step 0x1015a7 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1015aa [0xE8, 0x71, 0x11, 0x00, 0x00] (PushPre 0x1015aa 5) (callEffect (fun _ => 0x102720) 0x1015af)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1015aa 0x102720 0x1015af).toInstrSpec (call_rel32_effect_step 0x1015aa 0x1171 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10156f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101574) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101579) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10157e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101582) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101587) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10158c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101591) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (7, 64), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101599) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (7, 64), (8, 66), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10159e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015a1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015a4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 55), (2, 72), (3, 3), (4, 4), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015a7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 74), (2, 72), (3, 3), (4, 4), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015aa) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 74), (2, 72), (3, 3), (4, 76), (5, 5), (6, 70), (7, 64), (8, 66), (9, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102720) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 78) (by decide) (by decide) rfl rfl

theorem block_l10156b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10156b :=
  Rest.liftedBlock (rest_l10156b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10156b x hx)

theorem rest_l1015af [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015af bytes_l1015af) (entryMap (live .l1015af))
      1 0x1015af bytes_l1015af b_l1015af := by
  have f0 : InstrSpec 0x1015af [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x1015af) (movzxR32R8Effect 0x1015af 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x1015af 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x1015af 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015b2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1015af [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015af :=
  Rest.liftedBlock (rest_l1015af code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015af x hx)

theorem rest_l1015b2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015b2 bytes_l1015b2) (entryMap (live .l1015b2))
      8 0x1015b2 bytes_l1015b2 b_l1015b2 := by
  have f0 : InstrSpec 0x1015b2 [0x48, 0x81, 0xC4, 0x18, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x1015b2) (addR64Imm32Effect 0x1015b2 4 0x218)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1015b2 4 0x218).toInstrSpec (add_r64_imm32_effect_step 0x1015b2 0x48 0xc4 0x218 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1015b9 [0x5B] (PopPre 0x1015b9) (popR64Effect 0x1015b9 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1015b9 1 3).toInstrSpec (pop_r64_effect_step 0x1015b9 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1015ba [0x41, 0x5C] (PopPre 0x1015ba) (popR64Effect 0x1015ba 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1015ba 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1015ba 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1015bc [0x41, 0x5D] (PopPre 0x1015bc) (popR64Effect 0x1015bc 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1015bc 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1015bc 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1015be [0x41, 0x5E] (PopPre 0x1015be) (popR64Effect 0x1015be 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1015be 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1015be 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1015c0 [0x41, 0x5F] (PopPre 0x1015c0) (popR64Effect 0x1015c0 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1015c0 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1015c0 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1015c2 [0x5D] (PopPre 0x1015c2) (popR64Effect 0x1015c2 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1015c2 1 5).toInstrSpec (pop_r64_effect_step 0x1015c2 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1015c3 [0xC3] (RetPre 0x1015c3) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1015c3).toInstrSpec (ret_effect_step 0x1015c3) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015ba) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015bc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015be) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015c2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015c3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l1015b2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015b2 :=
  Rest.liftedBlock (rest_l1015b2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015b2 x hx)

theorem rest_l1015d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015d0 bytes_l1015d0) (entryMap (live .l1015d0))
      16 0x1015d0 bytes_l1015d0 b_l1015d0 := by
  have f0 : InstrSpec 0x1015d0 [0x55] (PushPre 0x1015d0 1) (pushR64Effect 0x1015d0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1015d0 1 5).toInstrSpec (push_r64_effect_step 0x1015d0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1015d1 [0x41, 0x57] (PushPre 0x1015d1 2) (pushR64Effect 0x1015d1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1015d1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1015d1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1015d3 [0x41, 0x56] (PushPre 0x1015d3 2) (pushR64Effect 0x1015d3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1015d3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1015d3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1015d5 [0x41, 0x55] (PushPre 0x1015d5 2) (pushR64Effect 0x1015d5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1015d5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1015d5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1015d7 [0x41, 0x54] (PushPre 0x1015d7 2) (pushR64Effect 0x1015d7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1015d7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1015d7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1015d9 [0x53] (PushPre 0x1015d9 1) (pushR64Effect 0x1015d9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1015d9 1 3).toInstrSpec (push_r64_effect_step 0x1015d9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1015da [0x48, 0x81, 0xEC, 0x18, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x1015da) (subR64Imm32Effect 0x1015da 4 0x218)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1015da 4 0x218).toInstrSpec (sub_r64_imm32_effect_step 0x1015da 0x48 0xec 0x218 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1015e1 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x1015e1) (movR64R64Effect 0x1015e1 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1015e1 3 9).toInstrSpec (mov_r64_r64_effect_step 0x1015e1 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1015e4 [0x4D, 0x89, 0xC6] (fun s => s.RIP = 0x1015e4) (movR64R64Effect 0x1015e4 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1015e4 14 8).toInstrSpec (mov_r64_r64_effect_step 0x1015e4 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1015e7 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x1015e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1015e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1015e7 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1015e7 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1015e7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1015ec [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x1015ec) (movR64R64Effect 0x1015ec 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1015ec 12 2).toInstrSpec (mov_r64_r64_effect_step 0x1015ec 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1015ef [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x1015ef) (movR64R64Effect 0x1015ef 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1015ef 13 6).toInstrSpec (mov_r64_r64_effect_step 0x1015ef 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1015f2 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x1015f2) (movR64R64Effect 0x1015f2 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1015f2 6 7).toInstrSpec (mov_r64_r64_effect_step 0x1015f2 0x48 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1015f5 [0x48, 0x8D, 0x6C, 0x24, 0x10] (fun s => s.RIP = 0x1015f5) (leaR64Effect 0x1015f5 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x1015f5 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1015f5 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1015fa [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x1015fa) (movR64R64Effect 0x1015fa 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1015fa 7 5).toInstrSpec (mov_r64_r64_effect_step 0x1015fa 0x48 0xef (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1015fd [0xE8, 0xBE, 0x41, 0x00, 0x00] (PushPre 0x1015fd 5) (callEffect (fun _ => 0x1057c0) 0x101602)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1015fd 0x1057c0 0x101602).toInstrSpec (call_rel32_effect_step 0x1015fd 0x41be (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015d1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015d3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015d5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015d7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015d9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015da) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015e1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015e4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015e7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015ec) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015ef) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015f2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 76), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015f5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 78), (6, 76), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015fa) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015fd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 82), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c0) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l1015d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015d0 :=
  Rest.liftedBlock (rest_l1015d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015d0 x hx)

theorem rest_l101602 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101602 bytes_l101602) (entryMap (live .l101602))
      4 0x101602 bytes_l101602 b_l101602 := by
  have f0 : InstrSpec 0x101602 [0x4C, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101602) (leaR64Effect 0x101602 15 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x101602 15 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x101602 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10160a [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10160a) (movR64R64Effect 0x10160a 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10160a 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10160a 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10160d [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x10160d) (movR64R64Effect 0x10160d 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10160d 6 5).toInstrSpec (mov_r64_r64_effect_step 0x10160d 0x48 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101610 [0xE8, 0x6B, 0x0B, 0x00, 0x00] (PushPre 0x101610 5) (callEffect (fun _ => 0x102180) 0x101615)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101610 0x102180 0x101615).toInstrSpec (call_rel32_effect_step 0x101610 0xb6b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10160a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10160d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101610) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102180) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101602 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101602 :=
  Rest.liftedBlock (rest_l101602 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101602 x hx)

theorem rest_l101615 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101615 bytes_l101615) (entryMap (live .l101615))
      12 0x101615 bytes_l101615 b_l101615 := by
  have f0 : InstrSpec 0x101615 [0x4C, 0x89, 0x74, 0x24, 0x10] (StorePre 0x101615 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101615 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101615 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101615 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101615 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10161a [0x48, 0x8B, 0x84, 0x24, 0x50, 0x02, 0x00, 0x00] (LoadPre 0x10161a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x10161a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10161a 0 (.sib 4 none 0 (.d32 0x250)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10161a 0 (.sib 4 none 0 (.d32 0x250))).toInstrSpec (mov_r64_m64_effect_step 0x10161a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x250)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101622 [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x101622) (addR64R64Effect 0x101622 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101622 14 0).toInstrSpec (add_r64_r64_effect_step 0x101622 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101625 [0x48, 0x89, 0x5C, 0x24, 0x18] (StorePre 0x101625 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101625 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101625 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101625 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101625 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10162a [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10162a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10162a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10162a 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10162a 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10162a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10162f [0x4C, 0x8D, 0x44, 0x24, 0x10] (fun s => s.RIP = 0x10162f) (leaR64Effect 0x10162f 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x10162f 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x10162f 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101634 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101634) (movR64R64Effect 0x101634 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101634 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101634 0x4c 0xff (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101637 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x101637) (movR64R64Effect 0x101637 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101637 6 13).toInstrSpec (mov_r64_r64_effect_step 0x101637 0x4c 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10163a [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x10163a) (movR64R64Effect 0x10163a 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10163a 2 12).toInstrSpec (mov_r64_r64_effect_step 0x10163a 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10163d [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x10163d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10163d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10163d 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10163d 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10163d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101642 [0x4D, 0x89, 0xF1] (fun s => s.RIP = 0x101642) (movR64R64Effect 0x101642 9 14)
      [.gpr 14] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x101642 9 14).toInstrSpec (mov_r64_r64_effect_step 0x101642 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101645 [0xE8, 0xD6, 0x10, 0x00, 0x00] (PushPre 0x101645 5) (callEffect (fun _ => 0x102720) 0x10164a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101645 0x102720 0x10164a).toInstrSpec (call_rel32_effect_step 0x101645 0x10d6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10161a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101622) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101625) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10162a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10162f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101634) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (7, 62), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101637) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10163a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 54), (2, 66), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10163d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 68), (2, 66), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 60), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101642) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 54), (1, 68), (2, 66), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 60), (9, 70), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101645) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 54), (1, 68), (2, 66), (3, 3), (4, 72), (5, 5), (6, 64), (7, 62), (8, 60), (9, 70), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102720) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 74) (by decide) (by decide) rfl rfl

theorem block_l101615 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101615 :=
  Rest.liftedBlock (rest_l101615 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101615 x hx)

theorem rest_l10164a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10164a bytes_l10164a) (entryMap (live .l10164a))
      9 0x10164a bytes_l10164a b_l10164a := by
  have f0 : InstrSpec 0x10164a [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x10164a) (movzxR32R8Effect 0x10164a 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x10164a 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x10164a 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10164d [0x48, 0x81, 0xC4, 0x18, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10164d) (addR64Imm32Effect 0x10164d 4 0x218)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10164d 4 0x218).toInstrSpec (add_r64_imm32_effect_step 0x10164d 0x48 0xc4 0x218 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101654 [0x5B] (PopPre 0x101654) (popR64Effect 0x101654 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101654 1 3).toInstrSpec (pop_r64_effect_step 0x101654 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101655 [0x41, 0x5C] (PopPre 0x101655) (popR64Effect 0x101655 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101655 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101655 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101657 [0x41, 0x5D] (PopPre 0x101657) (popR64Effect 0x101657 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101657 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101657 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101659 [0x41, 0x5E] (PopPre 0x101659) (popR64Effect 0x101659 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101659 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101659 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10165b [0x41, 0x5F] (PopPre 0x10165b) (popR64Effect 0x10165b 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10165b 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10165b 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10165d [0x5D] (PopPre 0x10165d) (popR64Effect 0x10165d 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10165d 1 5).toInstrSpec (pop_r64_effect_step 0x10165d 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10165e [0xC3] (RetPre 0x10165e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10165e).toInstrSpec (ret_effect_step 0x10165e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10164d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101654) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101655) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101657) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101659) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10165b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10165d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10165e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l10164a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10164a :=
  Rest.liftedBlock (rest_l10164a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10164a x hx)

theorem rest_l101660 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101660 bytes_l101660) (entryMap (live .l101660))
      16 0x101660 bytes_l101660 b_l101660 := by
  have f0 : InstrSpec 0x101660 [0x55] (PushPre 0x101660 1) (pushR64Effect 0x101660 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101660 1 5).toInstrSpec (push_r64_effect_step 0x101660 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101661 [0x41, 0x57] (PushPre 0x101661 2) (pushR64Effect 0x101661 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101661 2 15).toInstrSpec (push_r64_rex_effect_step 0x101661 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101663 [0x41, 0x56] (PushPre 0x101663 2) (pushR64Effect 0x101663 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101663 2 14).toInstrSpec (push_r64_rex_effect_step 0x101663 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101665 [0x41, 0x55] (PushPre 0x101665 2) (pushR64Effect 0x101665 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101665 2 13).toInstrSpec (push_r64_rex_effect_step 0x101665 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101667 [0x41, 0x54] (PushPre 0x101667 2) (pushR64Effect 0x101667 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101667 2 12).toInstrSpec (push_r64_rex_effect_step 0x101667 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101669 [0x53] (PushPre 0x101669 1) (pushR64Effect 0x101669 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101669 1 3).toInstrSpec (push_r64_effect_step 0x101669 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10166a [0x48, 0x81, 0xEC, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10166a) (subR64Imm32Effect 0x10166a 4 0x228)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10166a 4 0x228).toInstrSpec (sub_r64_imm32_effect_step 0x10166a 0x48 0xec 0x228 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101671 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x101671) (movR64R64Effect 0x101671 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101671 3 9).toInstrSpec (mov_r64_r64_effect_step 0x101671 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101674 [0x4D, 0x89, 0xC6] (fun s => s.RIP = 0x101674) (movR64R64Effect 0x101674 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101674 14 8).toInstrSpec (mov_r64_r64_effect_step 0x101674 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101677 [0x49, 0x89, 0xCF] (fun s => s.RIP = 0x101677) (movR64R64Effect 0x101677 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x101677 15 1).toInstrSpec (mov_r64_r64_effect_step 0x101677 0x49 0xcf (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10167a [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10167a) (movR64R64Effect 0x10167a 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10167a 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10167a 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10167d [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x10167d) (movR64R64Effect 0x10167d 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10167d 13 6).toInstrSpec (mov_r64_r64_effect_step 0x10167d 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101680 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x101680) (movR64R64Effect 0x101680 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101680 6 7).toInstrSpec (mov_r64_r64_effect_step 0x101680 0x48 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101683 [0x48, 0x8D, 0x6C, 0x24, 0x20] (fun s => s.RIP = 0x101683) (leaR64Effect 0x101683 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x101683 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x101683 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101688 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x101688) (movR64R64Effect 0x101688 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101688 7 5).toInstrSpec (mov_r64_r64_effect_step 0x101688 0x48 0xef (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10168b [0xE8, 0x30, 0x41, 0x00, 0x00] (PushPre 0x10168b 5) (callEffect (fun _ => 0x1057c0) 0x101690)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10168b 0x1057c0 0x101690).toInstrSpec (call_rel32_effect_step 0x10168b 0x4130 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101661) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101663) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101665) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101667) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101669) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10166a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101671) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101674) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101677) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10167a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 73), (13, 13), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10167d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101680) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 77), (7, 7), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101683) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 79), (6, 77), (7, 7), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101688) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10168b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 83), (5, 79), (6, 77), (7, 81), (8, 8), (9, 9), (11, 11), (12, 73), (13, 75), (14, 69), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c0) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l101660 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101660 :=
  Rest.liftedBlock (rest_l101660 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101660 x hx)

theorem rest_l101690 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101690 bytes_l101690) (entryMap (live .l101690))
      4 0x101690 bytes_l101690 b_l101690 := by
  have f0 : InstrSpec 0x101690 [0x48, 0x8D, 0xBC, 0x24, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101690) (leaR64Effect 0x101690 7 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101690 7 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (lea_r64_effect_step 0x101690 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101698 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x101698) (movR64R64Effect 0x101698 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101698 6 5).toInstrSpec (mov_r64_r64_effect_step 0x101698 0x48 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10169b [0x48, 0x8B, 0xAC, 0x24, 0x60, 0x02, 0x00, 0x00] (LoadPre 0x10169b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x10169b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10169b 5 (.sib 4 none 0 (.d32 0x260)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10169b 5 (.sib 4 none 0 (.d32 0x260))).toInstrSpec (mov_r64_m64_effect_step 0x10169b 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x260)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1016a3 [0xE8, 0xD8, 0x0A, 0x00, 0x00] (PushPre 0x1016a3 5) (callEffect (fun _ => 0x102180) 0x1016a8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1016a3 0x102180 0x1016a8).toInstrSpec (call_rel32_effect_step 0x1016a3 0xad8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101698) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10169b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 57), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 57), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102180) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101690 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101690 :=
  Rest.liftedBlock (rest_l101690 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101690 x hx)

theorem rest_l1016a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1016a8 bytes_l1016a8) (entryMap (live .l1016a8))
      15 0x1016a8 bytes_l1016a8 b_l1016a8 := by
  have f0 : InstrSpec 0x1016a8 [0x31, 0xC0] (fun s => s.RIP = 0x1016a8) (xorR32R32Effect 0x1016a8 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1016a8 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1016a8 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x1016aa [0x48, 0x39, 0xEB] (fun s => s.RIP = 0x1016aa) (cmpR64R64Effect 0x1016aa 3 5)
      [.gpr 3, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1016aa 3 5).toInstrSpec (cmp_r64_r64_effect_step 0x1016aa 0x48 0xeb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1016ad [0x48, 0x0F, 0x46, 0xC3] (fun s => s.RIP = 0x1016ad) (atFlags (condHolds 6) (cmovR64R64Effect 0x1016ad 4 0 3))
      [.gpr 0, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (cmovR64R64Effect_footprint 0x1016ad 4 0 3 6).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1016ad 6 0x48 (by decide) 0xc3 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1016b1 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1016b1) (movR32Imm32Effect 0x1016b1 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1016b1 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1016b1 0xb9 (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x1016b6 [0x49, 0x0F, 0x46, 0xCE] (fun s => s.RIP = 0x1016b6) (atFlags (condHolds 6) (cmovR64R64Effect 0x1016b6 4 1 14))
      [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x1016b6 4 1 14 6).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1016b6 6 0x49 (by decide) 0xce (by decide) c)) pre_rip
  have f5 : InstrSpec 0x1016ba [0x48, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x1016ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1016ba + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016ba 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1016ba 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1016ba 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1016bf [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x1016bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1016bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016bf 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1016bf 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1016bf 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1016c4 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x1016c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1016c4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016c4 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1016c4 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1016c4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1016c9 [0x48, 0x8D, 0x7C, 0x24, 0x0F] (fun s => s.RIP = 0x1016c9) (leaR64Effect 0x1016c9 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1016c9 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x1016c9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1016ce [0x4C, 0x8D, 0x4C, 0x24, 0x20] (fun s => s.RIP = 0x1016ce) (leaR64Effect 0x1016ce 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x1016ce 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1016ce 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1016d3 [0x48, 0x8D, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1016d3) (leaR64Effect 0x1016d3 6 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1016d3 6 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (lea_r64_effect_step 0x1016d3 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1016db [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1016db) (movR64R64Effect 0x1016db 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1016db 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1016db 0x4c 0xea (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1016de [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x1016de) (movR64R64Effect 0x1016de 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1016de 1 12).toInstrSpec (mov_r64_r64_effect_step 0x1016de 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1016e1 [0x4D, 0x89, 0xF8] (fun s => s.RIP = 0x1016e1) (movR64R64Effect 0x1016e1 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1016e1 8 15).toInstrSpec (mov_r64_r64_effect_step 0x1016e1 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1016e4 [0xE8, 0x97, 0x12, 0x00, 0x00] (PushPre 0x1016e4 5) (callEffect (fun _ => 0x102980) 0x1016e9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1016e4 0x102980 0x1016e9).toInstrSpec (call_rel32_effect_step 0x1016e4 0x1297 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016aa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016ad) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016b1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 60), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016b6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016ba) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016bf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016c4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016c9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (7, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016ce) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (7, 67), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016d3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 62), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016db) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 58), (1, 62), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016de) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 58), (1, 75), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016e1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 58), (1, 75), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 67), (8, 77), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016e4) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 58), (1, 75), (2, 73), (3, 3), (4, 79), (5, 5), (6, 71), (7, 67), (8, 77), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102980) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l1016a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1016a8 :=
  Rest.liftedBlock (rest_l1016a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1016a8 x hx)

theorem rest_l1016e9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1016e9 bytes_l1016e9) (entryMap (live .l1016e9))
      2 0x1016e9 bytes_l1016e9 b_l1016e9 := by
  have f0 : InstrSpec 0x1016e9 [0x80, 0x7C, 0x24, 0x0F, 0x01] (LoadPre 0x1016e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1016e9 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1016e9 5 (.sib 4 none 0 (.d8 0xf)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1016e9 5 (.sib 4 none 0 (.d8 0xf)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x1016e9 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016ee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1016ee 5 0x7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1016e9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1016e9 :=
  Rest.liftedBlock (rest_l1016e9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1016e9 x hx)

theorem rest_l1016f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1016f0 bytes_l1016f0) (entryMap (live .l1016f0))
      2 0x1016f0 bytes_l1016f0 b_l1016f0 := by
  have f0 : InstrSpec 0x1016f0 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1016f0) (movR32Imm32Effect 0x1016f0 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1016f0 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1016f0 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1016f5 0x42 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1016f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1016f0 :=
  Rest.liftedBlock (rest_l1016f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1016f0 x hx)

theorem rest_l1016f7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1016f7 bytes_l1016f7) (entryMap (live .l1016f7))
      12 0x1016f7 bytes_l1016f7 b_l1016f7 := by
  have f0 : InstrSpec 0x1016f7 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1016f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1016f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1016f7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1016f7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1016f7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1016fc [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1016fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1016fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1016fc 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1016fc 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1016fc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101701 [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x101701 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101701 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101701 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101701 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x101701 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101706 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x101706 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101706 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101706 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101706 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101706 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10170b [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10170b) (movR64R64Effect 0x10170b 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10170b 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10170b 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10170e [0x48, 0x83, 0xE8, 0xF0] (fun s => s.RIP = 0x10170e) (subR64Imm8Effect 0x10170e 0 0xf0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10170e 0 0xf0).toInstrSpec (sub_r64_imm8_effect_step 0x10170e 0x48 0xe8 0xf0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101712 [0x0F, 0x93, 0xC1] (fun s => s.RIP = 0x101712) (atFlags (condHolds 3) (setccR8Effect 0x101712 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x101712 3 1 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x101712 3 0xc1 (by decide) (by decide) c)) pre_rip
  have f7 : InstrSpec 0x101715 [0x48, 0x39, 0xE8] (fun s => s.RIP = 0x101715) (cmpR64R64Effect 0x101715 0 5)
      [.gpr 0, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x101715 0 5).toInstrSpec (cmp_r64_r64_effect_step 0x101715 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101718 [0x0F, 0x97, 0xC0] (fun s => s.RIP = 0x101718) (atFlags (condHolds 7) (setccR8Effect 0x101718 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x101718 3 0 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x101718 7 0xc0 (by decide) (by decide) c)) pre_rip
  have f9 : InstrSpec 0x10171b [0x08, 0xC8] (fun s => s.RIP = 0x10171b) (orR8R8Effect 0x10171b 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR8R8Effect_footprint 0x10171b 2 0 1).toInstrSpec (or_r8_r8_effect_step 0x10171b 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10171d [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10171d) (movR32Imm32Effect 0x10171d 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x10171d 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10171d 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016fc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101701) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101706) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10170b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10170e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101712) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101715) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (16, 66), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101718) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (16, 66), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10171b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10171d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101722) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 75) (jcc_rel8_effect_step 0x101722 5 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1016f7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1016f7 :=
  Rest.liftedBlock (rest_l1016f7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1016f7 x hx)

theorem rest_l101724 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101724 bytes_l101724) (entryMap (live .l101724))
      5 0x101724 bytes_l101724 b_l101724 := by
  have f0 : InstrSpec 0x101724 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x101724 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101724 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101724 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101724 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x101724 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101729 [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x101729 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101729 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101729 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101729 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x101729 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10172e [0x49, 0x89, 0x4C, 0x1E, 0x08] (StorePre 0x10172e 5 (fun s => AddrMode.addr (.sib 14 (some 3) 0 (.d8 0x8)) s (0x10172e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10172e 1 (.sib 14 (some 3) 0 (.d8 0x8)))
      [.gpr 1, .gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10172e 1 (.sib 14 (some 3) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10172e 0x49 (by decide) 1 (.sib 14 (some 3) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101733 [0x49, 0x89, 0x04, 0x1E] (StorePre 0x101733 4 (fun s => AddrMode.addr (.sib 14 (some 3) 0 .none) s (0x101733 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101733 0 (.sib 14 (some 3) 0 .none))
      [.gpr 0, .gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101733 0 (.sib 14 (some 3) 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101733 0x49 (by decide) 0 (.sib 14 (some 3) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101737 [0x31, 0xC0] (fun s => s.RIP = 0x101737) (xorR32R32Effect 0x101737 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101737 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x101737 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101729) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10172e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101733) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101737) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101739) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l101724 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101724 :=
  Rest.liftedBlock (rest_l101724 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101724 x hx)

theorem rest_l101739 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101739 bytes_l101739) (entryMap (live .l101739))
      8 0x101739 bytes_l101739 b_l101739 := by
  have f0 : InstrSpec 0x101739 [0x48, 0x81, 0xC4, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x101739) (addR64Imm32Effect 0x101739 4 0x228)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101739 4 0x228).toInstrSpec (add_r64_imm32_effect_step 0x101739 0x48 0xc4 0x228 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101740 [0x5B] (PopPre 0x101740) (popR64Effect 0x101740 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101740 1 3).toInstrSpec (pop_r64_effect_step 0x101740 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101741 [0x41, 0x5C] (PopPre 0x101741) (popR64Effect 0x101741 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101741 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101741 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101743 [0x41, 0x5D] (PopPre 0x101743) (popR64Effect 0x101743 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101743 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101743 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101745 [0x41, 0x5E] (PopPre 0x101745) (popR64Effect 0x101745 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101745 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101745 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101747 [0x41, 0x5F] (PopPre 0x101747) (popR64Effect 0x101747 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101747 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101747 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101749 [0x5D] (PopPre 0x101749) (popR64Effect 0x101749 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101749 1 5).toInstrSpec (pop_r64_effect_step 0x101749 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10174a [0xC3] (RetPre 0x10174a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10174a).toInstrSpec (ret_effect_step 0x10174a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101740) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101741) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101743) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101745) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101747) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101749) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10174a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l101739 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101739 :=
  Rest.liftedBlock (rest_l101739 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101739 x hx)

theorem rest_l101750 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101750 bytes_l101750) (entryMap (live .l101750))
      16 0x101750 bytes_l101750 b_l101750 := by
  have f0 : InstrSpec 0x101750 [0x55] (PushPre 0x101750 1) (pushR64Effect 0x101750 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101750 1 5).toInstrSpec (push_r64_effect_step 0x101750 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101751 [0x41, 0x57] (PushPre 0x101751 2) (pushR64Effect 0x101751 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101751 2 15).toInstrSpec (push_r64_rex_effect_step 0x101751 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101753 [0x41, 0x56] (PushPre 0x101753 2) (pushR64Effect 0x101753 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101753 2 14).toInstrSpec (push_r64_rex_effect_step 0x101753 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101755 [0x41, 0x55] (PushPre 0x101755 2) (pushR64Effect 0x101755 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101755 2 13).toInstrSpec (push_r64_rex_effect_step 0x101755 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101757 [0x41, 0x54] (PushPre 0x101757 2) (pushR64Effect 0x101757 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101757 2 12).toInstrSpec (push_r64_rex_effect_step 0x101757 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101759 [0x53] (PushPre 0x101759 1) (pushR64Effect 0x101759 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101759 1 3).toInstrSpec (push_r64_effect_step 0x101759 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10175a [0x48, 0x81, 0xEC, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10175a) (subR64Imm32Effect 0x10175a 4 0x228)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10175a 4 0x228).toInstrSpec (sub_r64_imm32_effect_step 0x10175a 0x48 0xec 0x228 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101761 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x101761) (movR64R64Effect 0x101761 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101761 3 9).toInstrSpec (mov_r64_r64_effect_step 0x101761 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101764 [0x4D, 0x89, 0xC6] (fun s => s.RIP = 0x101764) (movR64R64Effect 0x101764 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101764 14 8).toInstrSpec (mov_r64_r64_effect_step 0x101764 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101767 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x101767 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101767 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101767 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101767 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101767 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10176b [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10176b) (movR64R64Effect 0x10176b 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10176b 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10176b 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10176e [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x10176e) (movR64R64Effect 0x10176e 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10176e 13 6).toInstrSpec (mov_r64_r64_effect_step 0x10176e 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101771 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x101771) (movR64R64Effect 0x101771 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101771 6 7).toInstrSpec (mov_r64_r64_effect_step 0x101771 0x48 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101774 [0x48, 0x8D, 0x6C, 0x24, 0x20] (fun s => s.RIP = 0x101774) (leaR64Effect 0x101774 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x101774 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x101774 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101779 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x101779) (movR64R64Effect 0x101779 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101779 7 5).toInstrSpec (mov_r64_r64_effect_step 0x101779 0x48 0xef (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10177c [0xE8, 0x3F, 0x40, 0x00, 0x00] (PushPre 0x10177c 5) (callEffect (fun _ => 0x1057c0) 0x101781)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10177c 0x1057c0 0x101781).toInstrSpec (call_rel32_effect_step 0x10177c 0x403f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101751) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101753) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101755) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101757) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101759) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10175a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101761) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101764) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101767) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10176b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10176e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101771) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 76), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101774) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 78), (6, 76), (7, 7), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101779) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10177c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 82), (5, 78), (6, 76), (7, 80), (8, 8), (9, 9), (11, 11), (12, 72), (13, 74), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c0) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l101750 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101750 :=
  Rest.liftedBlock (rest_l101750 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101750 x hx)

theorem rest_l101781 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101781 bytes_l101781) (entryMap (live .l101781))
      4 0x101781 bytes_l101781 b_l101781 := by
  have f0 : InstrSpec 0x101781 [0x4C, 0x8D, 0xBC, 0x24, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101781) (leaR64Effect 0x101781 15 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x101781 15 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (lea_r64_effect_step 0x101781 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101789 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101789) (movR64R64Effect 0x101789 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101789 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101789 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10178c [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x10178c) (movR64R64Effect 0x10178c 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10178c 6 5).toInstrSpec (mov_r64_r64_effect_step 0x10178c 0x48 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10178f [0xE8, 0xEC, 0x09, 0x00, 0x00] (PushPre 0x10178f 5) (callEffect (fun _ => 0x102180) 0x101794)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10178f 0x102180 0x101794).toInstrSpec (call_rel32_effect_step 0x10178f 0x9ec (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101789) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10178c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10178f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102180) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101781 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101781 :=
  Rest.liftedBlock (rest_l101781 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101781 x hx)

theorem rest_l101794 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101794 bytes_l101794) (entryMap (live .l101794))
      11 0x101794 bytes_l101794 b_l101794 := by
  have f0 : InstrSpec 0x101794 [0x4C, 0x89, 0x74, 0x24, 0x20] (StorePre 0x101794 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101794 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101794 14 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101794 14 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101794 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101799 [0x4C, 0x8B, 0xB4, 0x24, 0x60, 0x02, 0x00, 0x00] (LoadPre 0x101799 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x101799 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101799 14 (.sib 4 none 0 (.d32 0x260)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x101799 14 (.sib 4 none 0 (.d32 0x260))).toInstrSpec (mov_r64_m64_effect_step 0x101799 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x260)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1017a1 [0x48, 0x89, 0x5C, 0x24, 0x28] (StorePre 0x1017a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1017a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017a1 3 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017a1 3 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1017a1 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1017a6 [0x4C, 0x89, 0x74, 0x24, 0x30] (StorePre 0x1017a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1017a6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017a6 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017a6 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1017a6 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1017ab [0x48, 0x8D, 0x7C, 0x24, 0x0F] (fun s => s.RIP = 0x1017ab) (leaR64Effect 0x1017ab 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1017ab 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x1017ab 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1017b0 [0x4C, 0x8D, 0x4C, 0x24, 0x20] (fun s => s.RIP = 0x1017b0) (leaR64Effect 0x1017b0 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x1017b0 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1017b0 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1017b5 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1017b5) (movR64R64Effect 0x1017b5 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1017b5 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1017b5 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1017b8 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1017b8) (movR64R64Effect 0x1017b8 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1017b8 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1017b8 0x4c 0xea (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1017bb [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x1017bb) (movR64R64Effect 0x1017bb 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1017bb 1 12).toInstrSpec (mov_r64_r64_effect_step 0x1017bb 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1017be [0x4C, 0x8B, 0x04, 0x24] (LoadPre 0x1017be (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1017be + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1017be 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1017be 8 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1017be 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1017c2 [0xE8, 0xB9, 0x11, 0x00, 0x00] (PushPre 0x1017c2 5) (callEffect (fun _ => 0x102980) 0x1017c7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1017c2 0x102980 0x1017c7).toInstrSpec (call_rel32_effect_step 0x1017c2 0x11b9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101799) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017a1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017ab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 58), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017b0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 58), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017b5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 62), (7, 58), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017b8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 4), (5, 5), (6, 62), (7, 58), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017bb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 62), (7, 58), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017be) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 4), (5, 5), (6, 62), (7, 58), (8, 68), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017c2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 70), (5, 5), (6, 62), (7, 58), (8, 68), (9, 60), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102980) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 72) (by decide) (by decide) rfl rfl

theorem block_l101794 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101794 :=
  Rest.liftedBlock (rest_l101794 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101794 x hx)

theorem rest_l1017c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1017c7 bytes_l1017c7) (entryMap (live .l1017c7))
      3 0x1017c7 bytes_l1017c7 b_l1017c7 := by
  have f0 : InstrSpec 0x1017c7 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1017c7) (movR32Imm32Effect 0x1017c7 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1017c7 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1017c7 0xb8 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x1017cc [0x80, 0x7C, 0x24, 0x0F, 0x00] (LoadPre 0x1017cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1017cc + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1017cc 5 (.sib 4 none 0 (.d8 0xf)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1017cc 5 (.sib 4 none 0 (.d8 0xf)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x1017cc (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017cc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017d1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1017d1 5 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1017c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1017c7 :=
  Rest.liftedBlock (rest_l1017c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1017c7 x hx)

theorem rest_l1017d3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1017d3 bytes_l1017d3) (entryMap (live .l1017d3))
      5 0x1017d3 bytes_l1017d3 b_l1017d3 := by
  have f0 : InstrSpec 0x1017d3 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1017d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1017d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1017d3 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017d3 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1017d3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1017d8 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1017d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1017d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1017d8 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1017d8 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1017d8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1017dd [0x4A, 0x89, 0x4C, 0x33, 0x08] (StorePre 0x1017dd 5 (fun s => AddrMode.addr (.sib 3 (some 14) 0 (.d8 0x8)) s (0x1017dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017dd 1 (.sib 3 (some 14) 0 (.d8 0x8)))
      [.gpr 1, .gpr 3, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017dd 1 (.sib 3 (some 14) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1017dd 0x4a (by decide) 1 (.sib 3 (some 14) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1017e2 [0x4A, 0x89, 0x04, 0x33] (StorePre 0x1017e2 4 (fun s => AddrMode.addr (.sib 3 (some 14) 0 .none) s (0x1017e2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1017e2 0 (.sib 3 (some 14) 0 .none))
      [.gpr 0, .gpr 3, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017e2 0 (.sib 3 (some 14) 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1017e2 0x4a (by decide) 0 (.sib 3 (some 14) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1017e6 [0x31, 0xC0] (fun s => s.RIP = 0x1017e6) (xorR32R32Effect 0x1017e6 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1017e6 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1017e6 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017dd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017e8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l1017d3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1017d3 :=
  Rest.liftedBlock (rest_l1017d3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1017d3 x hx)

theorem rest_l1017e8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1017e8 bytes_l1017e8) (entryMap (live .l1017e8))
      8 0x1017e8 bytes_l1017e8 b_l1017e8 := by
  have f0 : InstrSpec 0x1017e8 [0x48, 0x81, 0xC4, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x1017e8) (addR64Imm32Effect 0x1017e8 4 0x228)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1017e8 4 0x228).toInstrSpec (add_r64_imm32_effect_step 0x1017e8 0x48 0xc4 0x228 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1017ef [0x5B] (PopPre 0x1017ef) (popR64Effect 0x1017ef 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1017ef 1 3).toInstrSpec (pop_r64_effect_step 0x1017ef 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1017f0 [0x41, 0x5C] (PopPre 0x1017f0) (popR64Effect 0x1017f0 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1017f0 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1017f0 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1017f2 [0x41, 0x5D] (PopPre 0x1017f2) (popR64Effect 0x1017f2 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1017f2 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1017f2 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1017f4 [0x41, 0x5E] (PopPre 0x1017f4) (popR64Effect 0x1017f4 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1017f4 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1017f4 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1017f6 [0x41, 0x5F] (PopPre 0x1017f6) (popR64Effect 0x1017f6 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1017f6 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1017f6 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1017f8 [0x5D] (PopPre 0x1017f8) (popR64Effect 0x1017f8 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1017f8 1 5).toInstrSpec (pop_r64_effect_step 0x1017f8 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1017f9 [0xC3] (RetPre 0x1017f9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1017f9).toInstrSpec (ret_effect_step 0x1017f9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017ef) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l1017e8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1017e8 :=
  Rest.liftedBlock (rest_l1017e8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1017e8 x hx)

theorem rest_l102040 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102040 bytes_l102040) (entryMap (live .l102040))
      10 0x102040 bytes_l102040 b_l102040 := by
  have f0 : InstrSpec 0x102040 [0x41, 0x56] (PushPre 0x102040 2) (pushR64Effect 0x102040 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102040 2 14).toInstrSpec (push_r64_rex_effect_step 0x102040 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102042 [0x53] (PushPre 0x102042 1) (pushR64Effect 0x102042 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102042 1 3).toInstrSpec (push_r64_effect_step 0x102042 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102043 [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x102043) (subR64Imm8Effect 0x102043 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x102043 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x102043 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102047 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x102047) (movR64R64Effect 0x102047 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102047 14 6).toInstrSpec (mov_r64_r64_effect_step 0x102047 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10204a [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10204a) (movR64R64Effect 0x10204a 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10204a 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10204a 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10204d [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10204d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10204d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10204d (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10204d (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10204d 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x102056 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102056 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102056 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102056 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102056 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102056 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10205f [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x10205f) (movR64R64Effect 0x10205f 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10205f 7 4).toInstrSpec (mov_r64_r64_effect_step 0x10205f 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102062 [0x48, 0x8D, 0x54, 0x24, 0x18] (fun s => s.RIP = 0x102062) (leaR64Effect 0x102062 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102062 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x102062 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102067 [0xE8, 0x94, 0x30, 0x00, 0x00] (PushPre 0x102067 5) (callEffect (fun _ => 0x105100) 0x10206c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102067 0x105100 0x10206c).toInstrSpec (call_rel32_effect_step 0x102067 0x3094 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102042) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102043) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102047) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10204a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10204d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102056) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10205f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 65), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102062) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 67), (3, 61), (4, 57), (5, 5), (6, 6), (7, 65), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102067) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 67), (3, 61), (4, 69), (5, 5), (6, 6), (7, 65), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105100) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l102040 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102040 :=
  Rest.liftedBlock (rest_l102040 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102040 x hx)

theorem rest_l10206c_3 [Bindings] (code : CodeMap) :
    Rest (n := 171) code lifted (codeRange 0x10206c bytes_l10206c) [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 167), (7, 169), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x102157 bytes_l10206c_3 b_l10206c_3 := by
  have f60 : InstrSpec 0x102157 [0xE8, 0x24, 0x0A, 0x00, 0x00] (PushPre 0x102157 5) (callEffect (fun _ => 0x102b80) 0x10215c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102157 0x102b80 0x10215c).toInstrSpec (call_rel32_effect_step 0x102157 0xa24 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f60 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 171), (5, 5), (6, 167), (7, 169), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b80) f60 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 173) (by decide) (by decide) rfl rfl

theorem rest_l10206c_2 [Bindings] (code : CodeMap) :
    Rest (n := 133) code lifted (codeRange 0x10206c bytes_l10206c) [(0, 53), (1, 95), (2, 129), (3, 3), (4, 4), (5, 5), (6, 99), (7, 131), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      21 0x10210b bytes_l10206c_2 b_l10206c_2 := by
  have f40 : InstrSpec 0x10210b [0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x10210b) (shlR32Effect 0x10210b 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10210b 3 7 8).toInstrSpec (shl_r32_imm8_effect_step 0x10210b 0xe7 0x8 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10210e [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x10210e) (orR64R64Effect 0x10210e 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10210e 2 7).toInstrSpec (or_r64_r64_effect_step 0x10210e 0x48 0xfa (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x102111 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x102111) (movR64R64Effect 0x102111 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102111 7 0).toInstrSpec (mov_r64_r64_effect_step 0x102111 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x102114 [0x48, 0xC1, 0xE7, 0x38] (fun s => s.RIP = 0x102114) (shlR64Effect 0x102114 4 7 56)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x102114 4 7 56).toInstrSpec (shl_r64_imm8_effect_step 0x102114 0x48 0xe7 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x102118 [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x102118) (orR64R64Effect 0x102118 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102118 1 7).toInstrSpec (or_r64_r64_effect_step 0x102118 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10211b [0x48, 0x0F, 0xA4, 0xF1, 0x01] (fun s => s.RIP = 0x10211b) (shldR64R64Effect 0x10211b 5 1 6 1)
      [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10211b 5 1 6 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10211b 0x48 (by decide) 0xf1 (by decide) 0x1) pre_rip
  have f46 : InstrSpec 0x102120 [0xC1, 0xE8, 0x07] (fun s => s.RIP = 0x102120) (shrR32Effect 0x102120 3 0 7)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x102120 3 0 7).toInstrSpec (shr_r32_imm8_effect_step 0x102120 0xe8 0x7 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x102123 [0x48, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80] (fun s => s.RIP = 0x102123) (movR64Imm64Effect 0x102123 6 0x8000000000000000)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x102123 6 0x8000000000000000).toInstrSpec (mov_r64_imm64_effect_step 0x102123 0x48 0xbe (by decide) (by decide) 0x8000000000000000) pre_rip
  have f48 : InstrSpec 0x10212d [0x48, 0x21, 0xFE] (fun s => s.RIP = 0x10212d) (andR64R64Effect 0x10212d 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10212d 6 7).toInstrSpec (and_r64_r64_effect_step 0x10212d 0x48 0xfe (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x102130 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x102130) (movR64R64Effect 0x102130 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102130 7 0).toInstrSpec (mov_r64_r64_effect_step 0x102130 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x102133 [0x48, 0xC1, 0xE7, 0x3E] (fun s => s.RIP = 0x102133) (shlR64Effect 0x102133 4 7 62)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x102133 4 7 62).toInstrSpec (shl_r64_imm8_effect_step 0x102133 0x48 0xe7 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x102137 [0x48, 0x09, 0xF7] (fun s => s.RIP = 0x102137) (orR64R64Effect 0x102137 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102137 7 6).toInstrSpec (or_r64_r64_effect_step 0x102137 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10213a [0x48, 0x8D, 0x14, 0x50] (fun s => s.RIP = 0x10213a) (leaR64Effect 0x10213a 2 (.sib 0 (some 2) 1 .none))
      [.gpr 0, .gpr 2] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x10213a 2 (.sib 0 (some 2) 1 .none)).toInstrSpec (lea_r64_effect_step 0x10213a 0x48 (by decide) 2 (.sib 0 (some 2) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10213e [0x48, 0xC1, 0xE0, 0x39] (fun s => s.RIP = 0x10213e) (shlR64Effect 0x10213e 4 0 57)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10213e 4 0 57).toInstrSpec (shl_r64_imm8_effect_step 0x10213e 0x48 0xe0 0x39 (by decide) (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x102142 [0x48, 0x09, 0xF8] (fun s => s.RIP = 0x102142) (orR64R64Effect 0x102142 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102142 0 7).toInstrSpec (or_r64_r64_effect_step 0x102142 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x102145 [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x102145) (xorR64R64Effect 0x102145 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102145 0 1).toInstrSpec (xor_r64_r64_effect_step 0x102145 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x102148 [0x48, 0x89, 0x14, 0x24] (StorePre 0x102148 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102148 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102148 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102148 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102148 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x10214c [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10214c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10214c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10214c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10214c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10214c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x102151 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x102151) (movR64R64Effect 0x102151 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102151 6 4).toInstrSpec (mov_r64_r64_effect_step 0x102151 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x102154 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x102154) (movR64R64Effect 0x102154 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102154 7 3).toInstrSpec (mov_r64_r64_effect_step 0x102154 0x48 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f40 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 53), (1, 95), (2, 129), (3, 3), (4, 4), (5, 5), (6, 99), (7, 133), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10210e) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 53), (1, 95), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 133), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102111) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 53), (1, 95), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 137), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102114) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f43 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 53), (1, 95), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102118) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f44 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 53), (1, 141), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10211b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 53), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102120) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f46 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102123) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f47 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 147), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10212d) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f48 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 149), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102130) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f49 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 149), (7, 151), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102133) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f50 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 149), (7, 153), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102137) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f51 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10213a) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f52 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 145), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10213e) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 159), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102142) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f54 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 161), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102145) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f55 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102148) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.exec (n := 165) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10214c) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 166) (RestInside.exec (n := 166) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102151) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f58 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 167), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102154) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f59 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 167), (7, 169), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102157) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10206c_3 code

theorem rest_l10206c_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10206c bytes_l10206c) [(0, 53), (1, 91), (2, 79), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      41 0x1020bd bytes_l10206c_1 b_l10206c_1 := by
  have f20 : InstrSpec 0x1020bd [0x0F, 0xB6, 0x54, 0x24, 0x09] (LoadPre 0x1020bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x1020bd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020bd 5 2 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1020bd 5 2 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x1020bd 2 (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1020c2 [0x4C, 0x09, 0xC1] (fun s => s.RIP = 0x1020c2) (orR64R64Effect 0x1020c2 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020c2 1 8).toInstrSpec (or_r64_r64_effect_step 0x1020c2 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1020c5 [0x0F, 0xB6, 0x7C, 0x24, 0x0A] (LoadPre 0x1020c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1020c5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020c5 5 7 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1020c5 5 7 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m8_effect_step 0x1020c5 7 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x1020ca [0x48, 0xC1, 0xE6, 0x38] (fun s => s.RIP = 0x1020ca) (shlR64Effect 0x1020ca 4 6 56)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x1020ca 4 6 56).toInstrSpec (shl_r64_imm8_effect_step 0x1020ca 0x48 0xe6 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1020ce [0x48, 0xC1, 0xE2, 0x30] (fun s => s.RIP = 0x1020ce) (shlR64Effect 0x1020ce 4 2 48)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64Effect_footprint 0x1020ce 4 2 48).toInstrSpec (shl_r64_imm8_effect_step 0x1020ce 0x48 0xe2 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1020d2 [0x48, 0xC1, 0xE7, 0x28] (fun s => s.RIP = 0x1020d2) (shlR64Effect 0x1020d2 4 7 40)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x1020d2 4 7 40).toInstrSpec (shl_r64_imm8_effect_step 0x1020d2 0x48 0xe7 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1020d6 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x1020d6) (orR64R64Effect 0x1020d6 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020d6 2 6).toInstrSpec (or_r64_r64_effect_step 0x1020d6 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1020d9 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x1020d9) (orR64R64Effect 0x1020d9 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020d9 2 7).toInstrSpec (or_r64_r64_effect_step 0x1020d9 0x48 0xfa (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1020dc [0x0F, 0xB6, 0x7C, 0x24, 0x0B] (LoadPre 0x1020dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1020dc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020dc 5 7 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1020dc 5 7 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_effect_step 0x1020dc 7 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x1020e1 [0x48, 0xC1, 0xE7, 0x20] (fun s => s.RIP = 0x1020e1) (shlR64Effect 0x1020e1 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x1020e1 4 7 32).toInstrSpec (shl_r64_imm8_effect_step 0x1020e1 0x48 0xe7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1020e5 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x1020e5) (orR64R64Effect 0x1020e5 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020e5 2 7).toInstrSpec (or_r64_r64_effect_step 0x1020e5 0x48 0xfa (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x1020e8 [0x0F, 0xB6, 0x7C, 0x24, 0x0C] (LoadPre 0x1020e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1020e8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020e8 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1020e8 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x1020e8 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x1020ed [0xC1, 0xE7, 0x18] (fun s => s.RIP = 0x1020ed) (shlR32Effect 0x1020ed 3 7 24)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x1020ed 3 7 24).toInstrSpec (shl_r32_imm8_effect_step 0x1020ed 0xe7 0x18 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x1020f0 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x1020f0) (orR64R64Effect 0x1020f0 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020f0 2 7).toInstrSpec (or_r64_r64_effect_step 0x1020f0 0x48 0xfa (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1020f3 [0x0F, 0xB6, 0x7C, 0x24, 0x0D] (LoadPre 0x1020f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1020f3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020f3 5 7 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1020f3 5 7 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_effect_step 0x1020f3 7 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x1020f8 [0xC1, 0xE7, 0x10] (fun s => s.RIP = 0x1020f8) (shlR32Effect 0x1020f8 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x1020f8 3 7 16).toInstrSpec (shl_r32_imm8_effect_step 0x1020f8 0xe7 0x10 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x1020fb [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x1020fb) (orR64R64Effect 0x1020fb 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020fb 2 7).toInstrSpec (or_r64_r64_effect_step 0x1020fb 0x48 0xfa (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x1020fe [0x0F, 0xB6, 0x7C, 0x24, 0x0F] (LoadPre 0x1020fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1020fe + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020fe 5 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1020fe 5 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x1020fe 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x102103 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x102103) (orR64R64Effect 0x102103 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102103 2 7).toInstrSpec (or_r64_r64_effect_step 0x102103 0x48 0xfa (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x102106 [0x0F, 0xB6, 0x7C, 0x24, 0x0E] (LoadPre 0x102106 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x102106 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102106 5 7 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x102106 5 7 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x102106 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 53), (1, 91), (2, 93), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020c2) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 53), (1, 95), (2, 93), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020c5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 53), (1, 95), (2, 93), (3, 3), (4, 4), (5, 5), (6, 87), (7, 97), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020ca) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 53), (1, 95), (2, 93), (3, 3), (4, 4), (5, 5), (6, 99), (7, 97), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020ce) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 53), (1, 95), (2, 101), (3, 3), (4, 4), (5, 5), (6, 99), (7, 97), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020d2) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 53), (1, 95), (2, 101), (3, 3), (4, 4), (5, 5), (6, 99), (7, 103), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020d6) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 53), (1, 95), (2, 105), (3, 3), (4, 4), (5, 5), (6, 99), (7, 103), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020d9) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 53), (1, 95), (2, 107), (3, 3), (4, 4), (5, 5), (6, 99), (7, 103), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020dc) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 53), (1, 95), (2, 107), (3, 3), (4, 4), (5, 5), (6, 99), (7, 109), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020e1) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 53), (1, 95), (2, 107), (3, 3), (4, 4), (5, 5), (6, 99), (7, 111), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020e5) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 53), (1, 95), (2, 113), (3, 3), (4, 4), (5, 5), (6, 99), (7, 111), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020e8) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 53), (1, 95), (2, 113), (3, 3), (4, 4), (5, 5), (6, 99), (7, 115), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020ed) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 53), (1, 95), (2, 113), (3, 3), (4, 4), (5, 5), (6, 99), (7, 117), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020f0) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 53), (1, 95), (2, 119), (3, 3), (4, 4), (5, 5), (6, 99), (7, 117), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020f3) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 53), (1, 95), (2, 119), (3, 3), (4, 4), (5, 5), (6, 99), (7, 121), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020f8) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 53), (1, 95), (2, 119), (3, 3), (4, 4), (5, 5), (6, 99), (7, 123), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020fb) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 53), (1, 95), (2, 125), (3, 3), (4, 4), (5, 5), (6, 99), (7, 123), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020fe) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 53), (1, 95), (2, 125), (3, 3), (4, 4), (5, 5), (6, 99), (7, 127), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102103) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 53), (1, 95), (2, 129), (3, 3), (4, 4), (5, 5), (6, 99), (7, 127), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102106) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 53), (1, 95), (2, 129), (3, 3), (4, 4), (5, 5), (6, 99), (7, 131), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10210b) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10206c_2 code

theorem rest_l10206c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10206c bytes_l10206c) (entryMap (live .l10206c))
      61 0x10206c bytes_l10206c b_l10206c := by
  have f0 : InstrSpec 0x10206c [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x10206c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10206c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10206c 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10206c 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x10206c 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102070 [0x0F, 0xB6, 0x7C, 0x24, 0x01] (LoadPre 0x102070 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1)) s (0x102070 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102070 5 7 (.sib 4 none 0 (.d8 0x1)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x102070 5 7 (.sib 4 none 0 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x102070 7 (.sib 4 none 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x102075 [0x0F, 0xB6, 0x4C, 0x24, 0x02] (LoadPre 0x102075 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x102075 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102075 5 1 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x102075 5 1 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m8_effect_step 0x102075 1 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10207a [0x0F, 0xB6, 0x74, 0x24, 0x03] (LoadPre 0x10207a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x10207a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10207a 5 6 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10207a 5 6 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (movzx_r32_m8_effect_step 0x10207a 6 (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10207f [0x0F, 0xB6, 0x54, 0x24, 0x04] (LoadPre 0x10207f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10207f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10207f 5 2 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x10207f 5 2 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (movzx_r32_m8_effect_step 0x10207f 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102084 [0x48, 0xC1, 0xE7, 0x30] (fun s => s.RIP = 0x102084) (shlR64Effect 0x102084 4 7 48)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x102084 4 7 48).toInstrSpec (shl_r64_imm8_effect_step 0x102084 0x48 0xe7 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102088 [0x48, 0xC1, 0xE1, 0x28] (fun s => s.RIP = 0x102088) (shlR64Effect 0x102088 4 1 40)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x102088 4 1 40).toInstrSpec (shl_r64_imm8_effect_step 0x102088 0x48 0xe1 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10208c [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x10208c) (orR64R64Effect 0x10208c 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10208c 1 7).toInstrSpec (or_r64_r64_effect_step 0x10208c 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10208f [0x0F, 0xB6, 0x7C, 0x24, 0x05] (LoadPre 0x10208f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x10208f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10208f 5 7 (.sib 4 none 0 (.d8 0x5)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10208f 5 7 (.sib 4 none 0 (.d8 0x5))).toInstrSpec (movzx_r32_m8_effect_step 0x10208f 7 (.sib 4 none 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x102094 [0x48, 0xC1, 0xE6, 0x20] (fun s => s.RIP = 0x102094) (shlR64Effect 0x102094 4 6 32)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x102094 4 6 32).toInstrSpec (shl_r64_imm8_effect_step 0x102094 0x48 0xe6 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x102098 [0x48, 0x09, 0xCE] (fun s => s.RIP = 0x102098) (orR64R64Effect 0x102098 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102098 6 1).toInstrSpec (or_r64_r64_effect_step 0x102098 0x48 0xce (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10209b [0x0F, 0xB6, 0x4C, 0x24, 0x06] (LoadPre 0x10209b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x10209b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10209b 5 1 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10209b 5 1 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m8_effect_step 0x10209b 1 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1020a0 [0xC1, 0xE2, 0x18] (fun s => s.RIP = 0x1020a0) (shlR32Effect 0x1020a0 3 2 24)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x1020a0 3 2 24).toInstrSpec (shl_r32_imm8_effect_step 0x1020a0 0xe2 0x18 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1020a3 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x1020a3) (orR64R64Effect 0x1020a3 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020a3 2 6).toInstrSpec (or_r64_r64_effect_step 0x1020a3 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1020a6 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x07] (LoadPre 0x1020a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1020a6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1020a6 6 8 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x1020a6 6 8 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1020a6 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1020ac [0xC1, 0xE7, 0x10] (fun s => s.RIP = 0x1020ac) (shlR32Effect 0x1020ac 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x1020ac 3 7 16).toInstrSpec (shl_r32_imm8_effect_step 0x1020ac 0xe7 0x10 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1020af [0x48, 0x09, 0xD7] (fun s => s.RIP = 0x1020af) (orR64R64Effect 0x1020af 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020af 7 2).toInstrSpec (or_r64_r64_effect_step 0x1020af 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1020b2 [0x0F, 0xB6, 0x74, 0x24, 0x08] (LoadPre 0x1020b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1020b2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020b2 5 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1020b2 5 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x1020b2 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1020b7 [0xC1, 0xE1, 0x08] (fun s => s.RIP = 0x1020b7) (shlR32Effect 0x1020b7 3 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1020b7 3 1 8).toInstrSpec (shl_r32_imm8_effect_step 0x1020b7 0xe1 0x8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1020ba [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x1020ba) (orR64R64Effect 0x1020ba 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1020ba 1 7).toInstrSpec (or_r64_r64_effect_step 0x1020ba 0x48 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102070) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102075) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10207a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10207f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102084) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102088) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10208c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10208f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102094) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 71), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102098) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10209b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020a0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 75), (2, 77), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020a3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020a6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020ac) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (7, 83), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020af) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020b2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020b7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 53), (1, 89), (2, 79), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020ba) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 53), (1, 91), (2, 79), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1020bd) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10206c_1 code

theorem block_l10206c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10206c :=
  Rest.liftedBlock (rest_l10206c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10206c x hx)

theorem rest_l10215c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10215c bytes_l10215c) (entryMap (live .l10215c))
      5 0x10215c bytes_l10215c b_l10215c := by
  have f0 : InstrSpec 0x10215c [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10215c) (movR64R64Effect 0x10215c 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10215c 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10215c 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10215f [0x48, 0x83, 0xC7, 0x20] (fun s => s.RIP = 0x10215f) (addR64Imm8Effect 0x10215f 7 0x20)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10215f 7 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10215f 0x48 0xc7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102163 [0xBA, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102163) (movR32Imm32Effect 0x102163 5 2 0xb0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x102163 5 2 0xb0).toInstrSpec (mov_r32_imm32_effect_step 0x102163 0xba (by decide) 0xb0) pre_rip
  have f3 : InstrSpec 0x102168 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x102168) (movR64R64Effect 0x102168 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102168 6 14).toInstrSpec (mov_r64_r64_effect_step 0x102168 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10216b [0xFF, 0x15, 0x97, 0xF0, 0x0F, 0x00] (GoesTo (CallMemPre 0x10216b (.rip 0xff097)) (callEffect (callMemPtr 0x10216b (.rip 0xff097)) (0x10216b + BitVec.ofNat 64 (callMemLen (.rip 0xff097)))) 0x103f00) (callEffect (callMemPtr 0x10216b (.rip 0xff097)) (0x10216b + BitVec.ofNat 64 (callMemLen (.rip 0xff097))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10216b (.rip 0xff097)).toInstrSpec (call_m64_effect_step 0x10216b (.rip 0xff097) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10215f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102163) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102168) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10216b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 61), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10215c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10215c :=
  Rest.liftedBlock (rest_l10215c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10215c x hx)

theorem rest_l102171 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102171 bytes_l102171) (entryMap (live .l102171))
      5 0x102171 bytes_l102171 b_l102171 := by
  have f0 : InstrSpec 0x102171 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x102171) (movR64R64Effect 0x102171 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102171 0 3).toInstrSpec (mov_r64_r64_effect_step 0x102171 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102174 [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x102174) (addR64Imm8Effect 0x102174 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x102174 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x102174 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102178 [0x5B] (PopPre 0x102178) (popR64Effect 0x102178 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102178 1 3).toInstrSpec (pop_r64_effect_step 0x102178 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102179 [0x41, 0x5E] (PopPre 0x102179) (popR64Effect 0x102179 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102179 2 14).toInstrSpec (pop_r64_rex_effect_step 0x102179 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10217b [0xC3] (RetPre 0x10217b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10217b).toInstrSpec (ret_effect_step 0x10217b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102174) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102178) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102179) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10217b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l102171 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102171 :=
  Rest.liftedBlock (rest_l102171 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102171 x hx)

theorem rest_l102180 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102180 bytes_l102180) (entryMap (live .l102180))
      10 0x102180 bytes_l102180 b_l102180 := by
  have f0 : InstrSpec 0x102180 [0x41, 0x56] (PushPre 0x102180 2) (pushR64Effect 0x102180 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102180 2 14).toInstrSpec (push_r64_rex_effect_step 0x102180 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102182 [0x53] (PushPre 0x102182 1) (pushR64Effect 0x102182 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102182 1 3).toInstrSpec (push_r64_effect_step 0x102182 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102183 [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x102183) (subR64Imm8Effect 0x102183 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x102183 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x102183 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102187 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x102187) (movR64R64Effect 0x102187 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102187 14 6).toInstrSpec (mov_r64_r64_effect_step 0x102187 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10218a [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10218a) (movR64R64Effect 0x10218a 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10218a 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10218a 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10218d [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10218d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10218d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10218d (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10218d (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10218d 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x102196 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102196 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102196 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102196 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102196 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102196 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10219f [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x10219f) (movR64R64Effect 0x10219f 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10219f 7 4).toInstrSpec (mov_r64_r64_effect_step 0x10219f 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1021a2 [0x48, 0x8D, 0x54, 0x24, 0x18] (fun s => s.RIP = 0x1021a2) (leaR64Effect 0x1021a2 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1021a2 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x1021a2 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1021a7 [0xE8, 0xB4, 0x47, 0x00, 0x00] (PushPre 0x1021a7 5) (callEffect (fun _ => 0x106960) 0x1021ac)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1021a7 0x106960 0x1021ac).toInstrSpec (call_rel32_effect_step 0x1021a7 0x47b4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102182) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102183) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102187) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10218a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10218d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102196) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10219f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 65), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021a2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 67), (3, 61), (4, 57), (5, 5), (6, 6), (7, 65), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021a7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 67), (3, 61), (4, 69), (5, 5), (6, 6), (7, 65), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106960) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l102180 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102180 :=
  Rest.liftedBlock (rest_l102180 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102180 x hx)

theorem rest_l1021ac_3 [Bindings] (code : CodeMap) :
    Rest (n := 171) code lifted (codeRange 0x1021ac bytes_l1021ac) [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 167), (7, 169), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x102297 bytes_l1021ac_3 b_l1021ac_3 := by
  have f60 : InstrSpec 0x102297 [0xE8, 0xE4, 0x08, 0x00, 0x00] (PushPre 0x102297 5) (callEffect (fun _ => 0x102b80) 0x10229c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102297 0x102b80 0x10229c).toInstrSpec (call_rel32_effect_step 0x102297 0x8e4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f60 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 171), (5, 5), (6, 167), (7, 169), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b80) f60 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 173) (by decide) (by decide) rfl rfl

theorem rest_l1021ac_2 [Bindings] (code : CodeMap) :
    Rest (n := 133) code lifted (codeRange 0x1021ac bytes_l1021ac) [(0, 53), (1, 95), (2, 129), (3, 3), (4, 4), (5, 5), (6, 99), (7, 131), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      21 0x10224b bytes_l1021ac_2 b_l1021ac_2 := by
  have f40 : InstrSpec 0x10224b [0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x10224b) (shlR32Effect 0x10224b 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10224b 3 7 8).toInstrSpec (shl_r32_imm8_effect_step 0x10224b 0xe7 0x8 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10224e [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x10224e) (orR64R64Effect 0x10224e 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10224e 2 7).toInstrSpec (or_r64_r64_effect_step 0x10224e 0x48 0xfa (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x102251 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x102251) (movR64R64Effect 0x102251 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102251 7 0).toInstrSpec (mov_r64_r64_effect_step 0x102251 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x102254 [0x48, 0xC1, 0xE7, 0x38] (fun s => s.RIP = 0x102254) (shlR64Effect 0x102254 4 7 56)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x102254 4 7 56).toInstrSpec (shl_r64_imm8_effect_step 0x102254 0x48 0xe7 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x102258 [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x102258) (orR64R64Effect 0x102258 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102258 1 7).toInstrSpec (or_r64_r64_effect_step 0x102258 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10225b [0x48, 0x0F, 0xA4, 0xF1, 0x01] (fun s => s.RIP = 0x10225b) (shldR64R64Effect 0x10225b 5 1 6 1)
      [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10225b 5 1 6 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10225b 0x48 (by decide) 0xf1 (by decide) 0x1) pre_rip
  have f46 : InstrSpec 0x102260 [0xC1, 0xE8, 0x07] (fun s => s.RIP = 0x102260) (shrR32Effect 0x102260 3 0 7)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x102260 3 0 7).toInstrSpec (shr_r32_imm8_effect_step 0x102260 0xe8 0x7 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x102263 [0x48, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80] (fun s => s.RIP = 0x102263) (movR64Imm64Effect 0x102263 6 0x8000000000000000)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x102263 6 0x8000000000000000).toInstrSpec (mov_r64_imm64_effect_step 0x102263 0x48 0xbe (by decide) (by decide) 0x8000000000000000) pre_rip
  have f48 : InstrSpec 0x10226d [0x48, 0x21, 0xFE] (fun s => s.RIP = 0x10226d) (andR64R64Effect 0x10226d 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10226d 6 7).toInstrSpec (and_r64_r64_effect_step 0x10226d 0x48 0xfe (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x102270 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x102270) (movR64R64Effect 0x102270 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102270 7 0).toInstrSpec (mov_r64_r64_effect_step 0x102270 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x102273 [0x48, 0xC1, 0xE7, 0x3E] (fun s => s.RIP = 0x102273) (shlR64Effect 0x102273 4 7 62)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x102273 4 7 62).toInstrSpec (shl_r64_imm8_effect_step 0x102273 0x48 0xe7 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x102277 [0x48, 0x09, 0xF7] (fun s => s.RIP = 0x102277) (orR64R64Effect 0x102277 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102277 7 6).toInstrSpec (or_r64_r64_effect_step 0x102277 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10227a [0x48, 0x8D, 0x14, 0x50] (fun s => s.RIP = 0x10227a) (leaR64Effect 0x10227a 2 (.sib 0 (some 2) 1 .none))
      [.gpr 0, .gpr 2] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x10227a 2 (.sib 0 (some 2) 1 .none)).toInstrSpec (lea_r64_effect_step 0x10227a 0x48 (by decide) 2 (.sib 0 (some 2) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10227e [0x48, 0xC1, 0xE0, 0x39] (fun s => s.RIP = 0x10227e) (shlR64Effect 0x10227e 4 0 57)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10227e 4 0 57).toInstrSpec (shl_r64_imm8_effect_step 0x10227e 0x48 0xe0 0x39 (by decide) (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x102282 [0x48, 0x09, 0xF8] (fun s => s.RIP = 0x102282) (orR64R64Effect 0x102282 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102282 0 7).toInstrSpec (or_r64_r64_effect_step 0x102282 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x102285 [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x102285) (xorR64R64Effect 0x102285 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102285 0 1).toInstrSpec (xor_r64_r64_effect_step 0x102285 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x102288 [0x48, 0x89, 0x14, 0x24] (StorePre 0x102288 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102288 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102288 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102288 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102288 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x10228c [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10228c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10228c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10228c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10228c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10228c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x102291 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x102291) (movR64R64Effect 0x102291 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102291 6 4).toInstrSpec (mov_r64_r64_effect_step 0x102291 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x102294 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x102294) (movR64R64Effect 0x102294 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102294 7 3).toInstrSpec (mov_r64_r64_effect_step 0x102294 0x48 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f40 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 53), (1, 95), (2, 129), (3, 3), (4, 4), (5, 5), (6, 99), (7, 133), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10224e) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 53), (1, 95), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 133), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102251) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 53), (1, 95), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 137), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102254) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f43 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 53), (1, 95), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102258) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f44 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 53), (1, 141), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10225b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 53), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102260) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f46 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 99), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102263) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f47 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 147), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10226d) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f48 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 149), (7, 139), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102270) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f49 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 149), (7, 151), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102273) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f50 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 149), (7, 153), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102277) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f51 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 145), (1, 143), (2, 135), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10227a) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f52 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 145), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10227e) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 159), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102282) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f54 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 161), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102285) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f55 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102288) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.exec (n := 165) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10228c) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 166) (RestInside.exec (n := 166) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 149), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102291) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f58 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 167), (7, 155), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102294) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f59 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 163), (1, 143), (2, 157), (3, 3), (4, 4), (5, 5), (6, 167), (7, 169), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102297) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1021ac_3 code

theorem rest_l1021ac_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x1021ac bytes_l1021ac) [(0, 53), (1, 91), (2, 79), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      41 0x1021fd bytes_l1021ac_1 b_l1021ac_1 := by
  have f20 : InstrSpec 0x1021fd [0x0F, 0xB6, 0x54, 0x24, 0x09] (LoadPre 0x1021fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x1021fd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021fd 5 2 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1021fd 5 2 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x1021fd 2 (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x102202 [0x4C, 0x09, 0xC1] (fun s => s.RIP = 0x102202) (orR64R64Effect 0x102202 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102202 1 8).toInstrSpec (or_r64_r64_effect_step 0x102202 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x102205 [0x0F, 0xB6, 0x7C, 0x24, 0x0A] (LoadPre 0x102205 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x102205 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102205 5 7 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x102205 5 7 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m8_effect_step 0x102205 7 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x10220a [0x48, 0xC1, 0xE6, 0x38] (fun s => s.RIP = 0x10220a) (shlR64Effect 0x10220a 4 6 56)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x10220a 4 6 56).toInstrSpec (shl_r64_imm8_effect_step 0x10220a 0x48 0xe6 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x10220e [0x48, 0xC1, 0xE2, 0x30] (fun s => s.RIP = 0x10220e) (shlR64Effect 0x10220e 4 2 48)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64Effect_footprint 0x10220e 4 2 48).toInstrSpec (shl_r64_imm8_effect_step 0x10220e 0x48 0xe2 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x102212 [0x48, 0xC1, 0xE7, 0x28] (fun s => s.RIP = 0x102212) (shlR64Effect 0x102212 4 7 40)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x102212 4 7 40).toInstrSpec (shl_r64_imm8_effect_step 0x102212 0x48 0xe7 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x102216 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x102216) (orR64R64Effect 0x102216 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102216 2 6).toInstrSpec (or_r64_r64_effect_step 0x102216 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x102219 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x102219) (orR64R64Effect 0x102219 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102219 2 7).toInstrSpec (or_r64_r64_effect_step 0x102219 0x48 0xfa (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10221c [0x0F, 0xB6, 0x7C, 0x24, 0x0B] (LoadPre 0x10221c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x10221c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10221c 5 7 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10221c 5 7 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_effect_step 0x10221c 7 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x102221 [0x48, 0xC1, 0xE7, 0x20] (fun s => s.RIP = 0x102221) (shlR64Effect 0x102221 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x102221 4 7 32).toInstrSpec (shl_r64_imm8_effect_step 0x102221 0x48 0xe7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x102225 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x102225) (orR64R64Effect 0x102225 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102225 2 7).toInstrSpec (or_r64_r64_effect_step 0x102225 0x48 0xfa (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x102228 [0x0F, 0xB6, 0x7C, 0x24, 0x0C] (LoadPre 0x102228 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x102228 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102228 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x102228 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x102228 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x10222d [0xC1, 0xE7, 0x18] (fun s => s.RIP = 0x10222d) (shlR32Effect 0x10222d 3 7 24)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10222d 3 7 24).toInstrSpec (shl_r32_imm8_effect_step 0x10222d 0xe7 0x18 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x102230 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x102230) (orR64R64Effect 0x102230 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102230 2 7).toInstrSpec (or_r64_r64_effect_step 0x102230 0x48 0xfa (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x102233 [0x0F, 0xB6, 0x7C, 0x24, 0x0D] (LoadPre 0x102233 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x102233 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102233 5 7 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x102233 5 7 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_effect_step 0x102233 7 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x102238 [0xC1, 0xE7, 0x10] (fun s => s.RIP = 0x102238) (shlR32Effect 0x102238 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x102238 3 7 16).toInstrSpec (shl_r32_imm8_effect_step 0x102238 0xe7 0x10 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10223b [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x10223b) (orR64R64Effect 0x10223b 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10223b 2 7).toInstrSpec (or_r64_r64_effect_step 0x10223b 0x48 0xfa (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10223e [0x0F, 0xB6, 0x7C, 0x24, 0x0F] (LoadPre 0x10223e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x10223e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10223e 5 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10223e 5 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x10223e 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x102243 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x102243) (orR64R64Effect 0x102243 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102243 2 7).toInstrSpec (or_r64_r64_effect_step 0x102243 0x48 0xfa (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x102246 [0x0F, 0xB6, 0x7C, 0x24, 0x0E] (LoadPre 0x102246 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x102246 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102246 5 7 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x102246 5 7 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x102246 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 53), (1, 91), (2, 93), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102202) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 53), (1, 95), (2, 93), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102205) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 53), (1, 95), (2, 93), (3, 3), (4, 4), (5, 5), (6, 87), (7, 97), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10220a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 53), (1, 95), (2, 93), (3, 3), (4, 4), (5, 5), (6, 99), (7, 97), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10220e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 53), (1, 95), (2, 101), (3, 3), (4, 4), (5, 5), (6, 99), (7, 97), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102212) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 53), (1, 95), (2, 101), (3, 3), (4, 4), (5, 5), (6, 99), (7, 103), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102216) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 53), (1, 95), (2, 105), (3, 3), (4, 4), (5, 5), (6, 99), (7, 103), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102219) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 53), (1, 95), (2, 107), (3, 3), (4, 4), (5, 5), (6, 99), (7, 103), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10221c) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 53), (1, 95), (2, 107), (3, 3), (4, 4), (5, 5), (6, 99), (7, 109), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102221) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 53), (1, 95), (2, 107), (3, 3), (4, 4), (5, 5), (6, 99), (7, 111), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102225) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 53), (1, 95), (2, 113), (3, 3), (4, 4), (5, 5), (6, 99), (7, 111), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102228) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 53), (1, 95), (2, 113), (3, 3), (4, 4), (5, 5), (6, 99), (7, 115), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10222d) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 53), (1, 95), (2, 113), (3, 3), (4, 4), (5, 5), (6, 99), (7, 117), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102230) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 53), (1, 95), (2, 119), (3, 3), (4, 4), (5, 5), (6, 99), (7, 117), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102233) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 53), (1, 95), (2, 119), (3, 3), (4, 4), (5, 5), (6, 99), (7, 121), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102238) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 53), (1, 95), (2, 119), (3, 3), (4, 4), (5, 5), (6, 99), (7, 123), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10223b) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 53), (1, 95), (2, 125), (3, 3), (4, 4), (5, 5), (6, 99), (7, 123), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10223e) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 53), (1, 95), (2, 125), (3, 3), (4, 4), (5, 5), (6, 99), (7, 127), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102243) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 53), (1, 95), (2, 129), (3, 3), (4, 4), (5, 5), (6, 99), (7, 127), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102246) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 53), (1, 95), (2, 129), (3, 3), (4, 4), (5, 5), (6, 99), (7, 131), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10224b) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1021ac_2 code

theorem rest_l1021ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1021ac bytes_l1021ac) (entryMap (live .l1021ac))
      61 0x1021ac bytes_l1021ac b_l1021ac := by
  have f0 : InstrSpec 0x1021ac [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x1021ac (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1021ac + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1021ac 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1021ac 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x1021ac 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1021b0 [0x0F, 0xB6, 0x7C, 0x24, 0x01] (LoadPre 0x1021b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1)) s (0x1021b0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021b0 5 7 (.sib 4 none 0 (.d8 0x1)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1021b0 5 7 (.sib 4 none 0 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x1021b0 7 (.sib 4 none 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1021b5 [0x0F, 0xB6, 0x4C, 0x24, 0x02] (LoadPre 0x1021b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1021b5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021b5 5 1 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1021b5 5 1 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m8_effect_step 0x1021b5 1 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1021ba [0x0F, 0xB6, 0x74, 0x24, 0x03] (LoadPre 0x1021ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x1021ba + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021ba 5 6 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1021ba 5 6 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (movzx_r32_m8_effect_step 0x1021ba 6 (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1021bf [0x0F, 0xB6, 0x54, 0x24, 0x04] (LoadPre 0x1021bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1021bf + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021bf 5 2 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1021bf 5 2 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (movzx_r32_m8_effect_step 0x1021bf 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1021c4 [0x48, 0xC1, 0xE7, 0x30] (fun s => s.RIP = 0x1021c4) (shlR64Effect 0x1021c4 4 7 48)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x1021c4 4 7 48).toInstrSpec (shl_r64_imm8_effect_step 0x1021c4 0x48 0xe7 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1021c8 [0x48, 0xC1, 0xE1, 0x28] (fun s => s.RIP = 0x1021c8) (shlR64Effect 0x1021c8 4 1 40)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x1021c8 4 1 40).toInstrSpec (shl_r64_imm8_effect_step 0x1021c8 0x48 0xe1 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1021cc [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x1021cc) (orR64R64Effect 0x1021cc 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1021cc 1 7).toInstrSpec (or_r64_r64_effect_step 0x1021cc 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1021cf [0x0F, 0xB6, 0x7C, 0x24, 0x05] (LoadPre 0x1021cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x1021cf + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021cf 5 7 (.sib 4 none 0 (.d8 0x5)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1021cf 5 7 (.sib 4 none 0 (.d8 0x5))).toInstrSpec (movzx_r32_m8_effect_step 0x1021cf 7 (.sib 4 none 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1021d4 [0x48, 0xC1, 0xE6, 0x20] (fun s => s.RIP = 0x1021d4) (shlR64Effect 0x1021d4 4 6 32)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x1021d4 4 6 32).toInstrSpec (shl_r64_imm8_effect_step 0x1021d4 0x48 0xe6 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1021d8 [0x48, 0x09, 0xCE] (fun s => s.RIP = 0x1021d8) (orR64R64Effect 0x1021d8 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1021d8 6 1).toInstrSpec (or_r64_r64_effect_step 0x1021d8 0x48 0xce (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1021db [0x0F, 0xB6, 0x4C, 0x24, 0x06] (LoadPre 0x1021db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1021db + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021db 5 1 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1021db 5 1 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m8_effect_step 0x1021db 1 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1021e0 [0xC1, 0xE2, 0x18] (fun s => s.RIP = 0x1021e0) (shlR32Effect 0x1021e0 3 2 24)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x1021e0 3 2 24).toInstrSpec (shl_r32_imm8_effect_step 0x1021e0 0xe2 0x18 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1021e3 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x1021e3) (orR64R64Effect 0x1021e3 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1021e3 2 6).toInstrSpec (or_r64_r64_effect_step 0x1021e3 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1021e6 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x07] (LoadPre 0x1021e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1021e6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1021e6 6 8 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x1021e6 6 8 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1021e6 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1021ec [0xC1, 0xE7, 0x10] (fun s => s.RIP = 0x1021ec) (shlR32Effect 0x1021ec 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x1021ec 3 7 16).toInstrSpec (shl_r32_imm8_effect_step 0x1021ec 0xe7 0x10 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1021ef [0x48, 0x09, 0xD7] (fun s => s.RIP = 0x1021ef) (orR64R64Effect 0x1021ef 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1021ef 7 2).toInstrSpec (or_r64_r64_effect_step 0x1021ef 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1021f2 [0x0F, 0xB6, 0x74, 0x24, 0x08] (LoadPre 0x1021f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1021f2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021f2 5 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1021f2 5 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x1021f2 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1021f7 [0xC1, 0xE1, 0x08] (fun s => s.RIP = 0x1021f7) (shlR32Effect 0x1021f7 3 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x1021f7 3 1 8).toInstrSpec (shl_r32_imm8_effect_step 0x1021f7 0xe1 0x8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1021fa [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x1021fa) (orR64R64Effect 0x1021fa 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1021fa 1 7).toInstrSpec (or_r64_r64_effect_step 0x1021fa 0x48 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021bf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021c4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021c8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021cc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021cf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021d4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 71), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021d8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021db) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021e0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 75), (2, 77), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021e3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021e6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021ec) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (7, 83), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021ef) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 73), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021f2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021f7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 53), (1, 89), (2, 79), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021fa) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 53), (1, 91), (2, 79), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1021fd) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1021ac_1 code

theorem block_l1021ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1021ac :=
  Rest.liftedBlock (rest_l1021ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1021ac x hx)

theorem rest_l10229c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10229c bytes_l10229c) (entryMap (live .l10229c))
      5 0x10229c bytes_l10229c b_l10229c := by
  have f0 : InstrSpec 0x10229c [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10229c) (movR64R64Effect 0x10229c 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10229c 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10229c 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10229f [0x48, 0x83, 0xC7, 0x20] (fun s => s.RIP = 0x10229f) (addR64Imm8Effect 0x10229f 7 0x20)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10229f 7 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10229f 0x48 0xc7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1022a3 [0xBA, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1022a3) (movR32Imm32Effect 0x1022a3 5 2 0xf0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1022a3 5 2 0xf0).toInstrSpec (mov_r32_imm32_effect_step 0x1022a3 0xba (by decide) 0xf0) pre_rip
  have f3 : InstrSpec 0x1022a8 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1022a8) (movR64R64Effect 0x1022a8 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1022a8 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1022a8 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1022ab [0xFF, 0x15, 0x57, 0xEF, 0x0F, 0x00] (GoesTo (CallMemPre 0x1022ab (.rip 0xfef57)) (callEffect (callMemPtr 0x1022ab (.rip 0xfef57)) (0x1022ab + BitVec.ofNat 64 (callMemLen (.rip 0xfef57)))) 0x103f00) (callEffect (callMemPtr 0x1022ab (.rip 0xfef57)) (0x1022ab + BitVec.ofNat 64 (callMemLen (.rip 0xfef57))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1022ab (.rip 0xfef57)).toInstrSpec (call_m64_effect_step 0x1022ab (.rip 0xfef57) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10229f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022a8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022ab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 61), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10229c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10229c :=
  Rest.liftedBlock (rest_l10229c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10229c x hx)

theorem rest_l1022b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1022b1 bytes_l1022b1) (entryMap (live .l1022b1))
      5 0x1022b1 bytes_l1022b1 b_l1022b1 := by
  have f0 : InstrSpec 0x1022b1 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1022b1) (movR64R64Effect 0x1022b1 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1022b1 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1022b1 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1022b4 [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x1022b4) (addR64Imm8Effect 0x1022b4 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1022b4 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x1022b4 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1022b8 [0x5B] (PopPre 0x1022b8) (popR64Effect 0x1022b8 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1022b8 1 3).toInstrSpec (pop_r64_effect_step 0x1022b8 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1022b9 [0x41, 0x5E] (PopPre 0x1022b9) (popR64Effect 0x1022b9 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1022b9 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1022b9 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1022bb [0xC3] (RetPre 0x1022bb) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1022bb).toInstrSpec (ret_effect_step 0x1022bb) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022b8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022b9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1022bb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l1022b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1022b1 :=
  Rest.liftedBlock (rest_l1022b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1022b1 x hx)

theorem rest_l102b80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b80 bytes_l102b80) (entryMap (live .l102b80))
      14 0x102b80 bytes_l102b80 b_l102b80 := by
  have f0 : InstrSpec 0x102b80 [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x102b80) (subR64Imm8Effect 0x102b80 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x102b80 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x102b80 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102b84 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x102b84) (movR64R64Effect 0x102b84 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102b84 0 7).toInstrSpec (mov_r64_r64_effect_step 0x102b84 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102b87 [0x48, 0x8B, 0x0E] (LoadPre 0x102b87 (fun s => AddrMode.addr (.base 6 .none) s (0x102b87 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102b87 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102b87 1 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x102b87 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102b8a [0x48, 0x8B, 0x56, 0x08] (LoadPre 0x102b8a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102b8a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102b8a 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x102b8a 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102b8a 0x48 (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x102b8e [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x102b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102b8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b8e 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b8e 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x102b8e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102b93 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x102b93 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102b93 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102b93 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b93 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102b93 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x102b97 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102b97 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102b97 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102b97 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102b97 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102b97 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x102ba0 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102ba0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102ba0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102ba0 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102ba0 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102ba0 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102ba9 [0x48, 0x89, 0x0F] (StorePre 0x102ba9 3 (fun s => AddrMode.addr (.base 7 .none) s (0x102ba9 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x102ba9 1 (.base 7 .none))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x102ba9 1 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102ba9 0x48 (by decide) 1 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x102bac [0x48, 0x89, 0x57, 0x08] (StorePre 0x102bac 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x102bac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102bac 2 (.base 7 (.d8 0x8)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x102bac 2 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x102bac 0x48 (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102bb0 [0x48, 0xC7, 0x47, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102bb0 8 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x102bb0 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x102bb0 (.base 7 (.d8 0x18)) 0x0)
      [.gpr 7] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102bb0 (.base 7 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102bb0 0x48 (by decide) (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x102bb8 [0x48, 0xC7, 0x47, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x102bb8 8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x102bb8 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x102bb8 (.base 7 (.d8 0x10)) 0x0)
      [.gpr 7] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102bb8 (.base 7 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x102bb8 0x48 (by decide) (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102bc0 [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x102bc0) (addR64Imm8Effect 0x102bc0 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x102bc0 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x102bc0 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x102bc4 [0xC3] (RetPre 0x102bc4) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102bc4).toInstrSpec (ret_effect_step 0x102bc4) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b84) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b87) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b8a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b8e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b93) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b97) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ba0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ba9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bac) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bb0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bb8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bc0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bc4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 73) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 72), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f13 (by decide) rfl rfl rfl (by decide)

theorem block_l102b80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b80 :=
  Rest.liftedBlock (rest_l102b80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b80 x hx)

theorem rest_l1034a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1034a0 bytes_l1034a0) (entryMap (live .l1034a0))
      6 0x1034a0 bytes_l1034a0 b_l1034a0 := by
  have f0 : InstrSpec 0x1034a0 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x1034a0) (movR64R64Effect 0x1034a0 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1034a0 0 7).toInstrSpec (mov_r64_r64_effect_step 0x1034a0 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1034a3 [0x48, 0x8B, 0x4E, 0x10] (LoadPre 0x1034a3 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1034a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034a3 1 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1034a3 1 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1034a3 0x48 (by decide) 1 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1034a7 [0x48, 0x8B, 0x56, 0x18] (LoadPre 0x1034a7 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1034a7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034a7 2 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1034a7 2 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1034a7 0x48 (by decide) 2 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1034ab [0x48, 0x89, 0x57, 0x08] (StorePre 0x1034ab 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1034ab + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1034ab 2 (.base 7 (.d8 0x8)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034ab 2 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1034ab 0x48 (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1034af [0x48, 0x89, 0x0F] (StorePre 0x1034af 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1034af + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1034af 1 (.base 7 .none))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034af 1 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1034af 0x48 (by decide) 1 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1034b2 [0xC3] (RetPre 0x1034b2) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1034b2).toInstrSpec (ret_effect_step 0x1034b2) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034af) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034b2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l1034a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1034a0 :=
  Rest.liftedBlock (rest_l1034a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1034a0 x hx)

theorem rest_l1034c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1034c0 bytes_l1034c0) (entryMap (live .l1034c0))
      4 0x1034c0 bytes_l1034c0 b_l1034c0 := by
  have f0 : InstrSpec 0x1034c0 [0x48, 0x8B, 0x06] (LoadPre 0x1034c0 (fun s => AddrMode.addr (.base 6 .none) s (0x1034c0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1034c0 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1034c0 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1034c0 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1034c3 [0x48, 0x8B, 0x56, 0x08] (LoadPre 0x1034c3 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1034c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034c3 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1034c3 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1034c3 0x48 (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1034c7 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x1034c7) (movR64R64Effect 0x1034c7 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1034c7 6 0).toInstrSpec (mov_r64_r64_effect_step 0x1034c7 0x48 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034ca) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1034ca 0xfffff701 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1034c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1034c0 :=
  Rest.liftedBlock (rest_l1034c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1034c0 x hx)

theorem rest_l1034d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1034d0 bytes_l1034d0) (entryMap (live .l1034d0))
      8 0x1034d0 bytes_l1034d0 b_l1034d0 := by
  have f0 : InstrSpec 0x1034d0 [0x41, 0x56] (PushPre 0x1034d0 2) (pushR64Effect 0x1034d0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1034d0 2 14).toInstrSpec (push_r64_rex_effect_step 0x1034d0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1034d2 [0x53] (PushPre 0x1034d2 1) (pushR64Effect 0x1034d2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1034d2 1 3).toInstrSpec (push_r64_effect_step 0x1034d2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1034d3 [0x50] (PushPre 0x1034d3 1) (pushR64Effect 0x1034d3 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1034d3 1 0).toInstrSpec (push_r64_effect_step 0x1034d3 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1034d4 [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x1034d4) (movR64R64Effect 0x1034d4 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1034d4 3 6).toInstrSpec (mov_r64_r64_effect_step 0x1034d4 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1034d7 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x1034d7) (movR64R64Effect 0x1034d7 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1034d7 14 7).toInstrSpec (mov_r64_r64_effect_step 0x1034d7 0x49 0xfe (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1034da [0x48, 0x8B, 0x36] (LoadPre 0x1034da (fun s => AddrMode.addr (.base 6 .none) s (0x1034da + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1034da 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1034da 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1034da 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1034dd [0x48, 0x8B, 0x53, 0x08] (LoadPre 0x1034dd (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1034dd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034dd 2 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1034dd 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1034dd 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1034e1 [0xE8, 0xEA, 0xF6, 0xFF, 0xFF] (PushPre 0x1034e1 5) (callEffect (fun _ => 0x102bd0) 0x1034e6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1034e1 0x102bd0 0x1034e6).toInstrSpec (call_rel32_effect_step 0x1034e1 0xfffff6ea (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034d3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034d4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034d7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034da) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (3, 59), (4, 57), (5, 5), (6, 63), (7, 7), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034dd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 65), (3, 59), (4, 57), (5, 5), (6, 63), (7, 7), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034e1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (2, 65), (3, 59), (4, 67), (5, 5), (6, 63), (7, 7), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l1034d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1034d0 :=
  Rest.liftedBlock (rest_l1034d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1034d0 x hx)

theorem rest_l1034e6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1034e6 bytes_l1034e6) (entryMap (live .l1034e6))
      4 0x1034e6 bytes_l1034e6 b_l1034e6 := by
  have f0 : InstrSpec 0x1034e6 [0x48, 0x8B, 0x73, 0x10] (LoadPre 0x1034e6 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1034e6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034e6 6 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1034e6 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1034e6 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1034ea [0x48, 0x8B, 0x53, 0x18] (LoadPre 0x1034ea (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1034ea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034ea 2 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1034ea 2 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1034ea 0x48 (by decide) 2 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1034ee [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1034ee) (movR64R64Effect 0x1034ee 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1034ee 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1034ee 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1034f1 [0xE8, 0xDA, 0xF6, 0xFF, 0xFF] (PushPre 0x1034f1 5) (callEffect (fun _ => 0x102bd0) 0x1034f6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1034f1 0x102bd0 0x1034f6).toInstrSpec (call_rel32_effect_step 0x1034f1 0xfffff6da (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034ee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034f1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1034e6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1034e6 :=
  Rest.liftedBlock (rest_l1034e6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1034e6 x hx)

theorem rest_l1034f6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1034f6 bytes_l1034f6) (entryMap (live .l1034f6))
      4 0x1034f6 bytes_l1034f6 b_l1034f6 := by
  have f0 : InstrSpec 0x1034f6 [0x48, 0x8B, 0x73, 0x20] (LoadPre 0x1034f6 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1034f6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034f6 6 (.base 3 (.d8 0x20)))
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1034f6 6 (.base 3 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1034f6 0x48 (by decide) 6 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1034fa [0x48, 0x8B, 0x53, 0x28] (LoadPre 0x1034fa (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1034fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034fa 2 (.base 3 (.d8 0x28)))
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1034fa 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1034fa 0x48 (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1034fe [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1034fe) (movR64R64Effect 0x1034fe 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1034fe 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1034fe 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103501 [0xE8, 0xCA, 0xF6, 0xFF, 0xFF] (PushPre 0x103501 5) (callEffect (fun _ => 0x102bd0) 0x103506)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103501 0x102bd0 0x103506).toInstrSpec (call_rel32_effect_step 0x103501 0xfffff6ca (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034fa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034fe) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103501) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1034f6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1034f6 :=
  Rest.liftedBlock (rest_l1034f6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1034f6 x hx)

theorem rest_l103506 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103506 bytes_l103506) (entryMap (live .l103506))
      7 0x103506 bytes_l103506 b_l103506 := by
  have f0 : InstrSpec 0x103506 [0x48, 0x8B, 0x73, 0x30] (LoadPre 0x103506 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x103506 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103506 6 (.base 3 (.d8 0x30)))
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103506 6 (.base 3 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x103506 0x48 (by decide) 6 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10350a [0x48, 0x8B, 0x53, 0x38] (LoadPre 0x10350a (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10350a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10350a 2 (.base 3 (.d8 0x38)))
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10350a 2 (.base 3 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10350a 0x48 (by decide) 2 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10350e [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10350e) (movR64R64Effect 0x10350e 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10350e 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10350e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103511 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x103511) (addR64Imm8Effect 0x103511 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x103511 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x103511 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103515 [0x5B] (PopPre 0x103515) (popR64Effect 0x103515 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103515 1 3).toInstrSpec (pop_r64_effect_step 0x103515 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103516 [0x41, 0x5E] (PopPre 0x103516) (popR64Effect 0x103516 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103516 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103516 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10350a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10350e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103511) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103515) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(2, 55), (3, 61), (4, 62), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103516) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(2, 55), (3, 61), (4, 65), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103518) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 67) (jmp_rel32_effect_step 0x103518 0xfffff6b3 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103506 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103506 :=
  Rest.liftedBlock (rest_l103506 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103506 x hx)

theorem rest_l103837 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103837 bytes_l103837) (entryMap (live .l103837))
      15 0x103837 bytes_l103837 b_l103837 := by
  have f0 : InstrSpec 0x103837 [0x55] (PushPre 0x103837 1) (pushR64Effect 0x103837 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103837 1 5).toInstrSpec (push_r64_effect_step 0x103837 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103838 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x103838) (movR64R64Effect 0x103838 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103838 5 4).toInstrSpec (mov_r64_r64_effect_step 0x103838 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10383b [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x10383b) (subR64Imm8Effect 0x10383b 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10383b 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x10383b 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10383f [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x10383f) (leaR64Effect 0x10383f 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10383f 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x10383f 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103843 [0x48, 0x89, 0x38] (StorePre 0x103843 3 (fun s => AddrMode.addr (.base 0 .none) s (0x103843 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x103843 7 (.base 0 .none))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x103843 7 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x103843 0x48 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x103846 [0x48, 0x8D, 0x4D, 0xF0] (fun s => s.RIP = 0x103846) (leaR64Effect 0x103846 1 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x103846 1 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x103846 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10384a [0x48, 0x89, 0x31] (StorePre 0x10384a 3 (fun s => AddrMode.addr (.base 1 .none) s (0x10384a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10384a 6 (.base 1 .none))
      [.gpr 6, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x10384a 6 (.base 1 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10384a 0x48 (by decide) 6 (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10384d [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x10384d) (leaR64Effect 0x10384d 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10384d 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x10384d 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103851 [0x48, 0x89, 0x0E] (StorePre 0x103851 3 (fun s => AddrMode.addr (.base 6 .none) s (0x103851 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x103851 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x103851 1 (.base 6 .none)).toInstrSpec (mov_m64_r64_effect_step 0x103851 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103854 [0x48, 0x8D, 0x0D, 0x45, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x103854) (leaR64Effect 0x103854 1 (.rip 0x545))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x103854 1 (.rip 0x545)).toInstrSpec (lea_r64_effect_step 0x103854 0x48 (by decide) 1 (.rip 0x545) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10385b [0x48, 0x89, 0x4E, 0x08] (StorePre 0x10385b 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10385b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10385b 1 (.base 6 (.d8 0x8)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x10385b 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10385b 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10385f [0x48, 0x89, 0x46, 0x10] (StorePre 0x10385f 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10385f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10385f 0 (.base 6 (.d8 0x10)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x10385f 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10385f 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103863 [0x48, 0x89, 0x4E, 0x18] (StorePre 0x103863 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x103863 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103863 1 (.base 6 (.d8 0x18)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x103863 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x103863 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x103867 [0x48, 0x8D, 0x3D, 0x30, 0xCF, 0x0F, 0x00] (fun s => s.RIP = 0x103867) (leaR64Effect 0x103867 7 (.rip 0xfcf30))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103867 7 (.rip 0xfcf30)).toInstrSpec (lea_r64_effect_step 0x103867 0x48 (by decide) 7 (.rip 0xfcf30) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10386e [0xFF, 0x15, 0x9C, 0xD9, 0x0F, 0x00] (GoesTo (CallMemPre 0x10386e (.rip 0xfd99c)) (callEffect (callMemPtr 0x10386e (.rip 0xfd99c)) (0x10386e + BitVec.ofNat 64 (callMemLen (.rip 0xfd99c)))) 0x103880) (callEffect (callMemPtr 0x10386e (.rip 0xfd99c)) (0x10386e + BitVec.ofNat 64 (callMemLen (.rip 0xfd99c))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10386e (.rip 0xfd99c)).toInstrSpec (call_m64_effect_step 0x10386e (.rip 0xfd99c) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103880
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x103838) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x10383b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x10383f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x103843) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x103846) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x10384a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x10384d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x103851) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 62), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x103854) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x10385b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x10385f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x103863) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 7)]) (p' := 0x103867) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 57), (5, 55), (6, 65), (7, 73)]) (p' := 0x10386e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 59), (1, 68), (2, 2), (4, 75), (5, 55), (6, 65), (7, 73)]) (p' := 0x103880) f14 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l103837 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103837 :=
  Rest.liftedBlock (rest_l103837 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103837 x hx)

theorem rest_l103874 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103874 bytes_l103874) (entryMap (live .l103874))
      2 0x103874 bytes_l103874 b_l103874 := by
  have f0 : InstrSpec 0x103874 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103874) (fun _ => nopEffect 0x103874 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103874 10).toInstrSpec (nop_m_effect_step 0x103874 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10387e [0x66, 0x90] (fun s => s.RIP = 0x10387e) (fun _ => nopEffect 0x10387e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10387e 2).toInstrSpec (nop_66_effect_step 0x10387e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x10387e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103880) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l103874 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103874 :=
  Rest.liftedBlock (rest_l103874 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103874 x hx)

theorem rest_l103880 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103880 bytes_l103880) (entryMap (live .l103880))
      11 0x103880 bytes_l103880 b_l103880 := by
  have f0 : InstrSpec 0x103880 [0x55] (PushPre 0x103880 1) (pushR64Effect 0x103880 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103880 1 5).toInstrSpec (push_r64_effect_step 0x103880 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103881 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x103881) (movR64R64Effect 0x103881 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103881 5 4).toInstrSpec (mov_r64_r64_effect_step 0x103881 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103884 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x103884) (subR64Imm8Effect 0x103884 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x103884 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x103884 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103888 [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x103888 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x103888 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103888 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103888 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x103888 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10388c [0x48, 0x89, 0x75, 0xF8] (StorePre 0x10388c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x10388c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10388c 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x10388c 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x10388c 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x103890 [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x103890) (leaR64Effect 0x103890 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103890 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x103890 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103894 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x103894 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x103894 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103894 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103894 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x103894 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103898 [0x48, 0x89, 0x55, 0xE0] (StorePre 0x103898 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x103898 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103898 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103898 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x103898 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10389c [0x66, 0xC7, 0x45, 0xE8, 0x01, 0x00] (StorePre 0x10389c 6 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x10389c + BitVec.ofNat 64 6)) 2) (movM16Imm16Effect 0x10389c (.base 5 (.d8 0xe8)) 0x1)
      [.gpr 5] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x10389c (.base 5 (.d8 0xe8)) 0x1).toInstrSpec (mov_m16_imm16_effect_step 0x10389c (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1038a2 [0x48, 0x8D, 0x7D, 0xD8] (fun s => s.RIP = 0x1038a2) (leaR64Effect 0x1038a2 7 (.base 5 (.d8 0xd8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1038a2 7 (.base 5 (.d8 0xd8))).toInstrSpec (lea_r64_effect_step 0x1038a2 0x48 (by decide) 7 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1038a6 [0xFF, 0x15, 0x84, 0xD9, 0x0F, 0x00] (GoesTo (CallMemPre 0x1038a6 (.rip 0xfd984)) (callEffect (callMemPtr 0x1038a6 (.rip 0xfd984)) (0x1038a6 + BitVec.ofNat 64 (callMemLen (.rip 0xfd984)))) 0x101230) (callEffect (callMemPtr 0x1038a6 (.rip 0xfd984)) (0x1038a6 + BitVec.ofNat 64 (callMemLen (.rip 0xfd984))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1038a6 (.rip 0xfd984)).toInstrSpec (call_m64_effect_step 0x1038a6 (.rip 0xfd984) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x101230
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x103881) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x103884) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x103888) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x10388c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x103890) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x103894) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x103898) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x10389c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x1038a2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6)]) (p' := 0x1038a6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (2, 2), (5, 55), (6, 6)]) (p' := 0x101230) f10 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l103880 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103880 :=
  Rest.liftedBlock (rest_l103880 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103880 x hx)

theorem rest_l1038ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038ac bytes_l1038ac) (entryMap (live .l1038ac))
      1 0x1038ac bytes_l1038ac b_l1038ac := by
  have f0 : InstrSpec 0x1038ac [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x1038ac) (fun _ => nopEffect 0x1038ac 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1038ac 4).toInstrSpec (nop_m_effect_step 0x1038ac [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l1038ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038ac :=
  Rest.liftedBlock (rest_l1038ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038ac x hx)

theorem rest_l103c70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c70 bytes_l103c70) (entryMap (live .l103c70))
      5 0x103c70 bytes_l103c70 b_l103c70 := by
  have f0 : InstrSpec 0x103c70 [0x55] (PushPre 0x103c70 1) (pushR64Effect 0x103c70 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103c70 1 5).toInstrSpec (push_r64_effect_step 0x103c70 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103c71 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x103c71) (movR64R64Effect 0x103c71 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103c71 5 4).toInstrSpec (mov_r64_r64_effect_step 0x103c71 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103c74 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x103c74) (subR64Imm8Effect 0x103c74 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x103c74 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x103c74 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103c78 [0x48, 0x39, 0xD7] (fun s => s.RIP = 0x103c78) (cmpR64R64Effect 0x103c78 7 2)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103c78 7 2).toInstrSpec (cmp_r64_r64_effect_step 0x103c78 0x48 0xd7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x103c71) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x103c74) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x103c78) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (16, 59), (19, 60)]) (p' := 0x103c7b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x103c7b 6 0x3b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103c70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c70 :=
  Rest.liftedBlock (rest_l103c70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c70 x hx)

theorem rest_l103c7d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c7d bytes_l103c7d) (entryMap (live .l103c7d))
      13 0x103c7d bytes_l103c7d b_l103c7d := by
  have f0 : InstrSpec 0x103c7d [0x48, 0x89, 0x7D, 0xF8] (StorePre 0x103c7d 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x103c7d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c7d 7 (.base 5 (.d8 0xf8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c7d 7 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x103c7d 0x48 (by decide) 7 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103c81 [0x48, 0x89, 0x55, 0xF0] (StorePre 0x103c81 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x103c81 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c81 2 (.base 5 (.d8 0xf0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c81 2 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x103c81 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103c85 [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x103c85) (leaR64Effect 0x103c85 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103c85 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x103c85 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103c89 [0x48, 0x89, 0x45, 0xD0] (StorePre 0x103c89 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x103c89 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c89 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c89 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x103c89 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103c8d [0x48, 0x8D, 0x05, 0x0C, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x103c8d) (leaR64Effect 0x103c8d 0 (.rip 0x10c))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103c8d 0 (.rip 0x10c)).toInstrSpec (lea_r64_effect_step 0x103c8d 0x48 (by decide) 0 (.rip 0x10c) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103c94 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x103c94 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x103c94 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c94 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c94 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x103c94 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103c98 [0x48, 0x8D, 0x55, 0xF0] (fun s => s.RIP = 0x103c98) (leaR64Effect 0x103c98 2 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x103c98 2 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x103c98 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103c9c [0x48, 0x89, 0x55, 0xE0] (StorePre 0x103c9c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x103c9c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c9c 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c9c 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x103c9c 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103ca0 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x103ca0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x103ca0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ca0 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ca0 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x103ca0 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103ca4 [0x48, 0x8D, 0x3D, 0x49, 0xCC, 0x0F, 0x00] (fun s => s.RIP = 0x103ca4) (leaR64Effect 0x103ca4 7 (.rip 0xfcc49))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103ca4 7 (.rip 0xfcc49)).toInstrSpec (lea_r64_effect_step 0x103ca4 0x48 (by decide) 7 (.rip 0xfcc49) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103cab [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x103cab) (leaR64Effect 0x103cab 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103cab 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x103cab 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103caf [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x103caf) (movR64R64Effect 0x103caf 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103caf 2 1).toInstrSpec (mov_r64_r64_effect_step 0x103caf 0x48 0xca (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x103cb2 [0xFF, 0x15, 0x58, 0xD5, 0x0F, 0x00] (GoesTo (CallMemPre 0x103cb2 (.rip 0xfd558)) (callEffect (callMemPtr 0x103cb2 (.rip 0xfd558)) (0x103cb2 + BitVec.ofNat 64 (callMemLen (.rip 0xfd558)))) 0x103880) (callEffect (callMemPtr 0x103cb2 (.rip 0xfd558)) (0x103cb2 + BitVec.ofNat 64 (callMemLen (.rip 0xfd558))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x103cb2 (.rip 0xfd558)).toInstrSpec (call_m64_effect_step 0x103cb2 (.rip 0xfd558) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103880
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x103c81) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x103c85) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x103c89) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x103c8d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x103c94) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]) (p' := 0x103c98) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (7, 7)]) (p' := 0x103c9c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (7, 7)]) (p' := 0x103ca0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (7, 7)]) (p' := 0x103ca4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (7, 65)]) (p' := 0x103cab) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x103caf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x103cb2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)]) (p' := 0x103880) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l103c7d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c7d :=
  Rest.liftedBlock (rest_l103c7d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c7d x hx)

theorem rest_l103cb8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103cb8 bytes_l103cb8) (entryMap (live .l103cb8))
      2 0x103cb8 bytes_l103cb8 b_l103cb8 := by
  have f0 : InstrSpec 0x103cb8 [0x48, 0x39, 0xD6] (fun s => s.RIP = 0x103cb8) (cmpR64R64Effect 0x103cb8 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103cb8 6 2).toInstrSpec (cmp_r64_r64_effect_step 0x103cb8 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54)]) (p' := 0x103cbb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x103cbb 7 0x40) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103cb8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103cb8 :=
  Rest.liftedBlock (rest_l103cb8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103cb8 x hx)

theorem rest_l103cbd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103cbd bytes_l103cbd) (entryMap (live .l103cbd))
      2 0x103cbd bytes_l103cbd b_l103cbd := by
  have f0 : InstrSpec 0x103cbd [0x48, 0x39, 0xF7] (fun s => s.RIP = 0x103cbd) (cmpR64R64Effect 0x103cbd 7 6)
      [.gpr 7, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103cbd 7 6).toInstrSpec (cmp_r64_r64_effect_step 0x103cbd 0x48 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54)]) (p' := 0x103cc0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x103cc0 6 0x3b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103cbd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103cbd :=
  Rest.liftedBlock (rest_l103cbd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103cbd x hx)

theorem rest_l103cc2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103cc2 bytes_l103cc2) (entryMap (live .l103cc2))
      13 0x103cc2 bytes_l103cc2 b_l103cc2 := by
  have f0 : InstrSpec 0x103cc2 [0x48, 0x89, 0x7D, 0xF8] (StorePre 0x103cc2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x103cc2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cc2 7 (.base 5 (.d8 0xf8)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cc2 7 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x103cc2 0x48 (by decide) 7 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103cc6 [0x48, 0x89, 0x75, 0xF0] (StorePre 0x103cc6 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x103cc6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cc6 6 (.base 5 (.d8 0xf0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cc6 6 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x103cc6 0x48 (by decide) 6 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103cca [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x103cca) (leaR64Effect 0x103cca 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103cca 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x103cca 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103cce [0x48, 0x89, 0x45, 0xD0] (StorePre 0x103cce 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x103cce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cce 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cce 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x103cce 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103cd2 [0x48, 0x8D, 0x05, 0xC7, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103cd2) (leaR64Effect 0x103cd2 0 (.rip 0xc7))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103cd2 0 (.rip 0xc7)).toInstrSpec (lea_r64_effect_step 0x103cd2 0x48 (by decide) 0 (.rip 0xc7) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103cd9 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x103cd9 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x103cd9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cd9 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cd9 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x103cd9 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103cdd [0x48, 0x8D, 0x55, 0xF0] (fun s => s.RIP = 0x103cdd) (leaR64Effect 0x103cdd 2 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x103cdd 2 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x103cdd 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103ce1 [0x48, 0x89, 0x55, 0xE0] (StorePre 0x103ce1 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x103ce1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ce1 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ce1 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x103ce1 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103ce5 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x103ce5 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x103ce5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ce5 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ce5 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x103ce5 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103ce9 [0x48, 0x8D, 0x3D, 0xDC, 0xCB, 0x0F, 0x00] (fun s => s.RIP = 0x103ce9) (leaR64Effect 0x103ce9 7 (.rip 0xfcbdc))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103ce9 7 (.rip 0xfcbdc)).toInstrSpec (lea_r64_effect_step 0x103ce9 0x48 (by decide) 7 (.rip 0xfcbdc) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103cf0 [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x103cf0) (leaR64Effect 0x103cf0 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103cf0 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x103cf0 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103cf4 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x103cf4) (movR64R64Effect 0x103cf4 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103cf4 2 1).toInstrSpec (mov_r64_r64_effect_step 0x103cf4 0x48 0xca (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x103cf7 [0xFF, 0x15, 0x13, 0xD5, 0x0F, 0x00] (GoesTo (CallMemPre 0x103cf7 (.rip 0xfd513)) (callEffect (callMemPtr 0x103cf7 (.rip 0xfd513)) (0x103cf7 + BitVec.ofNat 64 (callMemLen (.rip 0xfd513)))) 0x103880) (callEffect (callMemPtr 0x103cf7 (.rip 0xfd513)) (0x103cf7 + BitVec.ofNat 64 (callMemLen (.rip 0xfd513))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x103cf7 (.rip 0xfd513)).toInstrSpec (call_m64_effect_step 0x103cf7 (.rip 0xfd513) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103880
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103cc6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103cca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103cce) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103cd2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103cd9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103cdd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103ce1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103ce5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x103ce9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 65)]) (p' := 0x103cf0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x103cf4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x103cf7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)]) (p' := 0x103880) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l103cc2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103cc2 :=
  Rest.liftedBlock (rest_l103cc2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103cc2 x hx)

theorem rest_l103cfd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103cfd bytes_l103cfd) (entryMap (live .l103cfd))
      13 0x103cfd bytes_l103cfd b_l103cfd := by
  have f0 : InstrSpec 0x103cfd [0x48, 0x89, 0x75, 0xF8] (StorePre 0x103cfd 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x103cfd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cfd 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cfd 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x103cfd 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103d01 [0x48, 0x89, 0x55, 0xF0] (StorePre 0x103d01 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x103d01 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d01 2 (.base 5 (.d8 0xf0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103d01 2 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x103d01 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103d05 [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x103d05) (leaR64Effect 0x103d05 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103d05 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x103d05 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103d09 [0x48, 0x89, 0x45, 0xD0] (StorePre 0x103d09 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x103d09 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d09 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103d09 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x103d09 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103d0d [0x48, 0x8D, 0x05, 0x8C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103d0d) (leaR64Effect 0x103d0d 0 (.rip 0x8c))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103d0d 0 (.rip 0x8c)).toInstrSpec (lea_r64_effect_step 0x103d0d 0x48 (by decide) 0 (.rip 0x8c) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103d14 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x103d14 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x103d14 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d14 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103d14 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x103d14 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103d18 [0x48, 0x8D, 0x55, 0xF0] (fun s => s.RIP = 0x103d18) (leaR64Effect 0x103d18 2 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x103d18 2 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x103d18 0x48 (by decide) 2 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103d1c [0x48, 0x89, 0x55, 0xE0] (StorePre 0x103d1c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x103d1c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d1c 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103d1c 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x103d1c 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103d20 [0x48, 0x89, 0x45, 0xE8] (StorePre 0x103d20 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x103d20 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d20 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103d20 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x103d20 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103d24 [0x48, 0x8D, 0x3D, 0x6A, 0xCB, 0x0F, 0x00] (fun s => s.RIP = 0x103d24) (leaR64Effect 0x103d24 7 (.rip 0xfcb6a))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103d24 7 (.rip 0xfcb6a)).toInstrSpec (lea_r64_effect_step 0x103d24 0x48 (by decide) 7 (.rip 0xfcb6a) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103d2b [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x103d2b) (leaR64Effect 0x103d2b 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103d2b 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x103d2b 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103d2f [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x103d2f) (movR64R64Effect 0x103d2f 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103d2f 2 1).toInstrSpec (mov_r64_r64_effect_step 0x103d2f 0x48 0xca (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x103d32 [0xFF, 0x15, 0xD8, 0xD4, 0x0F, 0x00] (GoesTo (CallMemPre 0x103d32 (.rip 0xfd4d8)) (callEffect (callMemPtr 0x103d32 (.rip 0xfd4d8)) (0x103d32 + BitVec.ofNat 64 (callMemLen (.rip 0xfd4d8)))) 0x103880) (callEffect (callMemPtr 0x103d32 (.rip 0xfd4d8)) (0x103d32 + BitVec.ofNat 64 (callMemLen (.rip 0xfd4d8))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x103d32 (.rip 0xfd4d8)).toInstrSpec (call_m64_effect_step 0x103d32 (.rip 0xfd4d8) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103880
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d01) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d09) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d0d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d14) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d18) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d1c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d20) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6)]) (p' := 0x103d24) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 65)]) (p' := 0x103d2b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 1), (2, 61), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x103d2f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 4), (5, 5), (6, 67), (7, 65)]) (p' := 0x103d32) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)]) (p' := 0x103880) f12 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l103cfd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103cfd :=
  Rest.liftedBlock (rest_l103cfd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103cfd x hx)

theorem rest_l103d38 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103d38 bytes_l103d38) (entryMap (live .l103d38))
      1 0x103d38 bytes_l103d38 b_l103d38 := by
  have f0 : InstrSpec 0x103d38 [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103d38) (fun _ => nopEffect 0x103d38 8)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103d38 8).toInstrSpec (nop_m_effect_step 0x103d38 [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d40) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l103d38 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103d38 :=
  Rest.liftedBlock (rest_l103d38 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103d38 x hx)

theorem rest_l103d40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103d40 bytes_l103d40) (entryMap (live .l103d40))
      12 0x103d40 bytes_l103d40 b_l103d40 := by
  have f0 : InstrSpec 0x103d40 [0x55] (PushPre 0x103d40 1) (pushR64Effect 0x103d40 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103d40 1 5).toInstrSpec (push_r64_effect_step 0x103d40 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103d41 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x103d41) (movR64R64Effect 0x103d41 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103d41 5 4).toInstrSpec (mov_r64_r64_effect_step 0x103d41 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103d44 [0x41, 0x57] (PushPre 0x103d44 2) (pushR64Effect 0x103d44 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103d44 2 15).toInstrSpec (push_r64_rex_effect_step 0x103d44 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103d46 [0x41, 0x56] (PushPre 0x103d46 2) (pushR64Effect 0x103d46 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103d46 2 14).toInstrSpec (push_r64_rex_effect_step 0x103d46 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103d48 [0x41, 0x54] (PushPre 0x103d48 2) (pushR64Effect 0x103d48 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103d48 2 12).toInstrSpec (push_r64_rex_effect_step 0x103d48 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103d4a [0x53] (PushPre 0x103d4a 1) (pushR64Effect 0x103d4a 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103d4a 1 3).toInstrSpec (push_r64_effect_step 0x103d4a 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x103d4b [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x103d4b) (movR64R64Effect 0x103d4b 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103d4b 3 8).toInstrSpec (mov_r64_r64_effect_step 0x103d4b 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103d4e [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x103d4e) (movR64R64Effect 0x103d4e 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103d4e 14 1).toInstrSpec (mov_r64_r64_effect_step 0x103d4e 0x49 0xce (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103d51 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x103d51) (movR64R64Effect 0x103d51 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x103d51 12 6).toInstrSpec (mov_r64_r64_effect_step 0x103d51 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103d54 [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x103d54) (movR64R64Effect 0x103d54 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x103d54 15 7).toInstrSpec (mov_r64_r64_effect_step 0x103d54 0x49 0xff (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103d57 [0x83, 0xFA, 0xFF] (fun s => s.RIP = 0x103d57) (cmpR32Imm8Effect 0x103d57 3 2 0xff)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103d57 3 2 0xff).toInstrSpec (cmp_r32_imm8_effect_step 0x103d57 0xfa 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d41) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d44) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d46) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d48) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d4a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d4b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d4e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d51) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 68), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d54) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d57) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d5a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 74) (jcc_rel8_effect_step 0x103d5a 4 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103d40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103d40 :=
  Rest.liftedBlock (rest_l103d40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103d40 x hx)

theorem rest_l103d5c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103d5c bytes_l103d5c) (entryMap (live .l103d5c))
      2 0x103d5c bytes_l103d5c b_l103d5c := by
  have f0 : InstrSpec 0x103d5c [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x103d5c) (movR64R64Effect 0x103d5c 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103d5c 7 15).toInstrSpec (mov_r64_r64_effect_step 0x103d5c 0x4c 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103d5f [0x89, 0xD6] (fun s => s.RIP = 0x103d5f) (movR32R32Effect 0x103d5f 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x103d5f 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x103d5f 0xd6 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (15, 15)]) (p' := 0x103d5f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (15, 15)]) (p' := 0x103d61) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l103d5c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103d5c :=
  Rest.liftedBlock (rest_l103d5c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103d5c x hx)

theorem rest_l103d66 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103d66 bytes_l103d66) (entryMap (live .l103d66))
      4 0x103d66 bytes_l103d66 b_l103d66 := by
  have f0 : InstrSpec 0x103d66 [0x89, 0xC1] (fun s => s.RIP = 0x103d66) (movR32R32Effect 0x103d66 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x103d66 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x103d66 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x103d68 [0xB0, 0x01] (fun s => s.RIP = 0x103d68) (movR8Imm8Effect 0x103d68 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x103d68 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x103d68 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x103d6a [0x84, 0xC9] (fun s => s.RIP = 0x103d6a) (testR8R8Effect 0x103d6a 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x103d6a 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x103d6a 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d68) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d6a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d6c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x103d6c 5 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103d66 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103d66 :=
  Rest.liftedBlock (rest_l103d66 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103d66 x hx)

theorem rest_l103d6e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103d6e bytes_l103d6e) (entryMap (live .l103d6e))
      2 0x103d6e bytes_l103d6e b_l103d6e := by
  have f0 : InstrSpec 0x103d6e [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x103d6e) (testR64R64Effect 0x103d6e 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103d6e 14 14).toInstrSpec (test_r64_r64_effect_step 0x103d6e 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d71) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103d71 4 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103d6e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103d6e :=
  Rest.liftedBlock (rest_l103d6e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103d6e x hx)

theorem rest_l103d73 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103d73 bytes_l103d73) (entryMap (live .l103d73))
      9 0x103d73 bytes_l103d73 b_l103d73 := by
  have f0 : InstrSpec 0x103d73 [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x103d73 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x103d73 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103d73 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103d73 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x103d73 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103d78 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x103d78) (movR64R64Effect 0x103d78 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103d78 7 15).toInstrSpec (mov_r64_r64_effect_step 0x103d78 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103d7b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x103d7b) (movR64R64Effect 0x103d7b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103d7b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x103d7b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103d7e [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x103d7e) (movR64R64Effect 0x103d7e 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103d7e 2 3).toInstrSpec (mov_r64_r64_effect_step 0x103d7e 0x48 0xda (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103d81 [0x5B] (PopPre 0x103d81) (popR64Effect 0x103d81 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d81 1 3).toInstrSpec (pop_r64_effect_step 0x103d81 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103d82 [0x41, 0x5C] (PopPre 0x103d82) (popR64Effect 0x103d82 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d82 2 12).toInstrSpec (pop_r64_rex_effect_step 0x103d82 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x103d84 [0x41, 0x5E] (PopPre 0x103d84) (popR64Effect 0x103d84 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d84 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103d84 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x103d86 [0x41, 0x5F] (PopPre 0x103d86) (popR64Effect 0x103d86 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d86 2 15).toInstrSpec (pop_r64_rex_effect_step 0x103d86 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x103d88 [0x5D] (PopPre 0x103d88) (popR64Effect 0x103d88 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d88 1 5).toInstrSpec (pop_r64_effect_step 0x103d88 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x103d78) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x103d7b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x103d7e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x103d81) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 57), (12, 12), (14, 14), (15, 15)]) (p' := 0x103d82) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 59), (14, 14), (15, 15)]) (p' := 0x103d84) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 61), (15, 15)]) (p' := 0x103d86) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(4, 63)]) (p' := 0x103d88) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := []) (p' := 0x103d89) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l103d73 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103d73 :=
  Rest.liftedBlock (rest_l103d73 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103d73 x hx)

theorem rest_l103d8b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103d8b bytes_l103d8b) (entryMap (live .l103d8b))
      1 0x103d8b bytes_l103d8b b_l103d8b := by
  have f0 : InstrSpec 0x103d8b [0x31, 0xC0] (fun s => s.RIP = 0x103d8b) (xorR32R32Effect 0x103d8b 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103d8b 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x103d8b 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d8d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l103d8b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103d8b :=
  Rest.liftedBlock (rest_l103d8b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103d8b x hx)

theorem rest_l103d8d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103d8d bytes_l103d8d) (entryMap (live .l103d8d))
      6 0x103d8d bytes_l103d8d b_l103d8d := by
  have f0 : InstrSpec 0x103d8d [0x5B] (PopPre 0x103d8d) (popR64Effect 0x103d8d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d8d 1 3).toInstrSpec (pop_r64_effect_step 0x103d8d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103d8e [0x41, 0x5C] (PopPre 0x103d8e) (popR64Effect 0x103d8e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d8e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x103d8e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103d90 [0x41, 0x5E] (PopPre 0x103d90) (popR64Effect 0x103d90 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d90 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103d90 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103d92 [0x41, 0x5F] (PopPre 0x103d92) (popR64Effect 0x103d92 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d92 2 15).toInstrSpec (pop_r64_rex_effect_step 0x103d92 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103d94 [0x5D] (PopPre 0x103d94) (popR64Effect 0x103d94 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103d94 1 5).toInstrSpec (pop_r64_effect_step 0x103d94 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103d95 [0xC3] (RetPre 0x103d95) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103d95).toInstrSpec (ret_effect_step 0x103d95) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 54), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d8e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 57), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d90) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d92) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 63), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d94) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 66), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d95) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l103d8d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103d8d :=
  Rest.liftedBlock (rest_l103d8d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103d8d x hx)

theorem rest_l103da0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103da0 bytes_l103da0) (entryMap (live .l103da0))
      10 0x103da0 bytes_l103da0 b_l103da0 := by
  have f0 : InstrSpec 0x103da0 [0x55] (PushPre 0x103da0 1) (pushR64Effect 0x103da0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103da0 1 5).toInstrSpec (push_r64_effect_step 0x103da0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103da1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x103da1) (movR64R64Effect 0x103da1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103da1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x103da1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103da4 [0x53] (PushPre 0x103da4 1) (pushR64Effect 0x103da4 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103da4 1 3).toInstrSpec (push_r64_effect_step 0x103da4 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103da5 [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x103da5) (subR64Imm8Effect 0x103da5 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x103da5 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x103da5 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103da9 [0x4C, 0x8B, 0x07] (LoadPre 0x103da9 (fun s => AddrMode.addr (.base 7 .none) s (0x103da9 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x103da9 8 (.base 7 .none))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x103da9 8 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103da9 0x4c (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103dac [0xB8, 0x14, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103dac) (movR32Imm32Effect 0x103dac 5 0 0x14)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x103dac 5 0 0x14).toInstrSpec (mov_r32_imm32_effect_step 0x103dac 0xb8 (by decide) 0x14) pre_rip
  have f6 : InstrSpec 0x103db1 [0x48, 0x8D, 0x3D, 0x78, 0xD1, 0x0F, 0x00] (fun s => s.RIP = 0x103db1) (leaR64Effect 0x103db1 7 (.rip 0xfd178))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103db1 7 (.rip 0xfd178)).toInstrSpec (lea_r64_effect_step 0x103db1 0x48 (by decide) 7 (.rip 0xfd178) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103db8 [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x103db8) (movR64R64Effect 0x103db8 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103db8 2 8).toInstrSpec (mov_r64_r64_effect_step 0x103db8 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103dbb [0x49, 0x81, 0xF8, 0xE8, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x103dbb) (cmpR64Imm32Effect 0x103dbb 8 0x3e8)
      [.gpr 8] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x103dbb 8 0x3e8).toInstrSpec (cmp_r64_imm32_effect_step 0x103dbb 0x49 0xf8 0x3e8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103da1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103da4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103da5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103da9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103dac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103db1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103db8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103dbb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103dc2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x103dc2 2 0x6d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103da0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103da0 :=
  Rest.liftedBlock (rest_l103da0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103da0 x hx)

theorem rest_l103dc4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103dc4 bytes_l103dc4) (entryMap (live .l103dc4))
      3 0x103dc4 bytes_l103dc4 b_l103dc4 := by
  have f0 : InstrSpec 0x103dc4 [0x49, 0xB9, 0x4B, 0x59, 0x86, 0x38, 0xD6, 0xC5, 0x6D, 0x34] (fun s => s.RIP = 0x103dc4) (movR64Imm64Effect 0x103dc4 9 0x346dc5d63886594b)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x103dc4 9 0x346dc5d63886594b).toInstrSpec (mov_r64_imm64_effect_step 0x103dc4 0x49 0xb9 (by decide) (by decide) 0x346dc5d63886594b) pre_rip
  have f1 : InstrSpec 0x103dce [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x103dce) (movR64R64Effect 0x103dce 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103dce 1 8).toInstrSpec (mov_r64_r64_effect_step 0x103dce 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103dd1 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103dd1) (fun _ => nopEffect 0x103dd1 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103dd1 15).toInstrSpec (nop_m_effect_step 0x103dd1 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103dce) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103dd1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103de0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l103dc4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103dc4 :=
  Rest.liftedBlock (rest_l103dc4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103dc4 x hx)

theorem rest_l103de0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103de0 bytes_l103de0) (entryMap (live .l103de0))
      20 0x103de0 bytes_l103de0 b_l103de0 := by
  have f0 : InstrSpec 0x103de0 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x103de0) (movR64R64Effect 0x103de0 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x103de0 10 0).toInstrSpec (mov_r64_r64_effect_step 0x103de0 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103de3 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x103de3) (movR64R64Effect 0x103de3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x103de3 0 1).toInstrSpec (mov_r64_r64_effect_step 0x103de3 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103de6 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x103de6) (mulR64Effect 0x103de6 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x103de6 9).toInstrSpec (mul_r64_effect_step 0x103de6 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103de9 [0x48, 0xC1, 0xEA, 0x0B] (fun s => s.RIP = 0x103de9) (shrR64Effect 0x103de9 4 2 11)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x103de9 4 2 11).toInstrSpec (shr_r64_imm8_effect_step 0x103de9 0x48 0xea 0xb (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103ded [0x69, 0xC2, 0x10, 0x27, 0x00, 0x00] (fun s => s.RIP = 0x103ded) (imulR32R32Imm32Effect 0x103ded 6 0 2 0x2710)
      [.gpr 2] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x103ded 6 0 2 0x2710).toInstrSpec (imul_r32_r32_imm32_effect_step 0x103ded 0xc2 (by decide) 0x2710) pre_rip
  have f5 : InstrSpec 0x103df3 [0x41, 0x89, 0xCB] (fun s => s.RIP = 0x103df3) (movR32R32Effect 0x103df3 3 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x103df3 3 11 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x103df3 0x41 0xcb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103df6 [0x41, 0x29, 0xC3] (fun s => s.RIP = 0x103df6) (subR32R32Effect 0x103df6 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x103df6 3 11 0).toInstrSpec (sub_r32_r32_rex_effect_step 0x103df6 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103df9 [0x41, 0x69, 0xC3, 0x7B, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x103df9) (imulR32R32Imm32Effect 0x103df9 7 0 11 0x147b)
      [.gpr 11] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x103df9 7 0 11 0x147b).toInstrSpec (imul_r32_r32_imm32_rex_effect_step 0x103df9 0x41 (by decide) 0xc3 (by decide) 0x147b) pre_rip
  have f8 : InstrSpec 0x103e00 [0xC1, 0xE8, 0x13] (fun s => s.RIP = 0x103e00) (shrR32Effect 0x103e00 3 0 19)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x103e00 3 0 19).toInstrSpec (shr_r32_imm8_effect_step 0x103e00 0xe8 0x13 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103e03 [0x6B, 0xD8, 0x64] (fun s => s.RIP = 0x103e03) (imulR32R32Imm8Effect 0x103e03 3 3 0 0x64)
      [.gpr 0] [] [.reg 3, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x103e03 3 3 0 0x64).toInstrSpec (imul_r32_r32_imm8_effect_step 0x103e03 0xd8 (by decide) 0x64) pre_rip
  have f10 : InstrSpec 0x103e06 [0x41, 0x29, 0xDB] (fun s => s.RIP = 0x103e06) (subR32R32Effect 0x103e06 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x103e06 3 11 3).toInstrSpec (sub_r32_r32_rex_effect_step 0x103e06 0x41 0xdb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103e09 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x103e09 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x103e09 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x103e09 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103e09 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x103e09 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x103e0d [0x66, 0x42, 0x89, 0x44, 0x15, 0xE0] (StorePre 0x103e0d 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe0)) s (0x103e0d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x103e0d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0)))
      [.gpr 0, .gpr 5, .gpr 10] [] [.rip] :=
    (movM16R16Effect_footprint 0x103e0d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0))).toInstrSpec (mov_m16_r16_rex_effect_step 0x103e0d 0x42 (by decide) 0 (.sib 5 (some 10) 0 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x103e13 [0x41, 0x0F, 0xB7, 0xC3] (fun s => s.RIP = 0x103e13) (movzxR32R16Effect 0x103e13 4 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movzxR32R16Effect_footprint 0x103e13 4 0 11).toInstrSpec (movzx_r32_r16_rex_effect_step 0x103e13 0x41 (by decide) 0xc3 (by decide)) pre_rip
  have f14 : InstrSpec 0x103e17 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x103e17 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x103e17 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x103e17 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103e17 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x103e17 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x103e1b [0x66, 0x42, 0x89, 0x44, 0x15, 0xE2] (StorePre 0x103e1b 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe2)) s (0x103e1b + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x103e1b 6 0 (.sib 5 (some 10) 0 (.d8 0xe2)))
      [.gpr 0, .gpr 5, .gpr 10] [] [.rip] :=
    (movM16R16Effect_footprint 0x103e1b 6 0 (.sib 5 (some 10) 0 (.d8 0xe2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x103e1b 0x42 (by decide) 0 (.sib 5 (some 10) 0 (.d8 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x103e21 [0x49, 0x8D, 0x42, 0xFC] (fun s => s.RIP = 0x103e21) (leaR64Effect 0x103e21 0 (.base 10 (.d8 0xfc)))
      [.gpr 10] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103e21 0 (.base 10 (.d8 0xfc))).toInstrSpec (lea_r64_effect_step 0x103e21 0x49 (by decide) 0 (.base 10 (.d8 0xfc)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x103e25 [0x48, 0x81, 0xF9, 0x7F, 0x96, 0x98, 0x00] (fun s => s.RIP = 0x103e25) (cmpR64Imm32Effect 0x103e25 1 0x98967f)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x103e25 1 0x98967f).toInstrSpec (cmp_r64_imm32_effect_step 0x103e25 0x48 0xf9 0x98967f (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x103e2c [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x103e2c) (movR64R64Effect 0x103e2c 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103e2c 1 2).toInstrSpec (mov_r64_r64_effect_step 0x103e2c 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103de3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103de6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103de9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ded) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103df3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103df6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103df9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e00) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e03) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e06) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e09) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e0d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e13) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e17) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e1b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e21) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e25) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e2c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 83), (1, 88), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e2f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel8_effect_step 0x103e2f 7 0xaf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103de0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103de0 :=
  Rest.liftedBlock (rest_l103de0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103de0 x hx)

theorem rest_l103e31 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103e31 bytes_l103e31) (entryMap (live .l103e31))
      2 0x103e31 bytes_l103e31 b_l103e31 := by
  have f0 : InstrSpec 0x103e31 [0x48, 0x83, 0xFA, 0x09] (fun s => s.RIP = 0x103e31) (cmpR64Imm8Effect 0x103e31 2 0x9)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x103e31 2 0x9).toInstrSpec (cmp_r64_imm8_effect_step 0x103e31 0x48 0xfa 0x9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e35) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x103e35 6 0x2b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103e31 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103e31 :=
  Rest.liftedBlock (rest_l103e31 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103e31 x hx)

theorem rest_l103e37 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103e37 bytes_l103e37) (entryMap (live .l103e37))
      12 0x103e37 bytes_l103e37 b_l103e37 := by
  have f0 : InstrSpec 0x103e37 [0x89, 0xD1] (fun s => s.RIP = 0x103e37) (movR32R32Effect 0x103e37 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x103e37 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x103e37 0xd1 (by decide)) pre_rip
  have f1 : InstrSpec 0x103e39 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x103e39) (shrR32Effect 0x103e39 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x103e39 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x103e39 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103e3c [0x0F, 0xB7, 0xC9] (fun s => s.RIP = 0x103e3c) (movzxR32R16Effect 0x103e3c 3 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32R16Effect_footprint 0x103e3c 3 1 1).toInstrSpec (movzx_r32_r16_effect_step 0x103e3c 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x103e3f [0x69, 0xC9, 0x7B, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x103e3f) (imulR32R32Imm32Effect 0x103e3f 6 1 1 0x147b)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x103e3f 6 1 1 0x147b).toInstrSpec (imul_r32_r32_imm32_effect_step 0x103e3f 0xc9 (by decide) 0x147b) pre_rip
  have f4 : InstrSpec 0x103e45 [0xC1, 0xE9, 0x11] (fun s => s.RIP = 0x103e45) (shrR32Effect 0x103e45 3 1 17)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x103e45 3 1 17).toInstrSpec (shr_r32_imm8_effect_step 0x103e45 0xe9 0x11 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103e48 [0x44, 0x6B, 0xC9, 0x64] (fun s => s.RIP = 0x103e48) (imulR32R32Imm8Effect 0x103e48 4 9 1 0x64)
      [.gpr 1] [] [.reg 9, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x103e48 4 9 1 0x64).toInstrSpec (imul_r32_r32_imm8_rex_effect_step 0x103e48 0x44 (by decide) 0xc9 (by decide) 0x64) pre_rip
  have f6 : InstrSpec 0x103e4c [0x44, 0x29, 0xCA] (fun s => s.RIP = 0x103e4c) (subR32R32Effect 0x103e4c 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (subR32R32Effect_footprint 0x103e4c 3 2 9).toInstrSpec (sub_r32_r32_rex_effect_step 0x103e4c 0x44 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103e4f [0x0F, 0xB7, 0xD2] (fun s => s.RIP = 0x103e4f) (movzxR32R16Effect 0x103e4f 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R16Effect_footprint 0x103e4f 3 2 2).toInstrSpec (movzx_r32_r16_effect_step 0x103e4f 0xd2 (by decide)) pre_rip
  have f8 : InstrSpec 0x103e52 [0x0F, 0xB7, 0x14, 0x57] (LoadPre 0x103e52 (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x103e52 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x103e52 4 2 (.sib 7 (some 2) 1 .none))
      [.gpr 7, .gpr 2] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x103e52 4 2 (.sib 7 (some 2) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x103e52 2 (.sib 7 (some 2) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103e56 [0x66, 0x89, 0x54, 0x05, 0xE2] (StorePre 0x103e56 5 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe2)) s (0x103e56 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103e56 5 2 (.sib 5 (some 0) 0 (.d8 0xe2)))
      [.gpr 2, .gpr 5, .gpr 0] [] [.rip] :=
    (movM16R16Effect_footprint 0x103e56 5 2 (.sib 5 (some 0) 0 (.d8 0xe2))).toInstrSpec (mov_m16_r16_effect_step 0x103e56 2 (.sib 5 (some 0) 0 (.d8 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x103e5b [0x48, 0x83, 0xC0, 0xFE] (fun s => s.RIP = 0x103e5b) (addR64Imm8Effect 0x103e5b 0 0xfe)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x103e5b 0 0xfe).toInstrSpec (add_r64_imm8_effect_step 0x103e5b 0x48 0xc0 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103e5f [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x103e5f) (movR64R64Effect 0x103e5f 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103e5f 2 1).toInstrSpec (mov_r64_r64_effect_step 0x103e5f 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e39) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e3c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e3f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e45) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e48) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e4c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e4f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e52) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e56) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e5b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e5f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 61), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e62) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l103e37 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103e37 :=
  Rest.liftedBlock (rest_l103e37 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103e37 x hx)

theorem rest_l103e62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103e62 bytes_l103e62) (entryMap (live .l103e62))
      2 0x103e62 bytes_l103e62 b_l103e62 := by
  have f0 : InstrSpec 0x103e62 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x103e62) (testR64R64Effect 0x103e62 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103e62 8 8).toInstrSpec (test_r64_r64_effect_step 0x103e62 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e65) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103e65 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103e62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103e62 :=
  Rest.liftedBlock (rest_l103e62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103e62 x hx)

theorem rest_l103e67 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103e67 bytes_l103e67) (entryMap (live .l103e67))
      2 0x103e67 bytes_l103e67 b_l103e67 := by
  have f0 : InstrSpec 0x103e67 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x103e67) (testR64R64Effect 0x103e67 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103e67 2 2).toInstrSpec (test_r64_r64_effect_step 0x103e67 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e6a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103e6a 4 0xc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103e67 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103e67 :=
  Rest.liftedBlock (rest_l103e67 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103e67 x hx)

theorem rest_l103e6c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103e6c bytes_l103e6c) (entryMap (live .l103e6c))
      3 0x103e6c bytes_l103e6c b_l103e6c := by
  have f0 : InstrSpec 0x103e6c [0x0F, 0xB6, 0x4C, 0x57, 0x01] (LoadPre 0x103e6c (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1)) s (0x103e6c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x103e6c 5 1 (.sib 7 (some 2) 1 (.d8 0x1)))
      [.gpr 7, .gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x103e6c 5 1 (.sib 7 (some 2) 1 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x103e6c 1 (.sib 7 (some 2) 1 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103e71 [0x88, 0x4C, 0x05, 0xE3] (StorePre 0x103e71 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe3)) s (0x103e71 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x103e71 4 1 (.sib 5 (some 0) 0 (.d8 0xe3)))
      [.gpr 1, .gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x103e71 4 1 (.sib 5 (some 0) 0 (.d8 0xe3))).toInstrSpec (mov_m8_r8_effect_step 0x103e71 1 (by decide) (.sib 5 (some 0) 0 (.d8 0xe3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103e75 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x103e75) (decR64Effect 0x103e75 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x103e75 0).toInstrSpec (dec_r64_effect_step 0x103e75 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e71) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e75) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e78) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l103e6c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103e6c :=
  Rest.liftedBlock (rest_l103e6c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103e6c x hx)

theorem rest_l103e78 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103e78 bytes_l103e78) (entryMap (live .l103e78))
      9 0x103e78 bytes_l103e78 b_l103e78 := by
  have f0 : InstrSpec 0x103e78 [0x41, 0xB9, 0x14, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103e78) (movR32Imm32Effect 0x103e78 6 9 0x14)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x103e78 6 9 0x14).toInstrSpec (mov_r32_imm32_rex_effect_step 0x103e78 0x41 0xb9 (by decide) (by decide) 0x14) pre_rip
  have f1 : InstrSpec 0x103e7e [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x103e7e) (subR64R64Effect 0x103e7e 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x103e7e 9 0).toInstrSpec (sub_r64_r64_effect_step 0x103e7e 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103e81 [0x4C, 0x8D, 0x04, 0x28] (fun s => s.RIP = 0x103e81) (leaR64Effect 0x103e81 8 (.sib 0 (some 5) 0 .none))
      [.gpr 0, .gpr 5] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x103e81 8 (.sib 0 (some 5) 0 .none)).toInstrSpec (lea_r64_effect_step 0x103e81 0x4c (by decide) 0 (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103e85 [0x49, 0x83, 0xC0, 0xE4] (fun s => s.RIP = 0x103e85) (addR64Imm8Effect 0x103e85 8 0xe4)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x103e85 8 0xe4).toInstrSpec (add_r64_imm8_effect_step 0x103e85 0x49 0xc0 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103e89 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103e89) (movR32Imm32Effect 0x103e89 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x103e89 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x103e89 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x103e8e [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x103e8e) (movR64R64Effect 0x103e8e 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103e8e 7 6).toInstrSpec (mov_r64_r64_effect_step 0x103e8e 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103e91 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103e91) (movR32Imm32Effect 0x103e91 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x103e91 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x103e91 0xbe (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x103e96 [0x31, 0xC9] (fun s => s.RIP = 0x103e96) (xorR32R32Effect 0x103e96 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103e96 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x103e96 0xc9 (by decide)) pre_rip
  have f8 : InstrSpec 0x103e98 [0xFF, 0x15, 0x7A, 0xD3, 0x0F, 0x00] (GoesTo (CallMemPre 0x103e98 (.rip 0xfd37a)) (callEffect (callMemPtr 0x103e98 (.rip 0xfd37a)) (0x103e98 + BitVec.ofNat 64 (callMemLen (.rip 0xfd37a)))) 0x103520) (callEffect (callMemPtr 0x103e98 (.rip 0xfd37a)) (0x103e98 + BitVec.ofNat 64 (callMemLen (.rip 0xfd37a))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x103e98 (.rip 0xfd37a)).toInstrSpec (call_m64_effect_step 0x103e98 (.rip 0xfd37a) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103520
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e81) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 57), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e89) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e8e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e91) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e96) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103e98) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103520) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l103e78 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103e78 :=
  Rest.liftedBlock (rest_l103e78 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103e78 x hx)

theorem rest_l103e9e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103e9e bytes_l103e9e) (entryMap (live .l103e9e))
      4 0x103e9e bytes_l103e9e b_l103e9e := by
  have f0 : InstrSpec 0x103e9e [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x103e9e) (addR64Imm8Effect 0x103e9e 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x103e9e 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x103e9e 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103ea2 [0x5B] (PopPre 0x103ea2) (popR64Effect 0x103ea2 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103ea2 1 3).toInstrSpec (pop_r64_effect_step 0x103ea2 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103ea3 [0x5D] (PopPre 0x103ea3) (popR64Effect 0x103ea3 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103ea3 1 5).toInstrSpec (pop_r64_effect_step 0x103ea3 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103ea4 [0xC3] (RetPre 0x103ea4) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103ea4).toInstrSpec (ret_effect_step 0x103ea4) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ea2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ea3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ea4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l103e9e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103e9e :=
  Rest.liftedBlock (rest_l103e9e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103e9e x hx)

theorem rest_l103eb0_1 [Bindings] (code : CodeMap) :
    Rest (n := 94) code lifted (codeRange 0x103eb0 bytes_l103eb0) [(0, 92), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x103ef4 bytes_l103eb0_1 b_l103eb0_1 := by
  have f20 : InstrSpec 0x103ef4 [0xC3] (RetPre 0x103ef4) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103ef4).toInstrSpec (ret_effect_step 0x103ef4) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f20 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 96) (ρ' := [(0, 92), (1, 90), (2, 55), (3, 3), (4, 95), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f20 (by decide) rfl rfl rfl (by decide)

theorem rest_l103eb0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103eb0 bytes_l103eb0) (entryMap (live .l103eb0))
      21 0x103eb0 bytes_l103eb0 b_l103eb0 := by
  have f0 : InstrSpec 0x103eb0 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x103eb0) (movR64R64Effect 0x103eb0 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x103eb0 8 2).toInstrSpec (mov_r64_r64_effect_step 0x103eb0 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103eb3 [0x48, 0x89, 0xFA] (fun s => s.RIP = 0x103eb3) (movR64R64Effect 0x103eb3 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103eb3 2 7).toInstrSpec (mov_r64_r64_effect_step 0x103eb3 0x48 0xfa (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103eb6 [0x40, 0x0F, 0xB6, 0xCE] (fun s => s.RIP = 0x103eb6) (movzxR32R8Effect 0x103eb6 4 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x103eb6 4 1 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x103eb6 0x40 (by decide) 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x103eba [0x48, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01] (fun s => s.RIP = 0x103eba) (movR64Imm64Effect 0x103eba 0 0x101010101010101)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x103eba 0 0x101010101010101).toInstrSpec (mov_r64_imm64_effect_step 0x103eba 0x48 0xb8 (by decide) (by decide) 0x101010101010101) pre_rip
  have f4 : InstrSpec 0x103ec4 [0x48, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x103ec4) (imulR64R64Effect 0x103ec4 4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103ec4 4 0 1).toInstrSpec (imul_r64_r64_effect_step 0x103ec4 0x48 (by decide) 0xc1 (by decide)) pre_rip
  have f5 : InstrSpec 0x103ec8 [0x89, 0xD1] (fun s => s.RIP = 0x103ec8) (movR32R32Effect 0x103ec8 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x103ec8 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x103ec8 0xd1 (by decide)) pre_rip
  have f6 : InstrSpec 0x103eca [0xF7, 0xD9] (fun s => s.RIP = 0x103eca) (negR32Effect 0x103eca 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR32Effect_footprint 0x103eca 2 1).toInstrSpec (neg_r32_effect_step 0x103eca 0xd9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103ecc [0x83, 0xE1, 0x07] (fun s => s.RIP = 0x103ecc) (andR32Imm8Effect 0x103ecc 3 1 0x7)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103ecc 3 1 0x7).toInstrSpec (and_r32_imm8_effect_step 0x103ecc 0xe1 0x7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103ecf [0x49, 0x39, 0xC8] (fun s => s.RIP = 0x103ecf) (cmpR64R64Effect 0x103ecf 8 1)
      [.gpr 8, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103ecf 8 1).toInstrSpec (cmp_r64_r64_effect_step 0x103ecf 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103ed2 [0x49, 0x0F, 0x42, 0xC8] (fun s => s.RIP = 0x103ed2) (atFlags (condHolds 2) (cmovR64R64Effect 0x103ed2 4 1 8))
      [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x103ed2 4 1 8 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x103ed2 2 0x49 (by decide) 0xc8 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x103ed6 [0x49, 0x29, 0xC8] (fun s => s.RIP = 0x103ed6) (subR64R64Effect 0x103ed6 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x103ed6 8 1).toInstrSpec (sub_r64_r64_effect_step 0x103ed6 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103ed9 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x103ed9) (movR64R64Effect 0x103ed9 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103ed9 6 8).toInstrSpec (mov_r64_r64_effect_step 0x103ed9 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x103edc [0x48, 0xC1, 0xEE, 0x03] (fun s => s.RIP = 0x103edc) (shrR64Effect 0x103edc 4 6 3)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x103edc 4 6 3).toInstrSpec (shr_r64_imm8_effect_step 0x103edc 0x48 0xee 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x103ee0 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x103ee0) (andR32Imm8Effect 0x103ee0 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103ee0 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x103ee0 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x103ee4 [0xF3, 0xAA] (RepPre 0x103ee4 (RepStosbPre 0x103ee4)) (repStosbEffect 0x103ee4)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosbEffect_footprint 0x103ee4).toInstrSpecOfRuns (rep_stosb_runs hstride 0x103ee4) (RepStosOk.of_stateOf RepStosbPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x103ee6 [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x103ee6) (movR64R64Effect 0x103ee6 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103ee6 1 6).toInstrSpec (mov_r64_r64_effect_step 0x103ee6 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x103ee9 [0xF3, 0x48, 0xAB] (RepPre 0x103ee9 (RepStosqPre 0x103ee9)) (repStosqEffect 0x103ee9)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosqEffect_footprint 0x103ee9).toInstrSpecOfRuns (rep_stosq_runs hstride 0x103ee9 0x48 (by decide)) (RepStosOk.of_stateOf RepStosqPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x103eec [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x103eec) (movR64R64Effect 0x103eec 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103eec 1 8).toInstrSpec (mov_r64_r64_effect_step 0x103eec 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x103eef [0xF3, 0xAA] (RepPre 0x103eef (RepStosbPre 0x103eef)) (repStosbEffect 0x103eef)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosbEffect_footprint 0x103eef).toInstrSpecOfRuns (rep_stosb_runs hstride 0x103eef) (RepStosOk.of_stateOf RepStosbPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f19 : InstrSpec 0x103ef1 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x103ef1) (movR64R64Effect 0x103ef1 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x103ef1 0 2).toInstrSpec (mov_r64_r64_effect_step 0x103ef1 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ec4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ec8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 65), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ecc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ecf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ed2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ed6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 73), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ed9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 75), (7, 7), (8, 73), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103edc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 7), (8, 73), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ee0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 7), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ee4) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ee6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 61), (1, 83), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ee9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 85), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eec) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 61), (1, 87), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 85), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eef) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 90) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 91) (ρ' := [(0, 61), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ef1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ef4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l103eb0_1 code

theorem block_l103eb0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103eb0 :=
  Rest.liftedBlock (rest_l103eb0 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103eb0 x hx)

theorem rest_l103f00 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f00 bytes_l103f00) (entryMap (live .l103f00))
      16 0x103f00 bytes_l103f00 b_l103f00 := by
  have f0 : InstrSpec 0x103f00 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x103f00) (movR64R64Effect 0x103f00 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x103f00 0 7).toInstrSpec (mov_r64_r64_effect_step 0x103f00 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103f03 [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x103f03) (movR32R32Effect 0x103f03 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x103f03 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x103f03 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103f06 [0x41, 0xF7, 0xD8] (fun s => s.RIP = 0x103f06) (negR32Effect 0x103f06 3 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR32Effect_footprint 0x103f06 3 8).toInstrSpec (neg_r32_rex_effect_step 0x103f06 0x41 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103f09 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x103f09) (andR32Imm8Effect 0x103f09 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103f09 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x103f09 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103f0d [0x4C, 0x39, 0xC2] (fun s => s.RIP = 0x103f0d) (cmpR64R64Effect 0x103f0d 2 8)
      [.gpr 2, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103f0d 2 8).toInstrSpec (cmp_r64_r64_effect_step 0x103f0d 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103f10 [0x4C, 0x0F, 0x42, 0xC2] (fun s => s.RIP = 0x103f10) (atFlags (condHolds 2) (cmovR64R64Effect 0x103f10 4 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x103f10 4 8 2 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x103f10 2 0x4c (by decide) 0xc2 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x103f14 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x103f14) (movR64R64Effect 0x103f14 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103f14 1 8).toInstrSpec (mov_r64_r64_effect_step 0x103f14 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103f17 [0xF3, 0xA4] (RepPre 0x103f17 (RepMovsbPre 0x103f17)) (repMovsbEffect 0x103f17)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x103f17).toInstrSpecOfRuns (rep_movsb_runs hstride 0x103f17) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x103f19 [0x4C, 0x29, 0xC2] (fun s => s.RIP = 0x103f19) (subR64R64Effect 0x103f19 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x103f19 2 8).toInstrSpec (sub_r64_r64_effect_step 0x103f19 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103f1c [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x103f1c) (movR64R64Effect 0x103f1c 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103f1c 1 2).toInstrSpec (mov_r64_r64_effect_step 0x103f1c 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103f1f [0x48, 0xC1, 0xE9, 0x03] (fun s => s.RIP = 0x103f1f) (shrR64Effect 0x103f1f 4 1 3)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x103f1f 4 1 3).toInstrSpec (shr_r64_imm8_effect_step 0x103f1f 0x48 0xe9 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103f23 [0xF3, 0x48, 0xA5] (RepPre 0x103f23 (RepMovsqPre 0x103f23)) (repMovsqEffect 0x103f23)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x103f23).toInstrSpecOfRuns (rep_movsq_runs hstride 0x103f23 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f12 : InstrSpec 0x103f26 [0x83, 0xE2, 0x07] (fun s => s.RIP = 0x103f26) (andR32Imm8Effect 0x103f26 3 2 0x7)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103f26 3 2 0x7).toInstrSpec (and_r32_imm8_effect_step 0x103f26 0xe2 0x7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x103f29 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x103f29) (movR64R64Effect 0x103f29 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103f29 1 2).toInstrSpec (mov_r64_r64_effect_step 0x103f29 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x103f2c [0xF3, 0xA4] (RepPre 0x103f2c (RepMovsbPre 0x103f2c)) (repMovsbEffect 0x103f2c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x103f2c).toInstrSpecOfRuns (rep_movsb_runs hstride 0x103f2c) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x103f2e [0xC3] (RetPre 0x103f2e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103f2e).toInstrSpec (ret_effect_step 0x103f2e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f03) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f06) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f09) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f0d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f10) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f14) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f17) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f19) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f1c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f1f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 74), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f23) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f26) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f29) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 81), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f2c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 85) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 4), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f2e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 89) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 88), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l103f00 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f00 :=
  Rest.liftedBlock (rest_l103f00 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f00 x hx)

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

theorem_by block_l101230_eval :
    program.runBlock (dialect code) ⟨.l101230, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101240_eval :
    program.runBlock (dialect code) ⟨.l101240, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101270_eval :
    program.runBlock (dialect code) ⟨.l101270, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101280_eval :
    program.runBlock (dialect code) ⟨.l101280, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10128b_eval :
    program.runBlock (dialect code) ⟨.l10128b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1012cf_eval :
    program.runBlock (dialect code) ⟨.l1012cf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1012d2_eval :
    program.runBlock (dialect code) ⟨.l1012d2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1012f0_eval :
    program.runBlock (dialect code) ⟨.l1012f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101322_eval :
    program.runBlock (dialect code) ⟨.l101322, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101335_eval :
    program.runBlock (dialect code) ⟨.l101335, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10136a_eval :
    program.runBlock (dialect code) ⟨.l10136a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101380_eval :
    program.runBlock (dialect code) ⟨.l101380, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1013b0_eval :
    program.runBlock (dialect code) ⟨.l1013b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1013c8_eval :
    program.runBlock (dialect code) ⟨.l1013c8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101409_eval :
    program.runBlock (dialect code) ⟨.l101409, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101410_eval :
    program.runBlock (dialect code) ⟨.l101410, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101417_eval :
    program.runBlock (dialect code) ⟨.l101417, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101444_eval :
    program.runBlock (dialect code) ⟨.l101444, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101459_eval :
    program.runBlock (dialect code) ⟨.l101459, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101470_eval :
    program.runBlock (dialect code) ⟨.l101470, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014a1_eval :
    program.runBlock (dialect code) ⟨.l1014a1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014b4_eval :
    program.runBlock (dialect code) ⟨.l1014b4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014e7_eval :
    program.runBlock (dialect code) ⟨.l1014e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014f3_eval :
    program.runBlock (dialect code) ⟨.l1014f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101508_eval :
    program.runBlock (dialect code) ⟨.l101508, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101520_eval :
    program.runBlock (dialect code) ⟨.l101520, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101550_eval :
    program.runBlock (dialect code) ⟨.l101550, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101560_eval :
    program.runBlock (dialect code) ⟨.l101560, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10156b_eval :
    program.runBlock (dialect code) ⟨.l10156b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015af_eval :
    program.runBlock (dialect code) ⟨.l1015af, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015b2_eval :
    program.runBlock (dialect code) ⟨.l1015b2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015d0_eval :
    program.runBlock (dialect code) ⟨.l1015d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101602_eval :
    program.runBlock (dialect code) ⟨.l101602, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101615_eval :
    program.runBlock (dialect code) ⟨.l101615, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10164a_eval :
    program.runBlock (dialect code) ⟨.l10164a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101660_eval :
    program.runBlock (dialect code) ⟨.l101660, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101690_eval :
    program.runBlock (dialect code) ⟨.l101690, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1016a8_eval :
    program.runBlock (dialect code) ⟨.l1016a8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1016e9_eval :
    program.runBlock (dialect code) ⟨.l1016e9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1016f0_eval :
    program.runBlock (dialect code) ⟨.l1016f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1016f7_eval :
    program.runBlock (dialect code) ⟨.l1016f7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101724_eval :
    program.runBlock (dialect code) ⟨.l101724, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101739_eval :
    program.runBlock (dialect code) ⟨.l101739, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101750_eval :
    program.runBlock (dialect code) ⟨.l101750, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101781_eval :
    program.runBlock (dialect code) ⟨.l101781, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101794_eval :
    program.runBlock (dialect code) ⟨.l101794, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1017c7_eval :
    program.runBlock (dialect code) ⟨.l1017c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1017d3_eval :
    program.runBlock (dialect code) ⟨.l1017d3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1017e8_eval :
    program.runBlock (dialect code) ⟨.l1017e8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102040_eval :
    program.runBlock (dialect code) ⟨.l102040, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10206c_eval :
    program.runBlock (dialect code) ⟨.l10206c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10215c_eval :
    program.runBlock (dialect code) ⟨.l10215c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102171_eval :
    program.runBlock (dialect code) ⟨.l102171, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102180_eval :
    program.runBlock (dialect code) ⟨.l102180, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1021ac_eval :
    program.runBlock (dialect code) ⟨.l1021ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10229c_eval :
    program.runBlock (dialect code) ⟨.l10229c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1022b1_eval :
    program.runBlock (dialect code) ⟨.l1022b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b80_eval :
    program.runBlock (dialect code) ⟨.l102b80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1034a0_eval :
    program.runBlock (dialect code) ⟨.l1034a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1034c0_eval :
    program.runBlock (dialect code) ⟨.l1034c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1034d0_eval :
    program.runBlock (dialect code) ⟨.l1034d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1034e6_eval :
    program.runBlock (dialect code) ⟨.l1034e6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1034f6_eval :
    program.runBlock (dialect code) ⟨.l1034f6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103506_eval :
    program.runBlock (dialect code) ⟨.l103506, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103837_eval :
    program.runBlock (dialect code) ⟨.l103837, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103874_eval :
    program.runBlock (dialect code) ⟨.l103874, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103880_eval :
    program.runBlock (dialect code) ⟨.l103880, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038ac_eval :
    program.runBlock (dialect code) ⟨.l1038ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c70_eval :
    program.runBlock (dialect code) ⟨.l103c70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c7d_eval :
    program.runBlock (dialect code) ⟨.l103c7d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103cb8_eval :
    program.runBlock (dialect code) ⟨.l103cb8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103cbd_eval :
    program.runBlock (dialect code) ⟨.l103cbd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103cc2_eval :
    program.runBlock (dialect code) ⟨.l103cc2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103cfd_eval :
    program.runBlock (dialect code) ⟨.l103cfd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103d38_eval :
    program.runBlock (dialect code) ⟨.l103d38, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103d40_eval :
    program.runBlock (dialect code) ⟨.l103d40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103d5c_eval :
    program.runBlock (dialect code) ⟨.l103d5c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103d66_eval :
    program.runBlock (dialect code) ⟨.l103d66, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103d6e_eval :
    program.runBlock (dialect code) ⟨.l103d6e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103d73_eval :
    program.runBlock (dialect code) ⟨.l103d73, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103d8b_eval :
    program.runBlock (dialect code) ⟨.l103d8b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103d8d_eval :
    program.runBlock (dialect code) ⟨.l103d8d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103da0_eval :
    program.runBlock (dialect code) ⟨.l103da0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103dc4_eval :
    program.runBlock (dialect code) ⟨.l103dc4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103de0_eval :
    program.runBlock (dialect code) ⟨.l103de0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103e31_eval :
    program.runBlock (dialect code) ⟨.l103e31, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103e37_eval :
    program.runBlock (dialect code) ⟨.l103e37, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103e62_eval :
    program.runBlock (dialect code) ⟨.l103e62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103e67_eval :
    program.runBlock (dialect code) ⟨.l103e67, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103e6c_eval :
    program.runBlock (dialect code) ⟨.l103e6c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103e78_eval :
    program.runBlock (dialect code) ⟨.l103e78, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103e9e_eval :
    program.runBlock (dialect code) ⟨.l103e9e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103eb0_eval :
    program.runBlock (dialect code) ⟨.l103eb0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f00_eval :
    program.runBlock (dialect code) ⟨.l103f00, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
