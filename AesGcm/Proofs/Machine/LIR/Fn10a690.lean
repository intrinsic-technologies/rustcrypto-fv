import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l10a690 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a690 bytes_l10a690) (entryMap (live .l10a690))
      9 0x10a690 bytes_l10a690 b_l10a690 := by
  have f0 : InstrSpec 0x10a690 [0x55] (PushPre 0x10a690 1) (pushR64Effect 0x10a690 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a690 1 5).toInstrSpec (push_r64_effect_step 0x10a690 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10a691 [0x41, 0x57] (PushPre 0x10a691 2) (pushR64Effect 0x10a691 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a691 2 15).toInstrSpec (push_r64_rex_effect_step 0x10a691 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10a693 [0x41, 0x56] (PushPre 0x10a693 2) (pushR64Effect 0x10a693 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a693 2 14).toInstrSpec (push_r64_rex_effect_step 0x10a693 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10a695 [0x41, 0x55] (PushPre 0x10a695 2) (pushR64Effect 0x10a695 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a695 2 13).toInstrSpec (push_r64_rex_effect_step 0x10a695 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10a697 [0x41, 0x54] (PushPre 0x10a697 2) (pushR64Effect 0x10a697 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a697 2 12).toInstrSpec (push_r64_rex_effect_step 0x10a697 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10a699 [0x53] (PushPre 0x10a699 1) (pushR64Effect 0x10a699 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a699 1 3).toInstrSpec (push_r64_effect_step 0x10a699 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10a69a [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x10a69a) (subR64Imm8Effect 0x10a69a 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10a69a 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x10a69a 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10a69e [0x48, 0x83, 0xFE, 0x07] (fun s => s.RIP = 0x10a69e) (cmpR64Imm8Effect 0x10a69e 6 0x7)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10a69e 6 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x10a69e 0x48 0xfe 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a691) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a693) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a695) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a697) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a699) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a69a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a69e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6a2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 70) (jcc_rel32_effect_step 0x10a6a2 6 0x3f1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a690 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a690 :=
  Rest.liftedBlock (rest_l10a690 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a690 x hx)

theorem rest_l10a6a8_14 [Bindings] (code : CodeMap) :
    Rest (n := 603) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 538), (1, 562), (2, 484), (3, 600), (4, 601), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x10aa8f bytes_l10a6a8_14 b_l10a6a8_14 := by
  have f280 : InstrSpec 0x10aa8f [0x41, 0x5C] (PopPre 0x10aa8f) (popR64Effect 0x10aa8f 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10aa8f 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10aa8f 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f281 : InstrSpec 0x10aa91 [0x41, 0x5D] (PopPre 0x10aa91) (popR64Effect 0x10aa91 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10aa91 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10aa91 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f282 : InstrSpec 0x10aa93 [0x41, 0x5E] (PopPre 0x10aa93) (popR64Effect 0x10aa93 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10aa93 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10aa93 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f283 : InstrSpec 0x10aa95 [0x41, 0x5F] (PopPre 0x10aa95) (popR64Effect 0x10aa95 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10aa95 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10aa95 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f284 : InstrSpec 0x10aa97 [0x5D] (PopPre 0x10aa97) (popR64Effect 0x10aa97 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10aa97 1 5).toInstrSpec (pop_r64_effect_step 0x10aa97 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f285 : InstrSpec 0x10aa98 [0xC3] (RetPre 0x10aa98) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10aa98).toInstrSpec (ret_effect_step 0x10aa98) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 603) (RestInside.out (n := 603) f280 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 604) f280 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 605) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 600), (4, 604), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 603), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa91) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 606) (RestInside.out (n := 606) f281 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 607) f281 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 608) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 600), (4, 607), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 603), (13, 606), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa93) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 609) (RestInside.out (n := 609) f282 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 610) f282 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 611) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 600), (4, 610), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 603), (13, 606), (14, 609), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa95) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 612) (RestInside.out (n := 612) f283 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 613) f283 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 614) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 600), (4, 613), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 603), (13, 606), (14, 609), (15, 612), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa97) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 615) (RestInside.out (n := 615) f284 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 616) f284 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 617) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 600), (4, 616), (5, 615), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 603), (13, 606), (14, 609), (15, 612), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa98) f284 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 618) (RestInside.out (n := 618) f285 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 619) f285 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 620) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 600), (4, 619), (5, 615), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 603), (13, 606), (14, 609), (15, 612), (22, 22), (39, 39), (50, 50), (51, 51)]) f285 (by decide) rfl rfl rfl (by decide)

theorem rest_l10a6a8_13 [Bindings] (code : CodeMap) :
    Rest (n := 570) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 538), (1, 562), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]
      26 0x10aa4a bytes_l10a6a8_13 b_l10a6a8_13 := by
  have f260 : InstrSpec 0x10aa4a [0x48, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x10aa4a) (shlR64Effect 0x10aa4a 4 3 2)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x10aa4a 4 3 2).toInstrSpec (shl_r64_imm8_effect_step 0x10aa4a 0x48 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f261 : InstrSpec 0x10aa4e [0x4C, 0x31, 0xE3] (fun s => s.RIP = 0x10aa4e) (xorR64R64Effect 0x10aa4e 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa4e 3 12).toInstrSpec (xor_r64_r64_effect_step 0x10aa4e 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f262 : InstrSpec 0x10aa51 [0x4C, 0x89, 0xDE] (fun s => s.RIP = 0x10aa51) (movR64R64Effect 0x10aa51 6 11)
      [.gpr 11] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10aa51 6 11).toInstrSpec (mov_r64_r64_effect_step 0x10aa51 0x4c 0xde (by decide) (by decide)) pre_rip
  have f263 : InstrSpec 0x10aa54 [0x48, 0xC1, 0xEE, 0x04] (fun s => s.RIP = 0x10aa54) (shrR64Effect 0x10aa54 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10aa54 4 6 4).toInstrSpec (shr_r64_imm8_effect_step 0x10aa54 0x48 0xee 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f264 : InstrSpec 0x10aa58 [0x48, 0x31, 0xDE] (fun s => s.RIP = 0x10aa58) (xorR64R64Effect 0x10aa58 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa58 6 3).toInstrSpec (xor_r64_r64_effect_step 0x10aa58 0x48 0xde (by decide) (by decide)) pre_rip
  have f265 : InstrSpec 0x10aa5b [0x4C, 0x21, 0xEE] (fun s => s.RIP = 0x10aa5b) (andR64R64Effect 0x10aa5b 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10aa5b 6 13).toInstrSpec (and_r64_r64_effect_step 0x10aa5b 0x4c 0xee (by decide) (by decide)) pre_rip
  have f266 : InstrSpec 0x10aa5e [0x49, 0x89, 0xF0] (fun s => s.RIP = 0x10aa5e) (movR64R64Effect 0x10aa5e 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10aa5e 8 6).toInstrSpec (mov_r64_r64_effect_step 0x10aa5e 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f267 : InstrSpec 0x10aa61 [0x49, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x10aa61) (shlR64Effect 0x10aa61 4 8 4)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x10aa61 4 8 4).toInstrSpec (shl_r64_imm8_effect_step 0x10aa61 0x49 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f268 : InstrSpec 0x10aa65 [0x4D, 0x31, 0xD8] (fun s => s.RIP = 0x10aa65) (xorR64R64Effect 0x10aa65 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa65 8 11).toInstrSpec (xor_r64_r64_effect_step 0x10aa65 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f269 : InstrSpec 0x10aa68 [0x48, 0x31, 0xDE] (fun s => s.RIP = 0x10aa68) (xorR64R64Effect 0x10aa68 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa68 6 3).toInstrSpec (xor_r64_r64_effect_step 0x10aa68 0x48 0xde (by decide) (by decide)) pre_rip
  have f270 : InstrSpec 0x10aa6b [0x4D, 0x89, 0x06] (StorePre 0x10aa6b 3 (fun s => AddrMode.addr (.base 14 .none) s (0x10aa6b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10aa6b 8 (.base 14 .none))
      [.gpr 8, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10aa6b 8 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10aa6b 0x4d (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f271 : InstrSpec 0x10aa6e [0x49, 0x89, 0x4E, 0x08] (StorePre 0x10aa6e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x10aa6e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa6e 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10aa6e 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10aa6e 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f272 : InstrSpec 0x10aa72 [0x49, 0x89, 0x7E, 0x10] (StorePre 0x10aa72 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x10aa72 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa72 7 (.base 14 (.d8 0x10)))
      [.gpr 7, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10aa72 7 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10aa72 0x49 (by decide) 7 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f273 : InstrSpec 0x10aa76 [0x4D, 0x89, 0x56, 0x18] (StorePre 0x10aa76 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x10aa76 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa76 10 (.base 14 (.d8 0x18)))
      [.gpr 10, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10aa76 10 (.base 14 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10aa76 0x4d (by decide) 2 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f274 : InstrSpec 0x10aa7a [0x49, 0x89, 0x76, 0x20] (StorePre 0x10aa7a 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10aa7a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa7a 6 (.base 14 (.d8 0x20)))
      [.gpr 6, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10aa7a 6 (.base 14 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10aa7a 0x49 (by decide) 6 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f275 : InstrSpec 0x10aa7e [0x4D, 0x89, 0x4E, 0x28] (StorePre 0x10aa7e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x10aa7e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa7e 9 (.base 14 (.d8 0x28)))
      [.gpr 9, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10aa7e 9 (.base 14 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10aa7e 0x4d (by decide) 1 (.base 14 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f276 : InstrSpec 0x10aa82 [0x49, 0x89, 0x46, 0x30] (StorePre 0x10aa82 4 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x10aa82 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa82 0 (.base 14 (.d8 0x30)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10aa82 0 (.base 14 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10aa82 0x49 (by decide) 0 (.base 14 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f277 : InstrSpec 0x10aa86 [0x49, 0x89, 0x56, 0x38] (StorePre 0x10aa86 4 (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x10aa86 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa86 2 (.base 14 (.d8 0x38)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10aa86 2 (.base 14 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10aa86 0x49 (by decide) 2 (.base 14 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f278 : InstrSpec 0x10aa8a [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x10aa8a) (addR64Imm8Effect 0x10aa8a 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10aa8a 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x10aa8a 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f279 : InstrSpec 0x10aa8e [0x5B] (PopPre 0x10aa8e) (popR64Effect 0x10aa8e 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10aa8e 1 3).toInstrSpec (pop_r64_effect_step 0x10aa8e 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 570) (RestInside.out (n := 570) f260 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 571) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 570), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa4e) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 572) (RestInside.out (n := 572) f261 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 573) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa51) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 574) (RestInside.out (n := 574) f262 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 575) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 574), (7, 536), (8, 488), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa54) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 576) (RestInside.out (n := 576) f263 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 577) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 576), (7, 536), (8, 488), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa58) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 578) (RestInside.out (n := 578) f264 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 579) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 578), (7, 536), (8, 488), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa5b) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 580) (RestInside.out (n := 580) f265 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 581) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 580), (7, 536), (8, 488), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa5e) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 582) (RestInside.out (n := 582) f266 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 583) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 580), (7, 536), (8, 582), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa61) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 584) (RestInside.out (n := 584) f267 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 585) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 580), (7, 536), (8, 584), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa65) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 586) (RestInside.out (n := 586) f268 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 587) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 580), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa68) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 588) (RestInside.out (n := 588) f269 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 589) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa6b) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 590) (RestInside.exec (n := 590) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa6e) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 591) (RestInside.exec (n := 591) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa72) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 592) (RestInside.exec (n := 592) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa76) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 593) (RestInside.exec (n := 593) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa7a) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 594) (RestInside.exec (n := 594) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa7e) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 595) (RestInside.exec (n := 595) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa82) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 596) (RestInside.exec (n := 596) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa86) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 597) (RestInside.exec (n := 597) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 4), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa8a) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 598) (RestInside.out (n := 598) f278 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 599) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 572), (4, 598), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa8e) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 600) (RestInside.out (n := 600) f279 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 601) f279 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 602) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 600), (4, 601), (5, 542), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa8f) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_14 code

theorem rest_l10a6a8_12 [Bindings] (code : CodeMap) :
    Rest (n := 530) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 526), (1, 528), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]
      46 0x10aa06 bytes_l10a6a8_12 b_l10a6a8_12 := by
  have f240 : InstrSpec 0x10aa06 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10aa06) (andR64R64Effect 0x10aa06 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10aa06 0 1).toInstrSpec (and_r64_r64_effect_step 0x10aa06 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f241 : InstrSpec 0x10aa09 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10aa09) (movR64R64Effect 0x10aa09 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10aa09 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10aa09 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f242 : InstrSpec 0x10aa0c [0x48, 0xC1, 0xE7, 0x04] (fun s => s.RIP = 0x10aa0c) (shlR64Effect 0x10aa0c 4 7 4)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x10aa0c 4 7 4).toInstrSpec (shl_r64_imm8_effect_step 0x10aa0c 0x48 0xe7 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f243 : InstrSpec 0x10aa10 [0x4C, 0x31, 0xCF] (fun s => s.RIP = 0x10aa10) (xorR64R64Effect 0x10aa10 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa10 7 9).toInstrSpec (xor_r64_r64_effect_step 0x10aa10 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f244 : InstrSpec 0x10aa13 [0x4C, 0x31, 0xE8] (fun s => s.RIP = 0x10aa13) (xorR64R64Effect 0x10aa13 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa13 0 13).toInstrSpec (xor_r64_r64_effect_step 0x10aa13 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f245 : InstrSpec 0x10aa16 [0x48, 0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x10aa16) (shlR64Effect 0x10aa16 4 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR64Effect_footprint 0x10aa16 4 5 2).toInstrSpec (shl_r64_imm8_effect_step 0x10aa16 0x48 0xe5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f246 : InstrSpec 0x10aa1a [0x48, 0x33, 0x6C, 0x24, 0x10] (LoadPre 0x10aa1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10aa1a + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x10aa1a 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 5, .gpr 4] [] [.reg 5, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10aa1a 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_r64_m64_effect_step 0x10aa1a 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f247 : InstrSpec 0x10aa1f [0x49, 0x89, 0xE9] (fun s => s.RIP = 0x10aa1f) (movR64R64Effect 0x10aa1f 9 5)
      [.gpr 5] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10aa1f 9 5).toInstrSpec (mov_r64_r64_effect_step 0x10aa1f 0x49 0xe9 (by decide) (by decide)) pre_rip
  have f248 : InstrSpec 0x10aa22 [0x49, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x10aa22) (shrR64Effect 0x10aa22 4 9 4)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x10aa22 4 9 4).toInstrSpec (shr_r64_imm8_effect_step 0x10aa22 0x49 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f249 : InstrSpec 0x10aa26 [0x49, 0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x10aa26) (shlR64Effect 0x10aa26 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64Effect_footprint 0x10aa26 4 15 2).toInstrSpec (shl_r64_imm8_effect_step 0x10aa26 0x49 0xe7 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f250 : InstrSpec 0x10aa2a [0x49, 0x31, 0xF7] (fun s => s.RIP = 0x10aa2a) (xorR64R64Effect 0x10aa2a 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa2a 15 6).toInstrSpec (xor_r64_r64_effect_step 0x10aa2a 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f251 : InstrSpec 0x10aa2d [0x4D, 0x31, 0xF9] (fun s => s.RIP = 0x10aa2d) (xorR64R64Effect 0x10aa2d 9 15)
      [.gpr 9, .gpr 15] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa2d 9 15).toInstrSpec (xor_r64_r64_effect_step 0x10aa2d 0x4d 0xf9 (by decide) (by decide)) pre_rip
  have f252 : InstrSpec 0x10aa30 [0x49, 0x21, 0xC9] (fun s => s.RIP = 0x10aa30) (andR64R64Effect 0x10aa30 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10aa30 9 1).toInstrSpec (and_r64_r64_effect_step 0x10aa30 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f253 : InstrSpec 0x10aa33 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x10aa33) (movR64R64Effect 0x10aa33 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10aa33 13 1).toInstrSpec (mov_r64_r64_effect_step 0x10aa33 0x49 0xcd (by decide) (by decide)) pre_rip
  have f254 : InstrSpec 0x10aa36 [0x4C, 0x89, 0xC9] (fun s => s.RIP = 0x10aa36) (movR64R64Effect 0x10aa36 1 9)
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10aa36 1 9).toInstrSpec (mov_r64_r64_effect_step 0x10aa36 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f255 : InstrSpec 0x10aa39 [0x48, 0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x10aa39) (shlR64Effect 0x10aa39 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10aa39 4 1 4).toInstrSpec (shl_r64_imm8_effect_step 0x10aa39 0x48 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f256 : InstrSpec 0x10aa3d [0x48, 0x31, 0xE9] (fun s => s.RIP = 0x10aa3d) (xorR64R64Effect 0x10aa3d 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa3d 1 5).toInstrSpec (xor_r64_r64_effect_step 0x10aa3d 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f257 : InstrSpec 0x10aa40 [0x4D, 0x31, 0xF9] (fun s => s.RIP = 0x10aa40) (xorR64R64Effect 0x10aa40 9 15)
      [.gpr 9, .gpr 15] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa40 9 15).toInstrSpec (xor_r64_r64_effect_step 0x10aa40 0x4d 0xf9 (by decide) (by decide)) pre_rip
  have f258 : InstrSpec 0x10aa43 [0x49, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x10aa43) (shlR64Effect 0x10aa43 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR64Effect_footprint 0x10aa43 4 11 2).toInstrSpec (shl_r64_imm8_effect_step 0x10aa43 0x49 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f259 : InstrSpec 0x10aa47 [0x4D, 0x31, 0xC3] (fun s => s.RIP = 0x10aa47) (xorR64R64Effect 0x10aa47 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10aa47 11 8).toInstrSpec (xor_r64_r64_effect_step 0x10aa47 0x4d 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 530) (RestInside.out (n := 530) f240 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 531) (ρ' := [(0, 530), (1, 528), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa09) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 532) (RestInside.out (n := 532) f241 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 533) (ρ' := [(0, 530), (1, 528), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 532), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa0c) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 534) (RestInside.out (n := 534) f242 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 535) (ρ' := [(0, 530), (1, 528), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 534), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa10) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 536) (RestInside.out (n := 536) f243 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 537) (ρ' := [(0, 530), (1, 528), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 536), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa13) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 538) (RestInside.out (n := 538) f244 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 539) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 536), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa16) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 540) (RestInside.out (n := 540) f245 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 541) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 540), (6, 458), (7, 536), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa1a) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 542) (RestInside.out (n := 542) f246 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 543) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa1f) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 544) (RestInside.out (n := 544) f247 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 545) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 544), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa22) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 546) (RestInside.out (n := 546) f248 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 547) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 546), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa26) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 548) (RestInside.out (n := 548) f249 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 549) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 546), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 548), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa2a) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 550) (RestInside.out (n := 550) f250 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 551) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 546), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa2d) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 552) (RestInside.out (n := 552) f251 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 553) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 552), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa30) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 554) (RestInside.out (n := 554) f252 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 555) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 554), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa33) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 556) (RestInside.out (n := 556) f253 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 557) (ρ' := [(0, 538), (1, 528), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 554), (10, 482), (11, 504), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa36) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 558) (RestInside.out (n := 558) f254 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 559) (ρ' := [(0, 538), (1, 558), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 554), (10, 482), (11, 504), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa39) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 560) (RestInside.out (n := 560) f255 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 561) (ρ' := [(0, 538), (1, 560), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 554), (10, 482), (11, 504), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa3d) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 562) (RestInside.out (n := 562) f256 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 563) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 554), (10, 482), (11, 504), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa40) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 564) (RestInside.out (n := 564) f257 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 565) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 564), (10, 482), (11, 504), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa43) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 566) (RestInside.out (n := 566) f258 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 567) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 564), (10, 482), (11, 566), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa47) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 568) (RestInside.out (n := 568) f259 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 569) (ρ' := [(0, 538), (1, 562), (2, 484), (3, 518), (4, 4), (5, 542), (6, 458), (7, 536), (8, 488), (9, 564), (10, 482), (11, 568), (12, 496), (13, 556), (14, 390), (15, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa4a) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_13 code

theorem rest_l10a6a8_11 [Bindings] (code : CodeMap) :
    Rest (n := 490) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 248), (10, 482), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]
      66 0x10a9bf bytes_l10a6a8_11 b_l10a6a8_11 := by
  have f220 : InstrSpec 0x10a9bf [0x4D, 0x01, 0xC9] (fun s => s.RIP = 0x10a9bf) (addR64R64Effect 0x10a9bf 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a9bf 9 9).toInstrSpec (add_r64_r64_effect_step 0x10a9bf 0x4d 0xc9 (by decide) (by decide)) pre_rip
  have f221 : InstrSpec 0x10a9c2 [0x4C, 0x33, 0x0C, 0x24] (LoadPre 0x10a9c2 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a9c2 + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x10a9c2 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10a9c2 9 (.sib 4 none 0 .none)).toInstrSpec (xor_r64_m64_effect_step 0x10a9c2 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f222 : InstrSpec 0x10a9c6 [0x4D, 0x01, 0xE4] (fun s => s.RIP = 0x10a9c6) (addR64R64Effect 0x10a9c6 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a9c6 12 12).toInstrSpec (add_r64_r64_effect_step 0x10a9c6 0x4d 0xe4 (by decide) (by decide)) pre_rip
  have f223 : InstrSpec 0x10a9c9 [0x4D, 0x31, 0xDC] (fun s => s.RIP = 0x10a9c9) (xorR64R64Effect 0x10a9c9 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9c9 12 11).toInstrSpec (xor_r64_r64_effect_step 0x10a9c9 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f224 : InstrSpec 0x10a9cc [0x4D, 0x89, 0xC3] (fun s => s.RIP = 0x10a9cc) (movR64R64Effect 0x10a9cc 11 8)
      [.gpr 8] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10a9cc 11 8).toInstrSpec (mov_r64_r64_effect_step 0x10a9cc 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f225 : InstrSpec 0x10a9cf [0x49, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x10a9cf) (shrR64Effect 0x10a9cf 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a9cf 4 11 2).toInstrSpec (shr_r64_imm8_effect_step 0x10a9cf 0x49 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f226 : InstrSpec 0x10a9d3 [0x4D, 0x31, 0xCB] (fun s => s.RIP = 0x10a9d3) (xorR64R64Effect 0x10a9d3 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9d3 11 9).toInstrSpec (xor_r64_r64_effect_step 0x10a9d3 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f227 : InstrSpec 0x10a9d6 [0x49, 0x21, 0xFB] (fun s => s.RIP = 0x10a9d6) (andR64R64Effect 0x10a9d6 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a9d6 11 7).toInstrSpec (and_r64_r64_effect_step 0x10a9d6 0x49 0xfb (by decide) (by decide)) pre_rip
  have f228 : InstrSpec 0x10a9d9 [0x4D, 0x31, 0xD9] (fun s => s.RIP = 0x10a9d9) (xorR64R64Effect 0x10a9d9 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9d9 9 11).toInstrSpec (xor_r64_r64_effect_step 0x10a9d9 0x4d 0xd9 (by decide) (by decide)) pre_rip
  have f229 : InstrSpec 0x10a9dc [0x4D, 0x01, 0xED] (fun s => s.RIP = 0x10a9dc) (addR64R64Effect 0x10a9dc 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a9dc 13 13).toInstrSpec (add_r64_r64_effect_step 0x10a9dc 0x4d 0xed (by decide) (by decide)) pre_rip
  have f230 : InstrSpec 0x10a9df [0x49, 0x31, 0xCD] (fun s => s.RIP = 0x10a9df) (xorR64R64Effect 0x10a9df 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9df 13 1).toInstrSpec (xor_r64_r64_effect_step 0x10a9df 0x49 0xcd (by decide) (by decide)) pre_rip
  have f231 : InstrSpec 0x10a9e2 [0x4C, 0x89, 0xE3] (fun s => s.RIP = 0x10a9e2) (movR64R64Effect 0x10a9e2 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10a9e2 3 12).toInstrSpec (mov_r64_r64_effect_step 0x10a9e2 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f232 : InstrSpec 0x10a9e5 [0x48, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x10a9e5) (shrR64Effect 0x10a9e5 4 3 2)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a9e5 4 3 2).toInstrSpec (shr_r64_imm8_effect_step 0x10a9e5 0x48 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f233 : InstrSpec 0x10a9e9 [0x4C, 0x31, 0xEB] (fun s => s.RIP = 0x10a9e9) (xorR64R64Effect 0x10a9e9 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9e9 3 13).toInstrSpec (xor_r64_r64_effect_step 0x10a9e9 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f234 : InstrSpec 0x10a9ec [0x48, 0x21, 0xFB] (fun s => s.RIP = 0x10a9ec) (andR64R64Effect 0x10a9ec 3 7)
      [.gpr 3, .gpr 7] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a9ec 3 7).toInstrSpec (and_r64_r64_effect_step 0x10a9ec 0x48 0xfb (by decide) (by decide)) pre_rip
  have f235 : InstrSpec 0x10a9ef [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x10a9ef) (movR64R64Effect 0x10a9ef 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10a9ef 0 9).toInstrSpec (mov_r64_r64_effect_step 0x10a9ef 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f236 : InstrSpec 0x10a9f2 [0x48, 0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x10a9f2) (shrR64Effect 0x10a9f2 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a9f2 4 0 4).toInstrSpec (shr_r64_imm8_effect_step 0x10a9f2 0x48 0xe8 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f237 : InstrSpec 0x10a9f6 [0x49, 0x31, 0xDD] (fun s => s.RIP = 0x10a9f6) (xorR64R64Effect 0x10a9f6 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9f6 13 3).toInstrSpec (xor_r64_r64_effect_step 0x10a9f6 0x49 0xdd (by decide) (by decide)) pre_rip
  have f238 : InstrSpec 0x10a9f9 [0x4C, 0x31, 0xE8] (fun s => s.RIP = 0x10a9f9) (xorR64R64Effect 0x10a9f9 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9f9 0 13).toInstrSpec (xor_r64_r64_effect_step 0x10a9f9 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f239 : InstrSpec 0x10a9fc [0x48, 0xB9, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F] (fun s => s.RIP = 0x10a9fc) (movR64Imm64Effect 0x10a9fc 1 0xf0f0f0f0f0f0f0f)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10a9fc 1 0xf0f0f0f0f0f0f0f).toInstrSpec (mov_r64_imm64_effect_step 0x10a9fc 0x48 0xb9 (by decide) (by decide) 0xf0f0f0f0f0f0f0f) pre_rip
  refine Rest.ofInside (n := 490) (RestInside.out (n := 490) f220 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 491) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 490), (10, 482), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9c2) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 492) (RestInside.out (n := 492) f221 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 493) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 492), (10, 482), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9c6) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 494) (RestInside.out (n := 494) f222 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 495) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 492), (10, 482), (11, 296), (12, 494), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9c9) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 496) (RestInside.out (n := 496) f223 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 497) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 492), (10, 482), (11, 296), (12, 496), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9cc) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 498) (RestInside.out (n := 498) f224 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 499) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 492), (10, 482), (11, 498), (12, 496), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9cf) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 500) (RestInside.out (n := 500) f225 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 501) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 492), (10, 482), (11, 500), (12, 496), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9d3) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 502) (RestInside.out (n := 502) f226 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 503) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 492), (10, 482), (11, 502), (12, 496), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9d6) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 504) (RestInside.out (n := 504) f227 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 505) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 492), (10, 482), (11, 504), (12, 496), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9d9) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 506) (RestInside.out (n := 506) f228 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 507) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9dc) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 508) (RestInside.out (n := 508) f229 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 509) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 508), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9df) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 510) (RestInside.out (n := 510) f230 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 511) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 510), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9e2) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 512) (RestInside.out (n := 512) f231 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 513) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 512), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 510), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9e5) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 514) (RestInside.out (n := 514) f232 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 515) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 514), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 510), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9e9) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 516) (RestInside.out (n := 516) f233 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 517) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 516), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 510), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9ec) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 518) (RestInside.out (n := 518) f234 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 519) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 510), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9ef) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 520) (RestInside.out (n := 520) f235 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 521) (ρ' := [(0, 520), (1, 384), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 510), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9f2) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 522) (RestInside.out (n := 522) f236 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 523) (ρ' := [(0, 522), (1, 384), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 510), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9f6) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 524) (RestInside.out (n := 524) f237 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 525) (ρ' := [(0, 522), (1, 384), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9f9) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 526) (RestInside.out (n := 526) f238 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 527) (ρ' := [(0, 526), (1, 384), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9fc) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 528) (RestInside.out (n := 528) f239 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 529) (ρ' := [(0, 526), (1, 528), (2, 484), (3, 518), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 506), (10, 482), (11, 504), (12, 496), (13, 524), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10aa06) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_12 code

theorem rest_l10a6a8_10 [Bindings] (code : CodeMap) :
    Rest (n := 450) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 438), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]
      86 0x10a977 bytes_l10a6a8_10 b_l10a6a8_10 := by
  have f200 : InstrSpec 0x10a977 [0x48, 0x21, 0xFD] (fun s => s.RIP = 0x10a977) (andR64R64Effect 0x10a977 5 7)
      [.gpr 5, .gpr 7] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a977 5 7).toInstrSpec (and_r64_r64_effect_step 0x10a977 0x48 0xfd (by decide) (by decide)) pre_rip
  have f201 : InstrSpec 0x10a97a [0x48, 0x31, 0xEB] (fun s => s.RIP = 0x10a97a) (xorR64R64Effect 0x10a97a 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a97a 3 5).toInstrSpec (xor_r64_r64_effect_step 0x10a97a 0x48 0xeb (by decide) (by decide)) pre_rip
  have f202 : InstrSpec 0x10a97d [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x10a97d) (movR64R64Effect 0x10a97d 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a97d 2 3).toInstrSpec (mov_r64_r64_effect_step 0x10a97d 0x48 0xda (by decide) (by decide)) pre_rip
  have f203 : InstrSpec 0x10a980 [0x48, 0xC1, 0xEA, 0x04] (fun s => s.RIP = 0x10a980) (shrR64Effect 0x10a980 4 2 4)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a980 4 2 4).toInstrSpec (shr_r64_imm8_effect_step 0x10a980 0x48 0xea 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f204 : InstrSpec 0x10a984 [0x4C, 0x31, 0xE6] (fun s => s.RIP = 0x10a984) (xorR64R64Effect 0x10a984 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a984 6 12).toInstrSpec (xor_r64_r64_effect_step 0x10a984 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f205 : InstrSpec 0x10a987 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x10a987) (movR64R64Effect 0x10a987 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10a987 15 6).toInstrSpec (mov_r64_r64_effect_step 0x10a987 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f206 : InstrSpec 0x10a98a [0x49, 0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x10a98a) (shrR64Effect 0x10a98a 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a98a 4 15 2).toInstrSpec (shr_r64_imm8_effect_step 0x10a98a 0x49 0xef 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f207 : InstrSpec 0x10a98e [0x4C, 0x31, 0xE8] (fun s => s.RIP = 0x10a98e) (xorR64R64Effect 0x10a98e 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a98e 0 13).toInstrSpec (xor_r64_r64_effect_step 0x10a98e 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f208 : InstrSpec 0x10a991 [0x49, 0x31, 0xC7] (fun s => s.RIP = 0x10a991) (xorR64R64Effect 0x10a991 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a991 15 0).toInstrSpec (xor_r64_r64_effect_step 0x10a991 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f209 : InstrSpec 0x10a994 [0x49, 0x21, 0xFF] (fun s => s.RIP = 0x10a994) (andR64R64Effect 0x10a994 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a994 15 7).toInstrSpec (and_r64_r64_effect_step 0x10a994 0x49 0xff (by decide) (by decide)) pre_rip
  have f210 : InstrSpec 0x10a997 [0x4C, 0x31, 0xF8] (fun s => s.RIP = 0x10a997) (xorR64R64Effect 0x10a997 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a997 0 15).toInstrSpec (xor_r64_r64_effect_step 0x10a997 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f211 : InstrSpec 0x10a99a [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x10a99a) (xorR64R64Effect 0x10a99a 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a99a 2 0).toInstrSpec (xor_r64_r64_effect_step 0x10a99a 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f212 : InstrSpec 0x10a99d [0x49, 0xBA, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F] (fun s => s.RIP = 0x10a99d) (movR64Imm64Effect 0x10a99d 10 0xf0f0f0f0f0f0f0f)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x10a99d 10 0xf0f0f0f0f0f0f0f).toInstrSpec (mov_r64_imm64_effect_step 0x10a99d 0x49 0xba (by decide) (by decide) 0xf0f0f0f0f0f0f0f) pre_rip
  have f213 : InstrSpec 0x10a9a7 [0x4C, 0x21, 0xD2] (fun s => s.RIP = 0x10a9a7) (andR64R64Effect 0x10a9a7 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a9a7 2 10).toInstrSpec (and_r64_r64_effect_step 0x10a9a7 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f214 : InstrSpec 0x10a9aa [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x10a9aa) (movR64R64Effect 0x10a9aa 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10a9aa 10 2).toInstrSpec (mov_r64_r64_effect_step 0x10a9aa 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f215 : InstrSpec 0x10a9ad [0x49, 0xC1, 0xE2, 0x04] (fun s => s.RIP = 0x10a9ad) (shlR64Effect 0x10a9ad 4 10 4)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a9ad 4 10 4).toInstrSpec (shl_r64_imm8_effect_step 0x10a9ad 0x49 0xe2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f216 : InstrSpec 0x10a9b1 [0x49, 0x31, 0xDA] (fun s => s.RIP = 0x10a9b1) (xorR64R64Effect 0x10a9b1 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9b1 10 3).toInstrSpec (xor_r64_r64_effect_step 0x10a9b1 0x49 0xda (by decide) (by decide)) pre_rip
  have f217 : InstrSpec 0x10a9b4 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x10a9b4) (xorR64R64Effect 0x10a9b4 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a9b4 2 0).toInstrSpec (xor_r64_r64_effect_step 0x10a9b4 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f218 : InstrSpec 0x10a9b7 [0x4D, 0x01, 0xC0] (fun s => s.RIP = 0x10a9b7) (addR64R64Effect 0x10a9b7 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a9b7 8 8).toInstrSpec (add_r64_r64_effect_step 0x10a9b7 0x4d 0xc0 (by decide) (by decide)) pre_rip
  have f219 : InstrSpec 0x10a9ba [0x4C, 0x33, 0x44, 0x24, 0x08] (LoadPre 0x10a9ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a9ba + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x10a9ba 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10a9ba 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_r64_m64_effect_step 0x10a9ba 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 450) (RestInside.out (n := 450) f200 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 451) (ρ' := [(0, 438), (1, 384), (2, 2), (3, 250), (4, 4), (5, 450), (6, 340), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a97a) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 452) (RestInside.out (n := 452) f201 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 453) (ρ' := [(0, 438), (1, 384), (2, 2), (3, 452), (4, 4), (5, 450), (6, 340), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a97d) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.out (n := 454) f202 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 455) (ρ' := [(0, 438), (1, 384), (2, 454), (3, 452), (4, 4), (5, 450), (6, 340), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a980) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 456) (RestInside.out (n := 456) f203 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 457) (ρ' := [(0, 438), (1, 384), (2, 456), (3, 452), (4, 4), (5, 450), (6, 340), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a984) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f204 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 438), (1, 384), (2, 456), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a987) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.out (n := 460) f205 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 461) (ρ' := [(0, 438), (1, 384), (2, 456), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 460), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a98a) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 462) (RestInside.out (n := 462) f206 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 463) (ρ' := [(0, 438), (1, 384), (2, 456), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 462), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a98e) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 464) (RestInside.out (n := 464) f207 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 465) (ρ' := [(0, 464), (1, 384), (2, 456), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 462), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a991) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.out (n := 466) f208 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 467) (ρ' := [(0, 464), (1, 384), (2, 456), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 466), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a994) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 468) (RestInside.out (n := 468) f209 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 469) (ρ' := [(0, 464), (1, 384), (2, 456), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a997) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 470) (RestInside.out (n := 470) f210 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 471) (ρ' := [(0, 470), (1, 384), (2, 456), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a99a) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 472) (RestInside.out (n := 472) f211 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 473) (ρ' := [(0, 470), (1, 384), (2, 472), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a99d) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 474) (RestInside.out (n := 474) f212 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 475) (ρ' := [(0, 470), (1, 384), (2, 472), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 474), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9a7) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f213 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 477) (ρ' := [(0, 470), (1, 384), (2, 476), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 474), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9aa) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 478) (RestInside.out (n := 478) f214 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 479) (ρ' := [(0, 470), (1, 384), (2, 476), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 478), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9ad) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 480) (RestInside.out (n := 480) f215 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 481) (ρ' := [(0, 470), (1, 384), (2, 476), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 480), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9b1) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 482) (RestInside.out (n := 482) f216 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 483) (ρ' := [(0, 470), (1, 384), (2, 476), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 482), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9b4) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 484) (RestInside.out (n := 484) f217 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 485) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 148), (9, 248), (10, 482), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9b7) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 486) (RestInside.out (n := 486) f218 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 487) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 486), (9, 248), (10, 482), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9ba) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 488) (RestInside.out (n := 488) f219 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 489) (ρ' := [(0, 470), (1, 384), (2, 484), (3, 452), (4, 4), (5, 450), (6, 458), (7, 448), (8, 488), (9, 248), (10, 482), (11, 296), (12, 432), (13, 446), (14, 390), (15, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a9bf) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_11 code

theorem rest_l10a6a8_9 [Bindings] (code : CodeMap) :
    Rest (n := 410) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 408), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 406), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]
      106 0x10a92e bytes_l10a6a8_9 b_l10a6a8_9 := by
  have f180 : InstrSpec 0x10a92e [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a92e) (shlR32Effect 0x10a92e 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a92e 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a92e 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x10a931 [0x48, 0x09, 0xF8] (fun s => s.RIP = 0x10a931) (orR64R64Effect 0x10a931 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a931 0 7).toInstrSpec (or_r64_r64_effect_step 0x10a931 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f182 : InstrSpec 0x10a934 [0x0F, 0xB6, 0x7A, 0x3D] (LoadPre 0x10a934 (fun s => AddrMode.addr (.base 2 (.d8 0x3d)) s (0x10a934 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a934 4 7 (.base 2 (.d8 0x3d)))
      [.gpr 2] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10a934 4 7 (.base 2 (.d8 0x3d))).toInstrSpec (movzx_r32_m8_effect_step 0x10a934 7 (.base 2 (.d8 0x3d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f183 : InstrSpec 0x10a938 [0xC1, 0xE7, 0x18] (fun s => s.RIP = 0x10a938) (shlR32Effect 0x10a938 3 7 24)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a938 3 7 24).toInstrSpec (shl_r32_imm8_effect_step 0x10a938 0xe7 0x18 (by decide) (by decide)) pre_rip
  have f184 : InstrSpec 0x10a93b [0x48, 0x09, 0xC7] (fun s => s.RIP = 0x10a93b) (orR64R64Effect 0x10a93b 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a93b 7 0).toInstrSpec (or_r64_r64_effect_step 0x10a93b 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f185 : InstrSpec 0x10a93e [0x44, 0x0F, 0xB6, 0x7A, 0x3E] (LoadPre 0x10a93e (fun s => AddrMode.addr (.base 2 (.d8 0x3e)) s (0x10a93e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a93e 5 15 (.base 2 (.d8 0x3e)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x10a93e 5 15 (.base 2 (.d8 0x3e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a93e 0x44 (by decide) 7 (.base 2 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f186 : InstrSpec 0x10a943 [0x49, 0xC1, 0xE7, 0x28] (fun s => s.RIP = 0x10a943) (shlR64Effect 0x10a943 4 15 40)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a943 4 15 40).toInstrSpec (shl_r64_imm8_effect_step 0x10a943 0x49 0xe7 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f187 : InstrSpec 0x10a947 [0x49, 0x09, 0xFF] (fun s => s.RIP = 0x10a947) (orR64R64Effect 0x10a947 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a947 15 7).toInstrSpec (or_r64_r64_effect_step 0x10a947 0x49 0xff (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x10a94a [0x4D, 0x89, 0xDC] (fun s => s.RIP = 0x10a94a) (movR64R64Effect 0x10a94a 12 11)
      [.gpr 11] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10a94a 12 11).toInstrSpec (mov_r64_r64_effect_step 0x10a94a 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f189 : InstrSpec 0x10a94d [0x49, 0xD1, 0xEC] (fun s => s.RIP = 0x10a94d) (shrR64Effect 0x10a94d 3 12 1)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a94d 3 12 1).toInstrSpec (shr_r64_one_effect_step 0x10a94d 0x49 0xec (by decide) (by decide) (by decide)) pre_rip
  have f190 : InstrSpec 0x10a950 [0x49, 0x31, 0xF4] (fun s => s.RIP = 0x10a950) (xorR64R64Effect 0x10a950 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a950 12 6).toInstrSpec (xor_r64_r64_effect_step 0x10a950 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x10a953 [0x4D, 0x21, 0xD4] (fun s => s.RIP = 0x10a953) (andR64R64Effect 0x10a953 12 10)
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a953 12 10).toInstrSpec (and_r64_r64_effect_step 0x10a953 0x4d 0xd4 (by decide) (by decide)) pre_rip
  have f192 : InstrSpec 0x10a956 [0x0F, 0xB6, 0x42, 0x3F] (LoadPre 0x10a956 (fun s => AddrMode.addr (.base 2 (.d8 0x3f)) s (0x10a956 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a956 4 0 (.base 2 (.d8 0x3f)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a956 4 0 (.base 2 (.d8 0x3f))).toInstrSpec (movzx_r32_m8_effect_step 0x10a956 0 (.base 2 (.d8 0x3f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f193 : InstrSpec 0x10a95a [0x48, 0xC1, 0xE0, 0x38] (fun s => s.RIP = 0x10a95a) (shlR64Effect 0x10a95a 4 0 56)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a95a 4 0 56).toInstrSpec (shl_r64_imm8_effect_step 0x10a95a 0x48 0xe0 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f194 : InstrSpec 0x10a95e [0x4C, 0x09, 0xF8] (fun s => s.RIP = 0x10a95e) (orR64R64Effect 0x10a95e 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a95e 0 15).toInstrSpec (or_r64_r64_effect_step 0x10a95e 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f195 : InstrSpec 0x10a961 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x10a961) (movR64R64Effect 0x10a961 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10a961 13 1).toInstrSpec (mov_r64_r64_effect_step 0x10a961 0x49 0xcd (by decide) (by decide)) pre_rip
  have f196 : InstrSpec 0x10a964 [0x49, 0xD1, 0xED] (fun s => s.RIP = 0x10a964) (shrR64Effect 0x10a964 3 13 1)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a964 3 13 1).toInstrSpec (shr_r64_one_effect_step 0x10a964 0x49 0xed (by decide) (by decide) (by decide)) pre_rip
  have f197 : InstrSpec 0x10a967 [0x49, 0x31, 0xC5] (fun s => s.RIP = 0x10a967) (xorR64R64Effect 0x10a967 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a967 13 0).toInstrSpec (xor_r64_r64_effect_step 0x10a967 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f198 : InstrSpec 0x10a96a [0x4D, 0x21, 0xD5] (fun s => s.RIP = 0x10a96a) (andR64R64Effect 0x10a96a 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a96a 13 10).toInstrSpec (and_r64_r64_effect_step 0x10a96a 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f199 : InstrSpec 0x10a96d [0x48, 0xBF, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33] (fun s => s.RIP = 0x10a96d) (movR64Imm64Effect 0x10a96d 7 0x3333333333333333)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x10a96d 7 0x3333333333333333).toInstrSpec (mov_r64_imm64_effect_step 0x10a96d 0x48 0xbf (by decide) (by decide) 0x3333333333333333) pre_rip
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f180 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 411) (ρ' := [(0, 410), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 406), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a931) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f181 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 413) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 406), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a934) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.out (n := 414) f182 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 415) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 414), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a938) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f183 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 416), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a93b) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.out (n := 418) f184 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 419) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a93e) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 420) (RestInside.out (n := 420) f185 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 421) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (15, 420), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a943) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 422) (RestInside.out (n := 422) f186 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 423) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (15, 422), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a947) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 424) (RestInside.out (n := 424) f187 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 425) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a94a) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 426) (RestInside.out (n := 426) f188 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 427) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 426), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a94d) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f189 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 428), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a950) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.out (n := 430) f190 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 431) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 430), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a953) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 432) (RestInside.out (n := 432) f191 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 433) (ρ' := [(0, 412), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a956) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 434) (RestInside.out (n := 434) f192 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 435) (ρ' := [(0, 434), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a95a) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 436) (RestInside.out (n := 436) f193 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 437) (ρ' := [(0, 436), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a95e) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 438) (RestInside.out (n := 438) f194 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 439) (ρ' := [(0, 438), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a961) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f195 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 441) (ρ' := [(0, 438), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 440), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a964) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.out (n := 442) f196 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 443) (ρ' := [(0, 438), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 442), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a967) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 444) (RestInside.out (n := 444) f197 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 445) (ρ' := [(0, 438), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 444), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a96a) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 446) (RestInside.out (n := 446) f198 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 447) (ρ' := [(0, 438), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 418), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a96d) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.out (n := 448) f199 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 449) (ρ' := [(0, 438), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 448), (8, 148), (9, 248), (10, 146), (11, 296), (12, 432), (13, 446), (14, 390), (15, 424), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a977) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_10 code

theorem rest_l10a6a8_8 [Bindings] (code : CodeMap) :
    Rest (n := 370) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 366), (1, 368), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]
      126 0x10a8e7 bytes_l10a6a8_8 b_l10a6a8_8 := by
  have f160 : InstrSpec 0x10a8e7 [0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x10a8e7) (shlR32Effect 0x10a8e7 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a8e7 3 1 24).toInstrSpec (shl_r32_imm8_effect_step 0x10a8e7 0xe1 0x18 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x10a8ea [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a8ea) (orR64R64Effect 0x10a8ea 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a8ea 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a8ea 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f162 : InstrSpec 0x10a8ed [0x0F, 0xB6, 0x42, 0x2E] (LoadPre 0x10a8ed (fun s => AddrMode.addr (.base 2 (.d8 0x2e)) s (0x10a8ed + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8ed 4 0 (.base 2 (.d8 0x2e)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8ed 4 0 (.base 2 (.d8 0x2e))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8ed 0 (.base 2 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f163 : InstrSpec 0x10a8f1 [0x48, 0xC1, 0xE0, 0x28] (fun s => s.RIP = 0x10a8f1) (shlR64Effect 0x10a8f1 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a8f1 4 0 40).toInstrSpec (shl_r64_imm8_effect_step 0x10a8f1 0x48 0xe0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f164 : InstrSpec 0x10a8f5 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a8f5) (orR64R64Effect 0x10a8f5 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a8f5 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a8f5 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x10a8f8 [0x0F, 0xB6, 0x4A, 0x2F] (LoadPre 0x10a8f8 (fun s => AddrMode.addr (.base 2 (.d8 0x2f)) s (0x10a8f8 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8f8 4 1 (.base 2 (.d8 0x2f)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8f8 4 1 (.base 2 (.d8 0x2f))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8f8 1 (.base 2 (.d8 0x2f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f166 : InstrSpec 0x10a8fc [0x48, 0xC1, 0xE1, 0x38] (fun s => s.RIP = 0x10a8fc) (shlR64Effect 0x10a8fc 4 1 56)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a8fc 4 1 56).toInstrSpec (shl_r64_imm8_effect_step 0x10a8fc 0x48 0xe1 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x10a900 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a900) (orR64R64Effect 0x10a900 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a900 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a900 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x10a903 [0x0F, 0xB6, 0x42, 0x35] (LoadPre 0x10a903 (fun s => AddrMode.addr (.base 2 (.d8 0x35)) s (0x10a903 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a903 4 0 (.base 2 (.d8 0x35)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a903 4 0 (.base 2 (.d8 0x35))).toInstrSpec (movzx_r32_m8_effect_step 0x10a903 0 (.base 2 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f169 : InstrSpec 0x10a907 [0xC1, 0xE0, 0x10] (fun s => s.RIP = 0x10a907) (shlR32Effect 0x10a907 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a907 3 0 16).toInstrSpec (shl_r32_imm8_effect_step 0x10a907 0xe0 0x10 (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x10a90a [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x10a90a) (movR64R64Effect 0x10a90a 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10a90a 14 7).toInstrSpec (mov_r64_r64_effect_step 0x10a90a 0x49 0xfe (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x10a90d [0x0F, 0xB6, 0x7A, 0x34] (LoadPre 0x10a90d (fun s => AddrMode.addr (.base 2 (.d8 0x34)) s (0x10a90d + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a90d 4 7 (.base 2 (.d8 0x34)))
      [.gpr 2] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10a90d 4 7 (.base 2 (.d8 0x34))).toInstrSpec (movzx_r32_m8_effect_step 0x10a90d 7 (.base 2 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f172 : InstrSpec 0x10a911 [0x48, 0x09, 0xC7] (fun s => s.RIP = 0x10a911) (orR64R64Effect 0x10a911 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a911 7 0).toInstrSpec (or_r64_r64_effect_step 0x10a911 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f173 : InstrSpec 0x10a914 [0x0F, 0xB6, 0x42, 0x36] (LoadPre 0x10a914 (fun s => AddrMode.addr (.base 2 (.d8 0x36)) s (0x10a914 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a914 4 0 (.base 2 (.d8 0x36)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a914 4 0 (.base 2 (.d8 0x36))).toInstrSpec (movzx_r32_m8_effect_step 0x10a914 0 (.base 2 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f174 : InstrSpec 0x10a918 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10a918) (shlR64Effect 0x10a918 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a918 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10a918 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x10a91c [0x48, 0x09, 0xF8] (fun s => s.RIP = 0x10a91c) (orR64R64Effect 0x10a91c 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a91c 0 7).toInstrSpec (or_r64_r64_effect_step 0x10a91c 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f176 : InstrSpec 0x10a91f [0x0F, 0xB6, 0x7A, 0x37] (LoadPre 0x10a91f (fun s => AddrMode.addr (.base 2 (.d8 0x37)) s (0x10a91f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a91f 4 7 (.base 2 (.d8 0x37)))
      [.gpr 2] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10a91f 4 7 (.base 2 (.d8 0x37))).toInstrSpec (movzx_r32_m8_effect_step 0x10a91f 7 (.base 2 (.d8 0x37)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f177 : InstrSpec 0x10a923 [0x48, 0xC1, 0xE7, 0x30] (fun s => s.RIP = 0x10a923) (shlR64Effect 0x10a923 4 7 48)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a923 4 7 48).toInstrSpec (shl_r64_imm8_effect_step 0x10a923 0x48 0xe7 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f178 : InstrSpec 0x10a927 [0x48, 0x09, 0xC7] (fun s => s.RIP = 0x10a927) (orR64R64Effect 0x10a927 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a927 7 0).toInstrSpec (or_r64_r64_effect_step 0x10a927 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f179 : InstrSpec 0x10a92a [0x0F, 0xB6, 0x42, 0x3C] (LoadPre 0x10a92a (fun s => AddrMode.addr (.base 2 (.d8 0x3c)) s (0x10a92a + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a92a 4 0 (.base 2 (.d8 0x3c)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a92a 4 0 (.base 2 (.d8 0x3c))).toInstrSpec (movzx_r32_m8_effect_step 0x10a92a 0 (.base 2 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 370) (RestInside.out (n := 370) f160 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 371) (ρ' := [(0, 366), (1, 370), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8ea) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.out (n := 372) f161 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 373) (ρ' := [(0, 366), (1, 372), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8ed) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 374) (RestInside.out (n := 374) f162 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 375) (ρ' := [(0, 374), (1, 372), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8f1) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f163 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 376), (1, 372), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8f5) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f164 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 378), (1, 372), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8f8) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f165 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 378), (1, 380), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8fc) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f166 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 378), (1, 382), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a900) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.out (n := 384) f167 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 385) (ρ' := [(0, 378), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a903) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 386) (RestInside.out (n := 386) f168 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 387) (ρ' := [(0, 386), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a907) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.out (n := 388) f169 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 389) (ρ' := [(0, 388), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a90a) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 390) (RestInside.out (n := 390) f170 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 391) (ρ' := [(0, 388), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a90d) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 392) (RestInside.out (n := 392) f171 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 393) (ρ' := [(0, 388), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 392), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a911) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.out (n := 394) f172 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 395) (ρ' := [(0, 388), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 394), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a914) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 396) (RestInside.out (n := 396) f173 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 397) (ρ' := [(0, 396), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 394), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a918) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f174 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 398), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 394), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a91c) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.out (n := 400) f175 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 401) (ρ' := [(0, 400), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 394), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a91f) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 402) (RestInside.out (n := 402) f176 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 403) (ρ' := [(0, 400), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 402), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a923) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f177 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 400), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 404), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a927) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f178 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 407) (ρ' := [(0, 400), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 406), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a92a) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 408) (RestInside.out (n := 408) f179 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 409) (ρ' := [(0, 408), (1, 384), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 406), (8, 148), (9, 248), (10, 146), (11, 296), (14, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a92e) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_9 code

theorem rest_l10a6a8_7 [Bindings] (code : CodeMap) :
    Rest (n := 330) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 322), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]
      146 0x10a89f bytes_l10a6a8_7 b_l10a6a8_7 := by
  have f140 : InstrSpec 0x10a89f [0x0F, 0xB6, 0x42, 0x1E] (LoadPre 0x10a89f (fun s => AddrMode.addr (.base 2 (.d8 0x1e)) s (0x10a89f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a89f 4 0 (.base 2 (.d8 0x1e)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a89f 4 0 (.base 2 (.d8 0x1e))).toInstrSpec (movzx_r32_m8_effect_step 0x10a89f 0 (.base 2 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f141 : InstrSpec 0x10a8a3 [0x48, 0xC1, 0xE0, 0x28] (fun s => s.RIP = 0x10a8a3) (shlR64Effect 0x10a8a3 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a8a3 4 0 40).toInstrSpec (shl_r64_imm8_effect_step 0x10a8a3 0x48 0xe0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x10a8a7 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a8a7) (orR64R64Effect 0x10a8a7 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a8a7 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a8a7 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x10a8aa [0x0F, 0xB6, 0x72, 0x1F] (LoadPre 0x10a8aa (fun s => AddrMode.addr (.base 2 (.d8 0x1f)) s (0x10a8aa + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8aa 4 6 (.base 2 (.d8 0x1f)))
      [.gpr 2] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8aa 4 6 (.base 2 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8aa 6 (.base 2 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f144 : InstrSpec 0x10a8ae [0x48, 0xC1, 0xE6, 0x38] (fun s => s.RIP = 0x10a8ae) (shlR64Effect 0x10a8ae 4 6 56)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a8ae 4 6 56).toInstrSpec (shl_r64_imm8_effect_step 0x10a8ae 0x48 0xe6 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x10a8b2 [0x48, 0x09, 0xC6] (fun s => s.RIP = 0x10a8b2) (orR64R64Effect 0x10a8b2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a8b2 6 0).toInstrSpec (or_r64_r64_effect_step 0x10a8b2 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f146 : InstrSpec 0x10a8b5 [0x0F, 0xB6, 0x42, 0x25] (LoadPre 0x10a8b5 (fun s => AddrMode.addr (.base 2 (.d8 0x25)) s (0x10a8b5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8b5 4 0 (.base 2 (.d8 0x25)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8b5 4 0 (.base 2 (.d8 0x25))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8b5 0 (.base 2 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f147 : InstrSpec 0x10a8b9 [0xC1, 0xE0, 0x10] (fun s => s.RIP = 0x10a8b9) (shlR32Effect 0x10a8b9 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a8b9 3 0 16).toInstrSpec (shl_r32_imm8_effect_step 0x10a8b9 0xe0 0x10 (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x10a8bc [0x0F, 0xB6, 0x4A, 0x24] (LoadPre 0x10a8bc (fun s => AddrMode.addr (.base 2 (.d8 0x24)) s (0x10a8bc + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8bc 4 1 (.base 2 (.d8 0x24)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8bc 4 1 (.base 2 (.d8 0x24))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8bc 1 (.base 2 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f149 : InstrSpec 0x10a8c0 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a8c0) (orR64R64Effect 0x10a8c0 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a8c0 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a8c0 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x10a8c3 [0x0F, 0xB6, 0x42, 0x26] (LoadPre 0x10a8c3 (fun s => AddrMode.addr (.base 2 (.d8 0x26)) s (0x10a8c3 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8c3 4 0 (.base 2 (.d8 0x26)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8c3 4 0 (.base 2 (.d8 0x26))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8c3 0 (.base 2 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f151 : InstrSpec 0x10a8c7 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10a8c7) (shlR64Effect 0x10a8c7 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a8c7 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10a8c7 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x10a8cb [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a8cb) (orR64R64Effect 0x10a8cb 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a8cb 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a8cb 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f153 : InstrSpec 0x10a8ce [0x0F, 0xB6, 0x4A, 0x27] (LoadPre 0x10a8ce (fun s => AddrMode.addr (.base 2 (.d8 0x27)) s (0x10a8ce + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8ce 4 1 (.base 2 (.d8 0x27)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8ce 4 1 (.base 2 (.d8 0x27))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8ce 1 (.base 2 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f154 : InstrSpec 0x10a8d2 [0x48, 0xC1, 0xE1, 0x30] (fun s => s.RIP = 0x10a8d2) (shlR64Effect 0x10a8d2 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a8d2 4 1 48).toInstrSpec (shl_r64_imm8_effect_step 0x10a8d2 0x48 0xe1 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x10a8d6 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a8d6) (orR64R64Effect 0x10a8d6 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a8d6 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a8d6 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x10a8d9 [0x0F, 0xB6, 0x42, 0x2C] (LoadPre 0x10a8d9 (fun s => AddrMode.addr (.base 2 (.d8 0x2c)) s (0x10a8d9 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8d9 4 0 (.base 2 (.d8 0x2c)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8d9 4 0 (.base 2 (.d8 0x2c))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8d9 0 (.base 2 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f157 : InstrSpec 0x10a8dd [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a8dd) (shlR32Effect 0x10a8dd 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a8dd 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a8dd 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x10a8e0 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a8e0) (orR64R64Effect 0x10a8e0 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a8e0 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a8e0 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x10a8e3 [0x0F, 0xB6, 0x4A, 0x2D] (LoadPre 0x10a8e3 (fun s => AddrMode.addr (.base 2 (.d8 0x2d)) s (0x10a8e3 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8e3 4 1 (.base 2 (.d8 0x2d)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a8e3 4 1 (.base 2 (.d8 0x2d))).toInstrSpec (movzx_r32_m8_effect_step 0x10a8e3 1 (.base 2 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f140 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 330), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8a3) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f141 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 332), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8a7) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f142 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 334), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8aa) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f143 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 334), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (6, 336), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8ae) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f144 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 339) (ρ' := [(0, 334), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (6, 338), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8b2) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 340) (RestInside.out (n := 340) f145 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 341) (ρ' := [(0, 334), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8b5) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f146 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 343) (ρ' := [(0, 342), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8b9) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f147 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 344), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8bc) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f148 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 344), (1, 346), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8c0) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f149 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 344), (1, 348), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8c3) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f150 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 351) (ρ' := [(0, 350), (1, 348), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8c7) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 352) (RestInside.out (n := 352) f151 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 353) (ρ' := [(0, 352), (1, 348), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8cb) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 354) (RestInside.out (n := 354) f152 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 355) (ρ' := [(0, 354), (1, 348), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8ce) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 356) (RestInside.out (n := 356) f153 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 357) (ρ' := [(0, 354), (1, 356), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8d2) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 358) (RestInside.out (n := 358) f154 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 359) (ρ' := [(0, 354), (1, 358), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8d6) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 360) (RestInside.out (n := 360) f155 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 361) (ρ' := [(0, 354), (1, 360), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8d9) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 362) (RestInside.out (n := 362) f156 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 363) (ρ' := [(0, 362), (1, 360), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8dd) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 364) (RestInside.out (n := 364) f157 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 365) (ρ' := [(0, 364), (1, 360), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8e0) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 366) (RestInside.out (n := 366) f158 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 367) (ρ' := [(0, 366), (1, 360), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8e3) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 368) (RestInside.out (n := 368) f159 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 369) (ρ' := [(0, 366), (1, 368), (2, 2), (3, 250), (4, 4), (5, 252), (6, 340), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a8e7) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_8 code

theorem rest_l10a6a8_6 [Bindings] (code : CodeMap) :
    Rest (n := 290) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 288), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]
      166 0x10a858 bytes_l10a6a8_6 b_l10a6a8_6 := by
  have f120 : InstrSpec 0x10a858 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a858) (orR64R64Effect 0x10a858 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a858 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a858 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x10a85b [0x44, 0x0F, 0xB6, 0x5A, 0x0F] (LoadPre 0x10a85b (fun s => AddrMode.addr (.base 2 (.d8 0xf)) s (0x10a85b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a85b 5 11 (.base 2 (.d8 0xf)))
      [.gpr 2] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x10a85b 5 11 (.base 2 (.d8 0xf))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a85b 0x44 (by decide) 3 (.base 2 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f122 : InstrSpec 0x10a860 [0x49, 0xC1, 0xE3, 0x38] (fun s => s.RIP = 0x10a860) (shlR64Effect 0x10a860 4 11 56)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a860 4 11 56).toInstrSpec (shl_r64_imm8_effect_step 0x10a860 0x49 0xe3 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x10a864 [0x49, 0x09, 0xC3] (fun s => s.RIP = 0x10a864) (orR64R64Effect 0x10a864 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a864 11 0).toInstrSpec (or_r64_r64_effect_step 0x10a864 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x10a867 [0x0F, 0xB6, 0x42, 0x15] (LoadPre 0x10a867 (fun s => AddrMode.addr (.base 2 (.d8 0x15)) s (0x10a867 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a867 4 0 (.base 2 (.d8 0x15)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a867 4 0 (.base 2 (.d8 0x15))).toInstrSpec (movzx_r32_m8_effect_step 0x10a867 0 (.base 2 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f125 : InstrSpec 0x10a86b [0xC1, 0xE0, 0x10] (fun s => s.RIP = 0x10a86b) (shlR32Effect 0x10a86b 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a86b 3 0 16).toInstrSpec (shl_r32_imm8_effect_step 0x10a86b 0xe0 0x10 (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x10a86e [0x0F, 0xB6, 0x4A, 0x14] (LoadPre 0x10a86e (fun s => AddrMode.addr (.base 2 (.d8 0x14)) s (0x10a86e + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a86e 4 1 (.base 2 (.d8 0x14)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a86e 4 1 (.base 2 (.d8 0x14))).toInstrSpec (movzx_r32_m8_effect_step 0x10a86e 1 (.base 2 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f127 : InstrSpec 0x10a872 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a872) (orR64R64Effect 0x10a872 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a872 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a872 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x10a875 [0x0F, 0xB6, 0x42, 0x16] (LoadPre 0x10a875 (fun s => AddrMode.addr (.base 2 (.d8 0x16)) s (0x10a875 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a875 4 0 (.base 2 (.d8 0x16)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a875 4 0 (.base 2 (.d8 0x16))).toInstrSpec (movzx_r32_m8_effect_step 0x10a875 0 (.base 2 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f129 : InstrSpec 0x10a879 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10a879) (shlR64Effect 0x10a879 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a879 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10a879 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x10a87d [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a87d) (orR64R64Effect 0x10a87d 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a87d 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a87d 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x10a880 [0x0F, 0xB6, 0x4A, 0x17] (LoadPre 0x10a880 (fun s => AddrMode.addr (.base 2 (.d8 0x17)) s (0x10a880 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a880 4 1 (.base 2 (.d8 0x17)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a880 4 1 (.base 2 (.d8 0x17))).toInstrSpec (movzx_r32_m8_effect_step 0x10a880 1 (.base 2 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f132 : InstrSpec 0x10a884 [0x48, 0xC1, 0xE1, 0x30] (fun s => s.RIP = 0x10a884) (shlR64Effect 0x10a884 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a884 4 1 48).toInstrSpec (shl_r64_imm8_effect_step 0x10a884 0x48 0xe1 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x10a888 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a888) (orR64R64Effect 0x10a888 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a888 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a888 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x10a88b [0x0F, 0xB6, 0x42, 0x1C] (LoadPre 0x10a88b (fun s => AddrMode.addr (.base 2 (.d8 0x1c)) s (0x10a88b + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a88b 4 0 (.base 2 (.d8 0x1c)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a88b 4 0 (.base 2 (.d8 0x1c))).toInstrSpec (movzx_r32_m8_effect_step 0x10a88b 0 (.base 2 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f135 : InstrSpec 0x10a88f [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a88f) (shlR32Effect 0x10a88f 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a88f 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a88f 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x10a892 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a892) (orR64R64Effect 0x10a892 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a892 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a892 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x10a895 [0x0F, 0xB6, 0x4A, 0x1D] (LoadPre 0x10a895 (fun s => AddrMode.addr (.base 2 (.d8 0x1d)) s (0x10a895 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a895 4 1 (.base 2 (.d8 0x1d)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a895 4 1 (.base 2 (.d8 0x1d))).toInstrSpec (movzx_r32_m8_effect_step 0x10a895 1 (.base 2 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f138 : InstrSpec 0x10a899 [0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x10a899) (shlR32Effect 0x10a899 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a899 3 1 24).toInstrSpec (shl_r32_imm8_effect_step 0x10a899 0xe1 0x18 (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x10a89c [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a89c) (orR64R64Effect 0x10a89c 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a89c 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a89c 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f120 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 290), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a85b) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f121 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 290), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a860) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f122 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 290), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a864) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.out (n := 296) f123 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 297) (ρ' := [(0, 290), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a867) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f124 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 298), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a86b) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f125 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 300), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a86e) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f126 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 300), (1, 302), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a872) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f127 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 300), (1, 304), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a875) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f128 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 306), (1, 304), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a879) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f129 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 308), (1, 304), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a87d) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f130 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 310), (1, 304), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a880) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f131 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 310), (1, 312), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a884) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f132 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 310), (1, 314), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a888) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f133 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 310), (1, 316), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a88b) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f134 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 318), (1, 316), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a88f) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f135 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 320), (1, 316), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a892) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f136 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 322), (1, 316), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a895) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f137 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 322), (1, 324), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a899) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f138 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 322), (1, 326), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a89c) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f139 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 329) (ρ' := [(0, 322), (1, 328), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (11, 296), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a89f) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_7 code

theorem rest_l10a6a8_5 [Bindings] (code : CodeMap) :
    Rest (n := 250) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 238), (1, 232), (2, 2), (3, 244), (4, 4), (5, 153), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]
      186 0x10a812 bytes_l10a6a8_5 b_l10a6a8_5 := by
  have f100 : InstrSpec 0x10a812 [0x4C, 0x31, 0xCB] (fun s => s.RIP = 0x10a812) (xorR64R64Effect 0x10a812 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a812 3 9).toInstrSpec (xor_r64_r64_effect_step 0x10a812 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x10a815 [0x48, 0x31, 0xDD] (fun s => s.RIP = 0x10a815) (xorR64R64Effect 0x10a815 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a815 5 3).toInstrSpec (xor_r64_r64_effect_step 0x10a815 0x48 0xdd (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x10a818 [0x0F, 0xB6, 0x42, 0x05] (LoadPre 0x10a818 (fun s => AddrMode.addr (.base 2 (.d8 0x5)) s (0x10a818 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a818 4 0 (.base 2 (.d8 0x5)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a818 4 0 (.base 2 (.d8 0x5))).toInstrSpec (movzx_r32_m8_effect_step 0x10a818 0 (.base 2 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f103 : InstrSpec 0x10a81c [0xC1, 0xE0, 0x10] (fun s => s.RIP = 0x10a81c) (shlR32Effect 0x10a81c 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a81c 3 0 16).toInstrSpec (shl_r32_imm8_effect_step 0x10a81c 0xe0 0x10 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x10a81f [0x0F, 0xB6, 0x4A, 0x04] (LoadPre 0x10a81f (fun s => AddrMode.addr (.base 2 (.d8 0x4)) s (0x10a81f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a81f 4 1 (.base 2 (.d8 0x4)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a81f 4 1 (.base 2 (.d8 0x4))).toInstrSpec (movzx_r32_m8_effect_step 0x10a81f 1 (.base 2 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f105 : InstrSpec 0x10a823 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a823) (orR64R64Effect 0x10a823 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a823 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a823 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x10a826 [0x0F, 0xB6, 0x42, 0x06] (LoadPre 0x10a826 (fun s => AddrMode.addr (.base 2 (.d8 0x6)) s (0x10a826 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a826 4 0 (.base 2 (.d8 0x6)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a826 4 0 (.base 2 (.d8 0x6))).toInstrSpec (movzx_r32_m8_effect_step 0x10a826 0 (.base 2 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f107 : InstrSpec 0x10a82a [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10a82a) (shlR64Effect 0x10a82a 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a82a 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10a82a 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x10a82e [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a82e) (orR64R64Effect 0x10a82e 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a82e 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a82e 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x10a831 [0x0F, 0xB6, 0x4A, 0x07] (LoadPre 0x10a831 (fun s => AddrMode.addr (.base 2 (.d8 0x7)) s (0x10a831 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a831 4 1 (.base 2 (.d8 0x7)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a831 4 1 (.base 2 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x10a831 1 (.base 2 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f110 : InstrSpec 0x10a835 [0x48, 0xC1, 0xE1, 0x30] (fun s => s.RIP = 0x10a835) (shlR64Effect 0x10a835 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a835 4 1 48).toInstrSpec (shl_r64_imm8_effect_step 0x10a835 0x48 0xe1 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x10a839 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a839) (orR64R64Effect 0x10a839 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a839 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a839 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x10a83c [0x0F, 0xB6, 0x42, 0x0C] (LoadPre 0x10a83c (fun s => AddrMode.addr (.base 2 (.d8 0xc)) s (0x10a83c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a83c 4 0 (.base 2 (.d8 0xc)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a83c 4 0 (.base 2 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x10a83c 0 (.base 2 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f113 : InstrSpec 0x10a840 [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a840) (shlR32Effect 0x10a840 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a840 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a840 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x10a843 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a843) (orR64R64Effect 0x10a843 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a843 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a843 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x10a846 [0x0F, 0xB6, 0x4A, 0x0D] (LoadPre 0x10a846 (fun s => AddrMode.addr (.base 2 (.d8 0xd)) s (0x10a846 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a846 4 1 (.base 2 (.d8 0xd)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a846 4 1 (.base 2 (.d8 0xd))).toInstrSpec (movzx_r32_m8_effect_step 0x10a846 1 (.base 2 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f116 : InstrSpec 0x10a84a [0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x10a84a) (shlR32Effect 0x10a84a 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a84a 3 1 24).toInstrSpec (shl_r32_imm8_effect_step 0x10a84a 0xe1 0x18 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x10a84d [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a84d) (orR64R64Effect 0x10a84d 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a84d 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a84d 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x10a850 [0x0F, 0xB6, 0x42, 0x0E] (LoadPre 0x10a850 (fun s => AddrMode.addr (.base 2 (.d8 0xe)) s (0x10a850 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a850 4 0 (.base 2 (.d8 0xe)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a850 4 0 (.base 2 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x10a850 0 (.base 2 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f119 : InstrSpec 0x10a854 [0x48, 0xC1, 0xE0, 0x28] (fun s => s.RIP = 0x10a854) (shlR64Effect 0x10a854 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a854 4 0 40).toInstrSpec (shl_r64_imm8_effect_step 0x10a854 0x48 0xe0 0x28 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f100 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 238), (1, 232), (2, 2), (3, 250), (4, 4), (5, 153), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a815) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f101 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 238), (1, 232), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a818) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f102 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 254), (1, 232), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a81c) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f103 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(0, 256), (1, 232), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a81f) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.out (n := 258) f104 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 259) (ρ' := [(0, 256), (1, 258), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a823) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.out (n := 260) f105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 261) (ρ' := [(0, 256), (1, 260), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a826) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f106 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 262), (1, 260), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a82a) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f107 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 264), (1, 260), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a82e) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f108 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 266), (1, 260), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a831) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f109 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 266), (1, 268), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a835) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f110 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 266), (1, 270), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a839) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f111 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 266), (1, 272), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a83c) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f112 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 274), (1, 272), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a840) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f113 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 276), (1, 272), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a843) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f114 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 278), (1, 272), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a846) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f115 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 278), (1, 280), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a84a) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f116 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 278), (1, 282), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a84d) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f117 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 278), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a850) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f118 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 286), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a854) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f119 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 288), (1, 284), (2, 2), (3, 250), (4, 4), (5, 252), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a858) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_6 code

theorem rest_l10a6a8_4 [Bindings] (code : CodeMap) :
    Rest (n := 210) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 204), (1, 208), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]
      206 0x10a7cc bytes_l10a6a8_4 b_l10a6a8_4 := by
  have f80 : InstrSpec 0x10a7cc [0x0F, 0xB6, 0x42, 0x32] (LoadPre 0x10a7cc (fun s => AddrMode.addr (.base 2 (.d8 0x32)) s (0x10a7cc + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7cc 4 0 (.base 2 (.d8 0x32)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7cc 4 0 (.base 2 (.d8 0x32))).toInstrSpec (movzx_r32_m8_effect_step 0x10a7cc 0 (.base 2 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f81 : InstrSpec 0x10a7d0 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10a7d0) (shlR64Effect 0x10a7d0 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a7d0 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10a7d0 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x10a7d4 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a7d4) (orR64R64Effect 0x10a7d4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a7d4 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a7d4 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x10a7d7 [0x0F, 0xB6, 0x4A, 0x33] (LoadPre 0x10a7d7 (fun s => AddrMode.addr (.base 2 (.d8 0x33)) s (0x10a7d7 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7d7 4 1 (.base 2 (.d8 0x33)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7d7 4 1 (.base 2 (.d8 0x33))).toInstrSpec (movzx_r32_m8_effect_step 0x10a7d7 1 (.base 2 (.d8 0x33)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f84 : InstrSpec 0x10a7db [0x48, 0xC1, 0xE1, 0x30] (fun s => s.RIP = 0x10a7db) (shlR64Effect 0x10a7db 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a7db 4 1 48).toInstrSpec (shl_r64_imm8_effect_step 0x10a7db 0x48 0xe1 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x10a7df [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a7df) (orR64R64Effect 0x10a7df 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a7df 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a7df 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x10a7e2 [0x0F, 0xB6, 0x42, 0x38] (LoadPre 0x10a7e2 (fun s => AddrMode.addr (.base 2 (.d8 0x38)) s (0x10a7e2 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7e2 4 0 (.base 2 (.d8 0x38)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7e2 4 0 (.base 2 (.d8 0x38))).toInstrSpec (movzx_r32_m8_effect_step 0x10a7e2 0 (.base 2 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f87 : InstrSpec 0x10a7e6 [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a7e6) (shlR32Effect 0x10a7e6 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a7e6 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a7e6 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x10a7e9 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a7e9) (orR64R64Effect 0x10a7e9 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a7e9 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a7e9 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x10a7ec [0x0F, 0xB6, 0x4A, 0x39] (LoadPre 0x10a7ec (fun s => AddrMode.addr (.base 2 (.d8 0x39)) s (0x10a7ec + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7ec 4 1 (.base 2 (.d8 0x39)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7ec 4 1 (.base 2 (.d8 0x39))).toInstrSpec (movzx_r32_m8_effect_step 0x10a7ec 1 (.base 2 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f90 : InstrSpec 0x10a7f0 [0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x10a7f0) (shlR32Effect 0x10a7f0 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a7f0 3 1 24).toInstrSpec (shl_r32_imm8_effect_step 0x10a7f0 0xe1 0x18 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x10a7f3 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a7f3) (orR64R64Effect 0x10a7f3 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a7f3 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a7f3 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x10a7f6 [0x0F, 0xB6, 0x42, 0x3A] (LoadPre 0x10a7f6 (fun s => AddrMode.addr (.base 2 (.d8 0x3a)) s (0x10a7f6 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7f6 4 0 (.base 2 (.d8 0x3a)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7f6 4 0 (.base 2 (.d8 0x3a))).toInstrSpec (movzx_r32_m8_effect_step 0x10a7f6 0 (.base 2 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f93 : InstrSpec 0x10a7fa [0x48, 0xC1, 0xE0, 0x28] (fun s => s.RIP = 0x10a7fa) (shlR64Effect 0x10a7fa 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a7fa 4 0 40).toInstrSpec (shl_r64_imm8_effect_step 0x10a7fa 0x48 0xe0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x10a7fe [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a7fe) (orR64R64Effect 0x10a7fe 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a7fe 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a7fe 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x10a801 [0x0F, 0xB6, 0x5A, 0x3B] (LoadPre 0x10a801 (fun s => AddrMode.addr (.base 2 (.d8 0x3b)) s (0x10a801 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a801 4 3 (.base 2 (.d8 0x3b)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x10a801 4 3 (.base 2 (.d8 0x3b))).toInstrSpec (movzx_r32_m8_effect_step 0x10a801 3 (.base 2 (.d8 0x3b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f96 : InstrSpec 0x10a805 [0x48, 0xC1, 0xE3, 0x38] (fun s => s.RIP = 0x10a805) (shlR64Effect 0x10a805 4 3 56)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a805 4 3 56).toInstrSpec (shl_r64_imm8_effect_step 0x10a805 0x48 0xe3 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x10a809 [0x48, 0x09, 0xC3] (fun s => s.RIP = 0x10a809) (orR64R64Effect 0x10a809 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a809 3 0).toInstrSpec (or_r64_r64_effect_step 0x10a809 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x10a80c [0x49, 0x31, 0xD9] (fun s => s.RIP = 0x10a80c) (xorR64R64Effect 0x10a80c 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a80c 9 3).toInstrSpec (xor_r64_r64_effect_step 0x10a80c 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x10a80f [0x4D, 0x21, 0xD1] (fun s => s.RIP = 0x10a80f) (andR64R64Effect 0x10a80f 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a80f 9 10).toInstrSpec (and_r64_r64_effect_step 0x10a80f 0x4d 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f80 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 210), (1, 208), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7d0) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f81 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 212), (1, 208), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7d4) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f82 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 214), (1, 208), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7d7) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 214), (1, 216), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7db) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 214), (1, 218), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7df) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 214), (1, 220), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7e2) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f86 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 222), (1, 220), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7e6) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f87 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 224), (1, 220), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7e9) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f88 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 226), (1, 220), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7ec) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f89 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 229) (ρ' := [(0, 226), (1, 228), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7f0) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f90 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 226), (1, 230), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7f3) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f91 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 226), (1, 232), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7f6) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f92 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 234), (1, 232), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7fa) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f93 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 236), (1, 232), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7fe) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f94 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 238), (1, 232), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a801) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f95 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 238), (1, 232), (2, 2), (3, 240), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a805) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f96 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 238), (1, 232), (2, 2), (3, 242), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a809) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f97 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 238), (1, 232), (2, 2), (3, 244), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a80c) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f98 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 238), (1, 232), (2, 2), (3, 244), (4, 4), (5, 153), (7, 7), (8, 148), (9, 246), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a80f) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f99 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 238), (1, 232), (2, 2), (3, 244), (4, 4), (5, 153), (7, 7), (8, 148), (9, 248), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a812) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_5 code

theorem rest_l10a6a8_3 [Bindings] (code : CodeMap) :
    Rest (n := 171) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 167), (1, 169), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]
      226 0x10a785 bytes_l10a6a8_3 b_l10a6a8_3 := by
  have f60 : InstrSpec 0x10a785 [0x48, 0xC1, 0xE1, 0x30] (fun s => s.RIP = 0x10a785) (shlR64Effect 0x10a785 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a785 4 1 48).toInstrSpec (shl_r64_imm8_effect_step 0x10a785 0x48 0xe1 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x10a789 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a789) (orR64R64Effect 0x10a789 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a789 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a789 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x10a78c [0x0F, 0xB6, 0x42, 0x28] (LoadPre 0x10a78c (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x10a78c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a78c 4 0 (.base 2 (.d8 0x28)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a78c 4 0 (.base 2 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x10a78c 0 (.base 2 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f63 : InstrSpec 0x10a790 [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a790) (shlR32Effect 0x10a790 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a790 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a790 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x10a793 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a793) (orR64R64Effect 0x10a793 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a793 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a793 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x10a796 [0x0F, 0xB6, 0x4A, 0x29] (LoadPre 0x10a796 (fun s => AddrMode.addr (.base 2 (.d8 0x29)) s (0x10a796 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a796 4 1 (.base 2 (.d8 0x29)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a796 4 1 (.base 2 (.d8 0x29))).toInstrSpec (movzx_r32_m8_effect_step 0x10a796 1 (.base 2 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x10a79a [0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x10a79a) (shlR32Effect 0x10a79a 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a79a 3 1 24).toInstrSpec (shl_r32_imm8_effect_step 0x10a79a 0xe1 0x18 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x10a79d [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a79d) (orR64R64Effect 0x10a79d 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a79d 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a79d 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x10a7a0 [0x0F, 0xB6, 0x42, 0x2A] (LoadPre 0x10a7a0 (fun s => AddrMode.addr (.base 2 (.d8 0x2a)) s (0x10a7a0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7a0 4 0 (.base 2 (.d8 0x2a)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7a0 4 0 (.base 2 (.d8 0x2a))).toInstrSpec (movzx_r32_m8_effect_step 0x10a7a0 0 (.base 2 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f69 : InstrSpec 0x10a7a4 [0x48, 0xC1, 0xE0, 0x28] (fun s => s.RIP = 0x10a7a4) (shlR64Effect 0x10a7a4 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a7a4 4 0 40).toInstrSpec (shl_r64_imm8_effect_step 0x10a7a4 0x48 0xe0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10a7a8 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a7a8) (orR64R64Effect 0x10a7a8 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a7a8 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a7a8 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x10a7ab [0x44, 0x0F, 0xB6, 0x4A, 0x2B] (LoadPre 0x10a7ab (fun s => AddrMode.addr (.base 2 (.d8 0x2b)) s (0x10a7ab + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a7ab 5 9 (.base 2 (.d8 0x2b)))
      [.gpr 2] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7ab 5 9 (.base 2 (.d8 0x2b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a7ab 0x44 (by decide) 1 (.base 2 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x10a7b0 [0x49, 0xC1, 0xE1, 0x38] (fun s => s.RIP = 0x10a7b0) (shlR64Effect 0x10a7b0 4 9 56)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a7b0 4 9 56).toInstrSpec (shl_r64_imm8_effect_step 0x10a7b0 0x49 0xe1 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10a7b4 [0x49, 0x09, 0xC1] (fun s => s.RIP = 0x10a7b4) (orR64R64Effect 0x10a7b4 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a7b4 9 0).toInstrSpec (or_r64_r64_effect_step 0x10a7b4 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10a7b7 [0x4C, 0x89, 0x0C, 0x24] (StorePre 0x10a7b7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a7b7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a7b7 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a7b7 9 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a7b7 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x10a7bb [0x49, 0xD1, 0xE9] (fun s => s.RIP = 0x10a7bb) (shrR64Effect 0x10a7bb 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a7bb 3 9 1).toInstrSpec (shr_r64_one_effect_step 0x10a7bb 0x49 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x10a7be [0x0F, 0xB6, 0x42, 0x31] (LoadPre 0x10a7be (fun s => AddrMode.addr (.base 2 (.d8 0x31)) s (0x10a7be + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7be 4 0 (.base 2 (.d8 0x31)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7be 4 0 (.base 2 (.d8 0x31))).toInstrSpec (movzx_r32_m8_effect_step 0x10a7be 0 (.base 2 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f77 : InstrSpec 0x10a7c2 [0xC1, 0xE0, 0x10] (fun s => s.RIP = 0x10a7c2) (shlR32Effect 0x10a7c2 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a7c2 3 0 16).toInstrSpec (shl_r32_imm8_effect_step 0x10a7c2 0xe0 0x10 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x10a7c5 [0x0F, 0xB6, 0x4A, 0x30] (LoadPre 0x10a7c5 (fun s => AddrMode.addr (.base 2 (.d8 0x30)) s (0x10a7c5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7c5 4 1 (.base 2 (.d8 0x30)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a7c5 4 1 (.base 2 (.d8 0x30))).toInstrSpec (movzx_r32_m8_effect_step 0x10a7c5 1 (.base 2 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f79 : InstrSpec 0x10a7c9 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a7c9) (orR64R64Effect 0x10a7c9 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a7c9 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a7c9 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f60 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 167), (1, 171), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a789) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f61 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 167), (1, 173), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a78c) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f62 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 175), (1, 173), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a790) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f63 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 177), (1, 173), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a793) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f64 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 179), (1, 173), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a796) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f65 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 179), (1, 181), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a79a) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f66 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 179), (1, 183), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a79d) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 179), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7a0) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f68 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 187), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7a4) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f69 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 189), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7a8) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 191), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7ab) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f71 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 191), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 193), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7b0) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f72 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 191), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 195), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7b4) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f73 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 191), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 197), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7b7) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.exec (n := 199) (ρ' := [(0, 191), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 197), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7bb) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f75 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 191), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7be) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f76 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 202), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7c2) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f77 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 204), (1, 185), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7c5) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f78 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 204), (1, 206), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7c9) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 204), (1, 208), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (9, 200), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a7cc) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_4 code

theorem rest_l10a6a8_2 [Bindings] (code : CodeMap) :
    Rest (n := 132) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 124), (1, 130), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]
      246 0x10a736 bytes_l10a6a8_2 b_l10a6a8_2 := by
  have f40 : InstrSpec 0x10a736 [0x0F, 0xB6, 0x42, 0x1A] (LoadPre 0x10a736 (fun s => AddrMode.addr (.base 2 (.d8 0x1a)) s (0x10a736 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a736 4 0 (.base 2 (.d8 0x1a)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a736 4 0 (.base 2 (.d8 0x1a))).toInstrSpec (movzx_r32_m8_effect_step 0x10a736 0 (.base 2 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10a73a [0x48, 0xC1, 0xE0, 0x28] (fun s => s.RIP = 0x10a73a) (shlR64Effect 0x10a73a 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a73a 4 0 40).toInstrSpec (shl_r64_imm8_effect_step 0x10a73a 0x48 0xe0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x10a73e [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a73e) (orR64R64Effect 0x10a73e 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a73e 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a73e 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x10a741 [0x0F, 0xB6, 0x6A, 0x1B] (LoadPre 0x10a741 (fun s => AddrMode.addr (.base 2 (.d8 0x1b)) s (0x10a741 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a741 4 5 (.base 2 (.d8 0x1b)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x10a741 4 5 (.base 2 (.d8 0x1b))).toInstrSpec (movzx_r32_m8_effect_step 0x10a741 5 (.base 2 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x10a745 [0x48, 0xC1, 0xE5, 0x38] (fun s => s.RIP = 0x10a745) (shlR64Effect 0x10a745 4 5 56)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a745 4 5 56).toInstrSpec (shl_r64_imm8_effect_step 0x10a745 0x48 0xe5 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10a749 [0x48, 0x09, 0xC5] (fun s => s.RIP = 0x10a749) (orR64R64Effect 0x10a749 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a749 5 0).toInstrSpec (or_r64_r64_effect_step 0x10a749 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10a74c [0x49, 0x31, 0xE8] (fun s => s.RIP = 0x10a74c) (xorR64R64Effect 0x10a74c 8 5)
      [.gpr 8, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a74c 8 5).toInstrSpec (xor_r64_r64_effect_step 0x10a74c 0x49 0xe8 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10a74f [0x49, 0xBA, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55] (fun s => s.RIP = 0x10a74f) (movR64Imm64Effect 0x10a74f 10 0x5555555555555555)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x10a74f 10 0x5555555555555555).toInstrSpec (mov_r64_imm64_effect_step 0x10a74f 0x49 0xba (by decide) (by decide) 0x5555555555555555) pre_rip
  have f48 : InstrSpec 0x10a759 [0x4D, 0x21, 0xD0] (fun s => s.RIP = 0x10a759) (andR64R64Effect 0x10a759 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a759 8 10).toInstrSpec (and_r64_r64_effect_step 0x10a759 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10a75c [0x4C, 0x31, 0xC5] (fun s => s.RIP = 0x10a75c) (xorR64R64Effect 0x10a75c 5 8)
      [.gpr 5, .gpr 8] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a75c 5 8).toInstrSpec (xor_r64_r64_effect_step 0x10a75c 0x4c 0xc5 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10a75f [0x48, 0x89, 0x6C, 0x24, 0x10] (StorePre 0x10a75f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a75f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a75f 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a75f 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10a75f 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x10a764 [0x48, 0xC1, 0xED, 0x02] (fun s => s.RIP = 0x10a764) (shrR64Effect 0x10a764 4 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a764 4 5 2).toInstrSpec (shr_r64_imm8_effect_step 0x10a764 0x48 0xed 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10a768 [0x0F, 0xB6, 0x42, 0x21] (LoadPre 0x10a768 (fun s => AddrMode.addr (.base 2 (.d8 0x21)) s (0x10a768 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a768 4 0 (.base 2 (.d8 0x21)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a768 4 0 (.base 2 (.d8 0x21))).toInstrSpec (movzx_r32_m8_effect_step 0x10a768 0 (.base 2 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x10a76c [0xC1, 0xE0, 0x10] (fun s => s.RIP = 0x10a76c) (shlR32Effect 0x10a76c 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a76c 3 0 16).toInstrSpec (shl_r32_imm8_effect_step 0x10a76c 0xe0 0x10 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x10a76f [0x0F, 0xB6, 0x4A, 0x20] (LoadPre 0x10a76f (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x10a76f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a76f 4 1 (.base 2 (.d8 0x20)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a76f 4 1 (.base 2 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x10a76f 1 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x10a773 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a773) (orR64R64Effect 0x10a773 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a773 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a773 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x10a776 [0x0F, 0xB6, 0x42, 0x22] (LoadPre 0x10a776 (fun s => AddrMode.addr (.base 2 (.d8 0x22)) s (0x10a776 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a776 4 0 (.base 2 (.d8 0x22)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a776 4 0 (.base 2 (.d8 0x22))).toInstrSpec (movzx_r32_m8_effect_step 0x10a776 0 (.base 2 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f57 : InstrSpec 0x10a77a [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10a77a) (shlR64Effect 0x10a77a 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a77a 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10a77a 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10a77e [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a77e) (orR64R64Effect 0x10a77e 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a77e 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a77e 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10a781 [0x0F, 0xB6, 0x4A, 0x23] (LoadPre 0x10a781 (fun s => AddrMode.addr (.base 2 (.d8 0x23)) s (0x10a781 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a781 4 1 (.base 2 (.d8 0x23)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a781 4 1 (.base 2 (.d8 0x23))).toInstrSpec (movzx_r32_m8_effect_step 0x10a781 1 (.base 2 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 132), (1, 130), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a73a) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f41 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 134), (1, 130), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a73e) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f42 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a741) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f43 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 138), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a745) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f44 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 140), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a749) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f45 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 142), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a74c) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f46 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 142), (7, 7), (8, 144), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a74f) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f47 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 142), (7, 7), (8, 144), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a759) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f48 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 142), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a75c) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f49 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 150), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a75f) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.exec (n := 152) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 150), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a764) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f51 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 136), (1, 130), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a768) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 155), (1, 130), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a76c) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 157), (1, 130), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a76f) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 157), (1, 159), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a773) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 157), (1, 161), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a776) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f56 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 163), (1, 161), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a77a) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f57 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 165), (1, 161), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a77e) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 167), (1, 161), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a781) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 167), (1, 169), (2, 2), (4, 4), (5, 153), (7, 7), (8, 148), (10, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a785) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_3 code

theorem rest_l10a6a8_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) [(0, 89), (1, 83), (2, 2), (4, 4), (7, 7), (8, 91), (22, 22), (39, 39), (50, 50), (51, 51)]
      266 0x10a6ef bytes_l10a6a8_1 b_l10a6a8_1 := by
  have f20 : InstrSpec 0x10a6ef [0x49, 0xC1, 0xE0, 0x38] (fun s => s.RIP = 0x10a6ef) (shlR64Effect 0x10a6ef 4 8 56)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a6ef 4 8 56).toInstrSpec (shl_r64_imm8_effect_step 0x10a6ef 0x49 0xe0 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10a6f3 [0x49, 0x09, 0xC0] (fun s => s.RIP = 0x10a6f3) (orR64R64Effect 0x10a6f3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a6f3 8 0).toInstrSpec (or_r64_r64_effect_step 0x10a6f3 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10a6f6 [0x4C, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10a6f6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a6f6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a6f6 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a6f6 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10a6f6 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x10a6fb [0x49, 0xD1, 0xE8] (fun s => s.RIP = 0x10a6fb) (shrR64Effect 0x10a6fb 3 8 1)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a6fb 3 8 1).toInstrSpec (shr_r64_one_effect_step 0x10a6fb 0x49 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x10a6fe [0x0F, 0xB6, 0x42, 0x11] (LoadPre 0x10a6fe (fun s => AddrMode.addr (.base 2 (.d8 0x11)) s (0x10a6fe + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6fe 4 0 (.base 2 (.d8 0x11)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6fe 4 0 (.base 2 (.d8 0x11))).toInstrSpec (movzx_r32_m8_effect_step 0x10a6fe 0 (.base 2 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x10a702 [0xC1, 0xE0, 0x10] (fun s => s.RIP = 0x10a702) (shlR32Effect 0x10a702 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a702 3 0 16).toInstrSpec (shl_r32_imm8_effect_step 0x10a702 0xe0 0x10 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10a705 [0x0F, 0xB6, 0x4A, 0x10] (LoadPre 0x10a705 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x10a705 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a705 4 1 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a705 4 1 (.base 2 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x10a705 1 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x10a709 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a709) (orR64R64Effect 0x10a709 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a709 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a709 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10a70c [0x0F, 0xB6, 0x42, 0x12] (LoadPre 0x10a70c (fun s => AddrMode.addr (.base 2 (.d8 0x12)) s (0x10a70c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a70c 4 0 (.base 2 (.d8 0x12)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a70c 4 0 (.base 2 (.d8 0x12))).toInstrSpec (movzx_r32_m8_effect_step 0x10a70c 0 (.base 2 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x10a710 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10a710) (shlR64Effect 0x10a710 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a710 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10a710 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10a714 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a714) (orR64R64Effect 0x10a714 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a714 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a714 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10a717 [0x0F, 0xB6, 0x4A, 0x13] (LoadPre 0x10a717 (fun s => AddrMode.addr (.base 2 (.d8 0x13)) s (0x10a717 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a717 4 1 (.base 2 (.d8 0x13)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a717 4 1 (.base 2 (.d8 0x13))).toInstrSpec (movzx_r32_m8_effect_step 0x10a717 1 (.base 2 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x10a71b [0x48, 0xC1, 0xE1, 0x30] (fun s => s.RIP = 0x10a71b) (shlR64Effect 0x10a71b 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a71b 4 1 48).toInstrSpec (shl_r64_imm8_effect_step 0x10a71b 0x48 0xe1 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10a71f [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a71f) (orR64R64Effect 0x10a71f 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a71f 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a71f 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10a722 [0x0F, 0xB6, 0x42, 0x18] (LoadPre 0x10a722 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x10a722 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a722 4 0 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a722 4 0 (.base 2 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x10a722 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x10a726 [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a726) (shlR32Effect 0x10a726 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a726 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a726 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10a729 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a729) (orR64R64Effect 0x10a729 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a729 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a729 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10a72c [0x0F, 0xB6, 0x4A, 0x19] (LoadPre 0x10a72c (fun s => AddrMode.addr (.base 2 (.d8 0x19)) s (0x10a72c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a72c 4 1 (.base 2 (.d8 0x19)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a72c 4 1 (.base 2 (.d8 0x19))).toInstrSpec (movzx_r32_m8_effect_step 0x10a72c 1 (.base 2 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x10a730 [0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x10a730) (shlR32Effect 0x10a730 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a730 3 1 24).toInstrSpec (shl_r32_imm8_effect_step 0x10a730 0xe1 0x18 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10a733 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a733) (orR64R64Effect 0x10a733 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a733 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a733 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 83), (2, 2), (4, 4), (7, 7), (8, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6f3) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 89), (1, 83), (2, 2), (4, 4), (7, 7), (8, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6f6) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 89), (1, 83), (2, 2), (4, 4), (7, 7), (8, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6fb) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 89), (1, 83), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6fe) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 100), (1, 83), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a702) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 102), (1, 83), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a705) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 102), (1, 104), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a709) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 102), (1, 106), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a70c) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 108), (1, 106), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a710) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 110), (1, 106), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a714) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 112), (1, 106), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a717) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 112), (1, 114), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a71b) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 112), (1, 116), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a71f) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 112), (1, 118), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a722) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 120), (1, 118), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a726) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 122), (1, 118), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a729) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 124), (1, 118), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a72c) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 124), (1, 126), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a730) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 124), (1, 128), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a733) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 124), (1, 130), (2, 2), (4, 4), (7, 7), (8, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a736) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_2 code

theorem rest_l10a6a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a6a8 bytes_l10a6a8) (entryMap (live .l10a6a8))
      286 0x10a6a8 bytes_l10a6a8 b_l10a6a8 := by
  have f0 : InstrSpec 0x10a6a8 [0x0F, 0xB6, 0x42, 0x01] (LoadPre 0x10a6a8 (fun s => AddrMode.addr (.base 2 (.d8 0x1)) s (0x10a6a8 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6a8 4 0 (.base 2 (.d8 0x1)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6a8 4 0 (.base 2 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x10a6a8 0 (.base 2 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10a6ac [0xC1, 0xE0, 0x10] (fun s => s.RIP = 0x10a6ac) (shlR32Effect 0x10a6ac 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a6ac 3 0 16).toInstrSpec (shl_r32_imm8_effect_step 0x10a6ac 0xe0 0x10 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a6af [0x0F, 0xB6, 0x0A] (LoadPre 0x10a6af (fun s => AddrMode.addr (.base 2 .none) s (0x10a6af + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x10a6af 3 1 (.base 2 .none))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6af 3 1 (.base 2 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x10a6af 1 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10a6b2 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a6b2) (orR64R64Effect 0x10a6b2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a6b2 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a6b2 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10a6b5 [0x0F, 0xB6, 0x42, 0x02] (LoadPre 0x10a6b5 (fun s => AddrMode.addr (.base 2 (.d8 0x2)) s (0x10a6b5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6b5 4 0 (.base 2 (.d8 0x2)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6b5 4 0 (.base 2 (.d8 0x2))).toInstrSpec (movzx_r32_m8_effect_step 0x10a6b5 0 (.base 2 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10a6b9 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x10a6b9) (shlR64Effect 0x10a6b9 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a6b9 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x10a6b9 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10a6bd [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a6bd) (orR64R64Effect 0x10a6bd 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a6bd 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a6bd 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10a6c0 [0x0F, 0xB6, 0x4A, 0x03] (LoadPre 0x10a6c0 (fun s => AddrMode.addr (.base 2 (.d8 0x3)) s (0x10a6c0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6c0 4 1 (.base 2 (.d8 0x3)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6c0 4 1 (.base 2 (.d8 0x3))).toInstrSpec (movzx_r32_m8_effect_step 0x10a6c0 1 (.base 2 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10a6c4 [0x48, 0xC1, 0xE1, 0x30] (fun s => s.RIP = 0x10a6c4) (shlR64Effect 0x10a6c4 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a6c4 4 1 48).toInstrSpec (shl_r64_imm8_effect_step 0x10a6c4 0x48 0xe1 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10a6c8 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a6c8) (orR64R64Effect 0x10a6c8 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a6c8 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a6c8 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10a6cb [0x0F, 0xB6, 0x42, 0x08] (LoadPre 0x10a6cb (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x10a6cb + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6cb 4 0 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6cb 4 0 (.base 2 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x10a6cb 0 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10a6cf [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a6cf) (shlR32Effect 0x10a6cf 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a6cf 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a6cf 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10a6d2 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a6d2) (orR64R64Effect 0x10a6d2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a6d2 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a6d2 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10a6d5 [0x0F, 0xB6, 0x4A, 0x09] (LoadPre 0x10a6d5 (fun s => AddrMode.addr (.base 2 (.d8 0x9)) s (0x10a6d5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6d5 4 1 (.base 2 (.d8 0x9)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6d5 4 1 (.base 2 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x10a6d5 1 (.base 2 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10a6d9 [0xC1, 0xE1, 0x18] (fun s => s.RIP = 0x10a6d9) (shlR32Effect 0x10a6d9 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a6d9 3 1 24).toInstrSpec (shl_r32_imm8_effect_step 0x10a6d9 0xe1 0x18 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10a6dc [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10a6dc) (orR64R64Effect 0x10a6dc 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a6dc 1 0).toInstrSpec (or_r64_r64_effect_step 0x10a6dc 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10a6df [0x0F, 0xB6, 0x42, 0x0A] (LoadPre 0x10a6df (fun s => AddrMode.addr (.base 2 (.d8 0xa)) s (0x10a6df + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6df 4 0 (.base 2 (.d8 0xa)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6df 4 0 (.base 2 (.d8 0xa))).toInstrSpec (movzx_r32_m8_effect_step 0x10a6df 0 (.base 2 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10a6e3 [0x48, 0xC1, 0xE0, 0x28] (fun s => s.RIP = 0x10a6e3) (shlR64Effect 0x10a6e3 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a6e3 4 0 40).toInstrSpec (shl_r64_imm8_effect_step 0x10a6e3 0x48 0xe0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10a6e7 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10a6e7) (orR64R64Effect 0x10a6e7 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10a6e7 0 1).toInstrSpec (or_r64_r64_effect_step 0x10a6e7 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10a6ea [0x44, 0x0F, 0xB6, 0x42, 0x0B] (LoadPre 0x10a6ea (fun s => AddrMode.addr (.base 2 (.d8 0xb)) s (0x10a6ea + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a6ea 5 8 (.base 2 (.d8 0xb)))
      [.gpr 2] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x10a6ea 5 8 (.base 2 (.d8 0xb))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a6ea 0x44 (by decide) 0 (.base 2 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6af) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6b2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6b5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 59), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6b9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6bd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 59), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6c0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 67), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6c4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 69), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6c8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 71), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6cb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 71), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6cf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 71), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6d2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 71), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6d5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 79), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6d9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 81), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6dc) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 77), (1, 83), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6df) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 83), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6e3) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 83), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6e7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 83), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6ea) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 83), (2, 2), (4, 4), (7, 7), (8, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a6ef) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a6a8_1 code

theorem block_l10a6a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a6a8 :=
  Rest.liftedBlock (rest_l10a6a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a6a8 x hx)

theorem rest_l10aa99 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10aa99 bytes_l10aa99) (entryMap (live .l10aa99))
      4 0x10aa99 bytes_l10aa99 b_l10aa99 := by
  have f0 : InstrSpec 0x10aa99 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10aa99) (movR64R64Effect 0x10aa99 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10aa99 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10aa99 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10aa9c [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10aa9c) (movR32Imm32Effect 0x10aa9c 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10aa9c 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x10aa9c 0xbe (by decide) 0x8) pre_rip
  have f2 : InstrSpec 0x10aaa1 [0x31, 0xFF] (fun s => s.RIP = 0x10aaa1) (xorR32R32Effect 0x10aaa1 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10aaa1 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x10aaa1 0xff (by decide)) pre_rip
  have f3 : InstrSpec 0x10aaa3 [0x48, 0xC7, 0xC1, 0xF0, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10aaa3) (movR64Imm32Effect 0x10aaa3 1 0x2011f0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x10aaa3 1 0x2011f0).toInstrSpec (mov_r64_imm32_effect_step 0x10aaa3 0x48 0xc1 (by decide) (by decide) (by decide) 0x2011f0) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(6, 6), (7, 7)]) (p' := 0x10aa9c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(7, 7)]) (p' := 0x10aaa1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := []) (p' := 0x10aaa3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := []) (p' := 0x10aaaa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l10aa99 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10aa99 :=
  Rest.liftedBlock (rest_l10aa99 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10aa99 x hx)

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

theorem_by block_l10a690_eval :
    program.runBlock (dialect code) ⟨.l10a690, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10aa99_eval :
    program.runBlock (dialect code) ⟨.l10aa99, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
