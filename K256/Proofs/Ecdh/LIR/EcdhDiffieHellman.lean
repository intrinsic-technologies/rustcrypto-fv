import K256.Proofs.Generate.LIR.CallPre
import K256.Proofs.Ecdh.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l101660_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x101660 bytes_l101660) [(0, 80), (1, 82), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x1016b1 bytes_l101660_1 b_l101660_1 := by
  have f20 : InstrSpec 0x1016b1 [0x48, 0x8D, 0x74, 0x24, 0x58] (fun s => s.RIP = 0x1016b1) (leaR64Effect 0x1016b1 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1016b1 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x1016b1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1016b6 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x1016b6) (movR64R64Effect 0x1016b6 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1016b6 7 15).toInstrSpec (mov_r64_r64_effect_step 0x1016b6 0x4c 0xff (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1016b9 [0xE8, 0xA2, 0x87, 0x00, 0x00] (PushPre 0x1016b9 5) (callEffect (fun _ => 0x109e60) 0x1016be)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1016b9 0x109e60 0x1016be).toInstrSpec (call_rel32_effect_step 0x1016b9 0x87a2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 80), (1, 82), (2, 2), (3, 72), (4, 68), (5, 5), (6, 88), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016b6) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 80), (1, 82), (2, 2), (3, 72), (4, 68), (5, 5), (6, 88), (7, 90), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016b9) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 80), (1, 82), (2, 2), (3, 72), (4, 92), (5, 5), (6, 88), (7, 90), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e60) f22 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 94) (by decide) (by decide) rfl rfl

theorem rest_l101660 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101660 bytes_l101660) (entryMap (live .l101660))
      23 0x101660 bytes_l101660 b_l101660 := by
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
  have f6 : InstrSpec 0x10166a [0x48, 0x81, 0xEC, 0x00, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x10166a) (subR64Imm32Effect 0x10166a 4 0x1000)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10166a 4 0x1000).toInstrSpec (sub_r64_imm32_effect_step 0x10166a 0x48 0xec 0x1000 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101671 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101671 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101671 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101671 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101671 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101671 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101679 [0x48, 0x81, 0xEC, 0xD8, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x101679) (subR64Imm32Effect 0x101679 4 0x7d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x101679 4 0x7d8).toInstrSpec (sub_r64_imm32_effect_step 0x101679 0x48 0xec 0x7d8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101680 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x101680) (movR64R64Effect 0x101680 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101680 14 2).toInstrSpec (mov_r64_r64_effect_step 0x101680 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101683 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x101683) (movR64R64Effect 0x101683 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101683 3 7).toInstrSpec (mov_r64_r64_effect_step 0x101683 0x48 0xfb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101686 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x101686 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101686 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101686 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101686 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101686 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10168a [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x10168a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10168a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10168a 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10168a 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10168a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10168f [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x10168f (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10168f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10168f 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10168f 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10168f 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101693 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x101693 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101693 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101693 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101693 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x101693 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101698 [0x48, 0x8B, 0x06] (LoadPre 0x101698 (fun s => AddrMode.addr (.base 6 .none) s (0x101698 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101698 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101698 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101698 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10169b [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x10169b (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10169b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10169b 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10169b 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10169b 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10169f [0x48, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x10169f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10169f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10169f 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10169f 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10169f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1016a4 [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x1016a4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1016a4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016a4 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1016a4 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1016a4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1016a9 [0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1016a9) (leaR64Effect 0x1016a9 15 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1016a9 15 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x1016a9 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101661) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101663) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101665) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101667) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101669) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10166a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101671) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101679) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 3), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101680) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(2, 2), (3, 3), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101683) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101686) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10168a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10168f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101693) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101698) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10169b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 80), (1, 82), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10169f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 80), (1, 82), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016a4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 80), (1, 82), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016a9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 80), (1, 82), (2, 2), (3, 72), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016b1) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101660_1 code

theorem block_l101660 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101660 :=
  Rest.liftedBlock (rest_l101660 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101660 x hx)

theorem rest_l1016be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1016be bytes_l1016be) (entryMap (live .l1016be))
      11 0x1016be bytes_l1016be b_l1016be := by
  have f0 : InstrSpec 0x1016be [0x48, 0xC7, 0x84, 0x24, 0xF0, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1016be 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f0)) s (0x1016be + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016be (.sib 4 none 0 (.d32 0x8f0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1016be (.sib 4 none 0 (.d32 0x8f0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1016be 0x48 (by decide) (.sib 4 none 0 (.d32 0x8f0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1016ca [0x48, 0xC7, 0x84, 0x24, 0xE8, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1016ca 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8e8)) s (0x1016ca + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016ca (.sib 4 none 0 (.d32 0x8e8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1016ca (.sib 4 none 0 (.d32 0x8e8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1016ca 0x48 (by decide) (.sib 4 none 0 (.d32 0x8e8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1016d6 [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1016d6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8e0)) s (0x1016d6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016d6 (.sib 4 none 0 (.d32 0x8e0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1016d6 (.sib 4 none 0 (.d32 0x8e0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1016d6 0x48 (by decide) (.sib 4 none 0 (.d32 0x8e0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1016e2 [0x48, 0xC7, 0x84, 0x24, 0xD8, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1016e2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8d8)) s (0x1016e2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016e2 (.sib 4 none 0 (.d32 0x8d8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1016e2 (.sib 4 none 0 (.d32 0x8d8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1016e2 0x48 (by decide) (.sib 4 none 0 (.d32 0x8d8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1016ee [0x8B, 0xAC, 0x24, 0x78, 0x01, 0x00, 0x00] (LoadPre 0x1016ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1016ee + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1016ee 5 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x1016ee 5 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_r32_m32_low_effect_step 0x1016ee 5 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1016f5 [0x4C, 0x8D, 0xA4, 0x24, 0x98, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x1016f5) (leaR64Effect 0x1016f5 12 (.sib 4 none 0 (.d32 0xc98)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x1016f5 12 (.sib 4 none 0 (.d32 0xc98))).toInstrSpec (lea_r64_effect_step 0x1016f5 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xc98)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1016fd [0x48, 0x8D, 0xB4, 0x24, 0xD8, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x1016fd) (leaR64Effect 0x1016fd 6 (.sib 4 none 0 (.d32 0x8d8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1016fd 6 (.sib 4 none 0 (.d32 0x8d8))).toInstrSpec (lea_r64_effect_step 0x1016fd 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x8d8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101705 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x101705) (movR64R64Effect 0x101705 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101705 7 12).toInstrSpec (mov_r64_r64_effect_step 0x101705 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101708 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x101708) (movR64R64Effect 0x101708 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101708 2 15).toInstrSpec (mov_r64_r64_effect_step 0x101708 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10170b [0x89, 0xE9] (fun s => s.RIP = 0x10170b) (movR32R32Effect 0x10170b 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10170b 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x10170b 0xe9 (by decide)) pre_rip
  have f10 : InstrSpec 0x10170d [0xE8, 0x0E, 0x8B, 0x00, 0x00] (PushPre 0x10170d 5) (callEffect (fun _ => 0x10a220) 0x101712)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10170d 0x10a220 0x101712).toInstrSpec (call_rel32_effect_step 0x10170d 0x8b0e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016ca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016d6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016ee) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016f5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 57), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016fd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 57), (6, 61), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101705) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101708) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 65), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10170b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (2, 65), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10170d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (2, 65), (3, 3), (4, 69), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a220) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l1016be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1016be :=
  Rest.liftedBlock (rest_l1016be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1016be x hx)

theorem rest_l101712 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101712 bytes_l101712) (entryMap (live .l101712))
      7 0x101712 bytes_l101712 b_l101712 := by
  have f0 : InstrSpec 0x101712 [0x48, 0xC7, 0x84, 0x24, 0x70, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101712 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1070)) s (0x101712 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101712 (.sib 4 none 0 (.d32 0x1070)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101712 (.sib 4 none 0 (.d32 0x1070)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101712 0x48 (by decide) (.sib 4 none 0 (.d32 0x1070)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10171e [0x48, 0xC7, 0x84, 0x24, 0x68, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10171e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1068)) s (0x10171e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10171e (.sib 4 none 0 (.d32 0x1068)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10171e (.sib 4 none 0 (.d32 0x1068)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10171e 0x48 (by decide) (.sib 4 none 0 (.d32 0x1068)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10172a [0x48, 0xC7, 0x84, 0x24, 0x60, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10172a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1060)) s (0x10172a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10172a (.sib 4 none 0 (.d32 0x1060)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10172a (.sib 4 none 0 (.d32 0x1060)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10172a 0x48 (by decide) (.sib 4 none 0 (.d32 0x1060)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101736 [0x48, 0xC7, 0x84, 0x24, 0x58, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101736 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1058)) s (0x101736 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101736 (.sib 4 none 0 (.d32 0x1058)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101736 (.sib 4 none 0 (.d32 0x1058)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101736 0x48 (by decide) (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101742 [0x48, 0x8D, 0xB4, 0x24, 0x58, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x101742) (leaR64Effect 0x101742 6 (.sib 4 none 0 (.d32 0x1058)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101742 6 (.sib 4 none 0 (.d32 0x1058))).toInstrSpec (lea_r64_effect_step 0x101742 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10174a [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10174a) (movR64R64Effect 0x10174a 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10174a 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10174a 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10174d [0xE8, 0x2E, 0x8B, 0x00, 0x00] (PushPre 0x10174d 5) (callEffect (fun _ => 0x10a280) 0x101752)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10174d 0x10a280 0x101752).toInstrSpec (call_rel32_effect_step 0x10174d 0x8b2e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10171e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10172a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101736) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101742) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10174a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10174d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l101712 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101712 :=
  Rest.liftedBlock (rest_l101712 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101712 x hx)

theorem rest_l101752 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101752 bytes_l101752) (entryMap (live .l101752))
      4 0x101752 bytes_l101752 b_l101752 := by
  have f0 : InstrSpec 0x101752 [0xF6, 0xD0] (fun s => s.RIP = 0x101752) (notR8Effect 0x101752 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x101752 2 0).toInstrSpec (not_r8_effect_step 0x101752 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101754 [0x24, 0x01] (fun s => s.RIP = 0x101754) (andAlImm8Effect 0x101754 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x101754 0x1).toInstrSpec (and_al_imm8_effect_step 0x101754 0x1) pre_rip
  have f2 : InstrSpec 0x101756 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x101756) (movzxR32R8Effect 0x101756 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x101756 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x101756 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101759 [0xE8, 0xF2, 0x65, 0x02, 0x00] (PushPre 0x101759 5) (callEffect (fun _ => 0x127d50) 0x10175e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101759 0x127d50 0x10175e).toInstrSpec (call_rel32_effect_step 0x101759 0x265f2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101754) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101756) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101759) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101752 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101752 :=
  Rest.liftedBlock (rest_l101752 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101752 x hx)

theorem rest_l10175e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10175e bytes_l10175e) (entryMap (live .l10175e))
      11 0x10175e bytes_l10175e b_l10175e := by
  have f0 : InstrSpec 0x10175e [0x48, 0x8B, 0x8C, 0x24, 0x98, 0x0C, 0x00, 0x00] (LoadPre 0x10175e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc98)) s (0x10175e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10175e 1 (.sib 4 none 0 (.d32 0xc98)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10175e 1 (.sib 4 none 0 (.d32 0xc98))).toInstrSpec (mov_r64_m64_effect_step 0x10175e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101766 [0x48, 0x8B, 0x94, 0x24, 0xA0, 0x0C, 0x00, 0x00] (LoadPre 0x101766 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca0)) s (0x101766 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101766 2 (.sib 4 none 0 (.d32 0xca0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101766 2 (.sib 4 none 0 (.d32 0xca0))).toInstrSpec (mov_r64_m64_effect_step 0x101766 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xca0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10176e [0x48, 0x89, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x10176e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10176e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10176e 1 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10176e 1 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x10176e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101776 [0x48, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x101776 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x101776 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101776 2 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101776 2 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x101776 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10177e [0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x0C, 0x00, 0x00] (LoadPre 0x10177e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca8)) s (0x10177e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10177e 1 (.sib 4 none 0 (.d32 0xca8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10177e 1 (.sib 4 none 0 (.d32 0xca8))).toInstrSpec (mov_r64_m64_effect_step 0x10177e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xca8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101786 [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x101786 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x101786 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101786 1 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101786 1 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x101786 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10178e [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x0C, 0x00, 0x00] (LoadPre 0x10178e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb0)) s (0x10178e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10178e 1 (.sib 4 none 0 (.d32 0xcb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10178e 1 (.sib 4 none 0 (.d32 0xcb0))).toInstrSpec (mov_r64_m64_effect_step 0x10178e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xcb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101796 [0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x101796 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x101796 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101796 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101796 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x101796 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10179e [0x40, 0x20, 0xE8] (fun s => s.RIP = 0x10179e) (andR8R8Effect 0x10179e 3 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR8R8Effect_footprint 0x10179e 3 0 5).toInstrSpec (and_r8_r8_rex_effect_step 0x10179e 0x40 0xe8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1017a1 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1017a1) (movzxR32R8Effect 0x1017a1 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1017a1 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1017a1 0xf8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1017a4 [0xE8, 0xA7, 0x65, 0x02, 0x00] (PushPre 0x1017a4 5) (callEffect (fun _ => 0x127d50) 0x1017a9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1017a4 0x127d50 0x1017a9).toInstrSpec (call_rel32_effect_step 0x1017a4 0x265a7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101766) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10176e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101776) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10177e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101786) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10178e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101796) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10179e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017a1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017a4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 69), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l10175e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10175e :=
  Rest.liftedBlock (rest_l10175e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10175e x hx)

theorem rest_l1017a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1017a9 bytes_l1017a9) (entryMap (live .l1017a9))
      2 0x1017a9 bytes_l1017a9 b_l1017a9 := by
  have f0 : InstrSpec 0x1017a9 [0x3C, 0x01] (fun s => s.RIP = 0x1017a9) (cmpAlImm8Effect 0x1017a9 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1017a9 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x1017a9 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1017ab 5 0x4ad) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1017a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1017a9 :=
  Rest.liftedBlock (rest_l1017a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1017a9 x hx)

theorem rest_l1017b1_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x1017b1 bytes_l1017b1) [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x10181e bytes_l1017b1_1 b_l1017b1_1 := by
  have f20 : InstrSpec 0x10181e [0xE8, 0x0D, 0xF7, 0x01, 0x00] (PushPre 0x10181e 5) (callEffect (fun _ => 0x120f30) 0x101823)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10181e 0x120f30 0x101823).toInstrSpec (call_rel32_effect_step 0x10181e 0x1f70d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 84), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f30) f20 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 86) (by decide) (by decide) rfl rfl

theorem rest_l1017b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1017b1 bytes_l1017b1) (entryMap (live .l1017b1))
      21 0x1017b1 bytes_l1017b1 b_l1017b1 := by
  have f0 : InstrSpec 0x1017b1 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1017b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1017b1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017b1 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017b1 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1017b1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1017b9 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1017b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1017b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017b9 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017b9 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1017b9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1017be [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x1017be (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1017be + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017be 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017be 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x1017be 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1017c6 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1017c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1017c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017c6 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017c6 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1017c6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1017cb [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x1017cb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1017cb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017cb 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017cb 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x1017cb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1017d3 [0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x1017d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1017d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017d3 1 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1017d3 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x1017d3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1017db [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x1017db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1017db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017db 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017db 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1017db 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1017e0 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x1017e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1017e0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017e0 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017e0 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1017e0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1017e5 [0x41, 0x0F, 0xB6, 0x46, 0x20] (LoadPre 0x1017e5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1017e5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1017e5 5 0 (.base 14 (.d8 0x20)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1017e5 5 0 (.base 14 (.d8 0x20))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1017e5 0x41 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1017ea [0x88, 0x44, 0x24, 0x50] (StorePre 0x1017ea 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1017ea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1017ea 4 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1017ea 4 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m8_r8_effect_step 0x1017ea 0 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1017ee [0x49, 0x8B, 0x46, 0x18] (LoadPre 0x1017ee (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1017ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1017ee 0 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017ee 0 (.base 14 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1017ee 0x49 (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1017f2 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x1017f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1017f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017f2 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017f2 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1017f2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1017f7 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x1017f7 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1017f7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1017f7 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017f7 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1017f7 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1017fb [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x1017fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1017fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017fb 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017fb 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1017fb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101800 [0x49, 0x8B, 0x06] (LoadPre 0x101800 (fun s => AddrMode.addr (.base 14 .none) s (0x101800 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101800 0 (.base 14 .none))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101800 0 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101800 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101803 [0x49, 0x8B, 0x4E, 0x08] (LoadPre 0x101803 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x101803 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101803 1 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101803 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101803 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101807 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x101807 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101807 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101807 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101807 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x101807 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10180c [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x10180c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10180c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10180c 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10180c 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10180c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101811 [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101811) (leaR64Effect 0x101811 7 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101811 7 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101811 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101819 [0x48, 0x8D, 0x74, 0x24, 0x30] (fun s => s.RIP = 0x101819) (leaR64Effect 0x101819 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101819 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x101819 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017be) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017cb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017d3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017db) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017e0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017e5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017ea) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017ee) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017fb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101800) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101803) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101807) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10180c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101811) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101819) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10181e) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1017b1_1 code

theorem block_l1017b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1017b1 :=
  Rest.liftedBlock (rest_l1017b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1017b1 x hx)

theorem rest_l101823 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101823 bytes_l101823) (entryMap (live .l101823))
      2 0x101823 bytes_l101823 b_l101823 := by
  have f0 : InstrSpec 0x101823 [0x80, 0xBC, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x01] (LoadPre 0x101823 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x101823 + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x101823 8 (.sib 4 none 0 (.d32 0x1b0)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x101823 8 (.sib 4 none 0 (.d32 0x1b0)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x101823 (.sib 4 none 0 (.d32 0x1b0)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10182b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10182b 5 0x42d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101823 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101823 :=
  Rest.liftedBlock (rest_l101823 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101823 x hx)

theorem rest_l101831 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101831 bytes_l101831) (entryMap (live .l101831))
      9 0x101831 bytes_l101831 b_l101831 := by
  have f0 : InstrSpec 0x101831 [0x48, 0x8D, 0x84, 0x24, 0x58, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x101831) (leaR64Effect 0x101831 0 (.sib 4 none 0 (.d32 0x1058)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x101831 0 (.sib 4 none 0 (.d32 0x1058))).toInstrSpec (lea_r64_effect_step 0x101831 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101839 [0x48, 0x8D, 0xB4, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101839) (leaR64Effect 0x101839 6 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101839 6 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101839 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101841 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101841) (movR32Imm32Effect 0x101841 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101841 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x101841 0xb9 (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x101846 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x101846) (movR64R64Effect 0x101846 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101846 7 0).toInstrSpec (mov_r64_r64_effect_step 0x101846 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101849 [0xF3, 0x48, 0xA5] (RepPre 0x101849 (RepMovsqPre 0x101849)) (repMovsqEffect 0x101849)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101849).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101849 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x10184c [0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10184c) (leaR64Effect 0x10184c 15 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10184c 15 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x10184c 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101854 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101854) (movR64R64Effect 0x101854 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101854 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101854 0x4c 0xff (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101857 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x101857) (movR64R64Effect 0x101857 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101857 6 0).toInstrSpec (mov_r64_r64_effect_step 0x101857 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10185a [0xE8, 0xB1, 0xE1, 0x00, 0x00] (PushPre 0x10185a 5) (callEffect (fun _ => 0x10fa10) 0x10185f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10185a 0x10fa10 0x10185f).toInstrSpec (call_rel32_effect_step 0x10185a 0xe1b1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101839) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101841) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101846) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101849) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10184c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101854) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101857) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10185a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa10) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l101831 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101831 :=
  Rest.liftedBlock (rest_l101831 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101831 x hx)

theorem rest_l10185f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10185f bytes_l10185f) (entryMap (live .l10185f))
      14 0x10185f bytes_l10185f b_l10185f := by
  have f0 : InstrSpec 0x10185f [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10185f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10185f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10185f 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10185f 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10185f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101864 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x101864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101864 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101864 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101864 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101864 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101869 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x101869 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x101869 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101869 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101869 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x101869 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101871 [0x48, 0x89, 0x8C, 0x24, 0xD8, 0x01, 0x00, 0x00] (StorePre 0x101871 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x101871 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101871 1 (.sib 4 none 0 (.d32 0x1d8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101871 1 (.sib 4 none 0 (.d32 0x1d8))).toInstrSpec (mov_m64_r64_effect_step 0x101871 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101879 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x101879 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101879 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101879 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101879 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x101879 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10187e [0x48, 0x89, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00] (StorePre 0x10187e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x10187e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10187e 0 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10187e 0 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_m64_r64_effect_step 0x10187e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101886 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x101886 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101886 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101886 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101886 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x101886 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10188b [0x48, 0x89, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x10188b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x10188b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10188b 0 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10188b 0 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (mov_m64_r64_effect_step 0x10188b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101893 [0x4C, 0x8D, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101893) (leaR64Effect 0x101893 14 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x101893 14 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x101893 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10189b [0x4C, 0x8D, 0x2D, 0x7E, 0x8F, 0x02, 0x00] (fun s => s.RIP = 0x10189b) (leaR64Effect 0x10189b 13 (.rip 0x28f7e))
      [] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10189b 13 (.rip 0x28f7e)).toInstrSpec (lea_r64_effect_step 0x10189b 0x4c (by decide) 5 (.rip 0x28f7e) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1018a2 [0xBA, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1018a2) (movR32Imm32Effect 0x1018a2 5 2 0x98)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1018a2 5 2 0x98).toInstrSpec (mov_r32_imm32_effect_step 0x1018a2 0xba (by decide) 0x98) pre_rip
  have f11 : InstrSpec 0x1018a7 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1018a7) (movR64R64Effect 0x1018a7 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1018a7 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1018a7 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1018aa [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1018aa) (movR64R64Effect 0x1018aa 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1018aa 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1018aa 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1018ad [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x1018ad 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x1018b0) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x1018b0)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x1018ad 13 0x1018b0).toInstrSpec (call_r64_rex_effect_step 0x1018ad 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101864) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101869) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101871) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101879) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10187e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101886) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10188b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101893) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10189b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018a2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 55), (2, 69), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018a7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 55), (2, 69), (3, 3), (4, 4), (5, 5), (7, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018aa) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 55), (2, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018ad) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 62), (1, 55), (2, 69), (3, 3), (4, 75), (5, 5), (6, 73), (7, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f13 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l10185f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10185f :=
  Rest.liftedBlock (rest_l10185f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10185f x hx)

theorem rest_l1018b0_3 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 159) code lifted (codeRange 0x1018b0 bytes_l1018b0) [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x101a05 bytes_l1018b0_3 b_l1018b0_3 := by
  have f60 : InstrSpec 0x101a05 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101a05) (movR64Imm32Effect 0x101a05 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101a05 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101a05 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f61 : InstrSpec 0x101a0c [0xF3, 0x48, 0xA5] (RepPre 0x101a0c (RepMovsqPre 0x101a0c)) (repMovsqEffect 0x101a0c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101a0c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101a0c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f62 : InstrSpec 0x101a0f [0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x101a0f) (leaR64Effect 0x101a0f 7 (.sib 4 none 0 (.d32 0xfe0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101a0f 7 (.sib 4 none 0 (.d32 0xfe0))).toInstrSpec (lea_r64_effect_step 0x101a0f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xfe0)) (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x101a17 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101a17) (movR32Imm32Effect 0x101a17 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101a17 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101a17 0xb9 (by decide) 0xf) pre_rip
  have f64 : InstrSpec 0x101a1c [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101a1c) (movR64Imm32Effect 0x101a1c 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101a1c 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101a1c 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f65 : InstrSpec 0x101a23 [0xF3, 0x48, 0xA5] (RepPre 0x101a23 (RepMovsqPre 0x101a23)) (repMovsqEffect 0x101a23)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101a23).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101a23 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f66 : InstrSpec 0x101a26 [0x4C, 0x8D, 0xA4, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101a26) (leaR64Effect 0x101a26 12 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x101a26 12 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101a26 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x101a2e [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x101a2e) (movR32Imm32Effect 0x101a2e 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101a2e 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x101a2e 0xba (by decide) 0x3c0) pre_rip
  have f68 : InstrSpec 0x101a33 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x101a33) (movR64R64Effect 0x101a33 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101a33 7 12).toInstrSpec (mov_r64_r64_effect_step 0x101a33 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x101a36 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x101a36) (movR64R64Effect 0x101a36 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101a36 6 0).toInstrSpec (mov_r64_r64_effect_step 0x101a36 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x101a39 [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x101a39 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a3c) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a3c)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x101a39 13 0x101a3c).toInstrSpec (call_r64_rex_effect_step 0x101a39 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f60 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (6, 159), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a0c) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a0f) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f62 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a17) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 53), (1, 164), (3, 3), (4, 4), (5, 5), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a1c) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f64 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 53), (1, 164), (3, 3), (4, 4), (5, 5), (6, 166), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a23) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.exec (n := 168) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a26) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f66 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a2e) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f67 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a33) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f68 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a36) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f69 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (6, 175), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a39) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f70 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 177), (5, 5), (6, 175), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f70 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 179) (by decide) (by decide) rfl rfl

theorem rest_l1018b0_2 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 124) code lifted (codeRange 0x1018b0 bytes_l1018b0) [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]
      31 0x101992 bytes_l1018b0_2 b_l1018b0_2 := by
  have f40 : InstrSpec 0x101992 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101992) (movR64Imm32Effect 0x101992 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101992 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101992 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f41 : InstrSpec 0x101999 [0xF3, 0x48, 0xA5] (RepPre 0x101999 (RepMovsqPre 0x101999)) (repMovsqEffect 0x101999)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101999).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101999 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f42 : InstrSpec 0x10199c [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x0D, 0x00, 0x00] (fun s => s.RIP = 0x10199c) (leaR64Effect 0x10199c 7 (.sib 4 none 0 (.d32 0xd88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10199c 7 (.sib 4 none 0 (.d32 0xd88))).toInstrSpec (lea_r64_effect_step 0x10199c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd88)) (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1019a4 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1019a4) (movR32Imm32Effect 0x1019a4 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1019a4 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1019a4 0xb9 (by decide) 0xf) pre_rip
  have f44 : InstrSpec 0x1019a9 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1019a9) (movR64Imm32Effect 0x1019a9 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1019a9 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1019a9 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f45 : InstrSpec 0x1019b0 [0xF3, 0x48, 0xA5] (RepPre 0x1019b0 (RepMovsqPre 0x1019b0)) (repMovsqEffect 0x1019b0)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1019b0).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1019b0 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f46 : InstrSpec 0x1019b3 [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x1019b3) (leaR64Effect 0x1019b3 7 (.sib 4 none 0 (.d32 0xe00)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1019b3 7 (.sib 4 none 0 (.d32 0xe00))).toInstrSpec (lea_r64_effect_step 0x1019b3 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe00)) (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x1019bb [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1019bb) (movR32Imm32Effect 0x1019bb 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1019bb 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1019bb 0xb9 (by decide) 0xf) pre_rip
  have f48 : InstrSpec 0x1019c0 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1019c0) (movR64Imm32Effect 0x1019c0 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1019c0 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1019c0 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f49 : InstrSpec 0x1019c7 [0xF3, 0x48, 0xA5] (RepPre 0x1019c7 (RepMovsqPre 0x1019c7)) (repMovsqEffect 0x1019c7)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1019c7).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1019c7 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f50 : InstrSpec 0x1019ca [0x48, 0x8D, 0xBC, 0x24, 0x78, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x1019ca) (leaR64Effect 0x1019ca 7 (.sib 4 none 0 (.d32 0xe78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1019ca 7 (.sib 4 none 0 (.d32 0xe78))).toInstrSpec (lea_r64_effect_step 0x1019ca 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe78)) (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x1019d2 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1019d2) (movR32Imm32Effect 0x1019d2 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1019d2 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1019d2 0xb9 (by decide) 0xf) pre_rip
  have f52 : InstrSpec 0x1019d7 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1019d7) (movR64Imm32Effect 0x1019d7 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1019d7 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1019d7 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f53 : InstrSpec 0x1019de [0xF3, 0x48, 0xA5] (RepPre 0x1019de (RepMovsqPre 0x1019de)) (repMovsqEffect 0x1019de)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1019de).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1019de 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f54 : InstrSpec 0x1019e1 [0x48, 0x8D, 0xBC, 0x24, 0xF0, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x1019e1) (leaR64Effect 0x1019e1 7 (.sib 4 none 0 (.d32 0xef0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1019e1 7 (.sib 4 none 0 (.d32 0xef0))).toInstrSpec (lea_r64_effect_step 0x1019e1 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xef0)) (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x1019e9 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1019e9) (movR32Imm32Effect 0x1019e9 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1019e9 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1019e9 0xb9 (by decide) 0xf) pre_rip
  have f56 : InstrSpec 0x1019ee [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1019ee) (movR64Imm32Effect 0x1019ee 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1019ee 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1019ee 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f57 : InstrSpec 0x1019f5 [0xF3, 0x48, 0xA5] (RepPre 0x1019f5 (RepMovsqPre 0x1019f5)) (repMovsqEffect 0x1019f5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1019f5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1019f5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f58 : InstrSpec 0x1019f8 [0x48, 0x8D, 0xBC, 0x24, 0x68, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x1019f8) (leaR64Effect 0x1019f8 7 (.sib 4 none 0 (.d32 0xf68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1019f8 7 (.sib 4 none 0 (.d32 0xf68))).toInstrSpec (lea_r64_effect_step 0x1019f8 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xf68)) (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x101a00 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101a00) (movR32Imm32Effect 0x101a00 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101a00 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101a00 0xb9 (by decide) 0xf) pre_rip
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (6, 124), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101999) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10199c) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019a4) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 53), (1, 129), (3, 3), (4, 4), (5, 5), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019a9) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f44 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 53), (1, 129), (3, 3), (4, 4), (5, 5), (6, 131), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019b0) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019b3) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f46 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019bb) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 53), (1, 136), (3, 3), (4, 4), (5, 5), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019c0) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f48 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 53), (1, 136), (3, 3), (4, 4), (5, 5), (6, 138), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019c7) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019ca) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f50 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019d2) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 53), (1, 143), (3, 3), (4, 4), (5, 5), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019d7) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 53), (1, 143), (3, 3), (4, 4), (5, 5), (6, 145), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019de) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019e1) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019e9) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 53), (1, 150), (3, 3), (4, 4), (5, 5), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019ee) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f56 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 53), (1, 150), (3, 3), (4, 4), (5, 5), (6, 152), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019f5) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.exec (n := 154) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019f8) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f58 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a00) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a05) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1018b0_3 hstride code

theorem rest_l1018b0_1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x1018b0 bytes_l1018b0) [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (6, 87), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      51 0x101923 bytes_l1018b0_1 b_l1018b0_1 := by
  have f20 : InstrSpec 0x101923 [0xF3, 0x48, 0xA5] (RepPre 0x101923 (RepMovsqPre 0x101923)) (repMovsqEffect 0x101923)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101923).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101923 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f21 : InstrSpec 0x101926 [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x101926) (leaR64Effect 0x101926 7 (.sib 4 none 0 (.d32 0xb30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101926 7 (.sib 4 none 0 (.d32 0xb30))).toInstrSpec (lea_r64_effect_step 0x101926 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb30)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10192e [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10192e) (movR32Imm32Effect 0x10192e 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10192e 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10192e 0xb9 (by decide) 0xf) pre_rip
  have f23 : InstrSpec 0x101933 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101933) (movR64Imm32Effect 0x101933 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101933 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101933 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f24 : InstrSpec 0x10193a [0xF3, 0x48, 0xA5] (RepPre 0x10193a (RepMovsqPre 0x10193a)) (repMovsqEffect 0x10193a)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10193a).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10193a 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f25 : InstrSpec 0x10193d [0x48, 0x8D, 0xBC, 0x24, 0xA8, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x10193d) (leaR64Effect 0x10193d 7 (.sib 4 none 0 (.d32 0xba8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10193d 7 (.sib 4 none 0 (.d32 0xba8))).toInstrSpec (lea_r64_effect_step 0x10193d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xba8)) (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x101945 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101945) (movR32Imm32Effect 0x101945 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101945 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101945 0xb9 (by decide) 0xf) pre_rip
  have f27 : InstrSpec 0x10194a [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x10194a) (movR64Imm32Effect 0x10194a 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10194a 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x10194a 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f28 : InstrSpec 0x101951 [0xF3, 0x48, 0xA5] (RepPre 0x101951 (RepMovsqPre 0x101951)) (repMovsqEffect 0x101951)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101951).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101951 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f29 : InstrSpec 0x101954 [0x48, 0x8D, 0xBC, 0x24, 0x20, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x101954) (leaR64Effect 0x101954 7 (.sib 4 none 0 (.d32 0xc20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101954 7 (.sib 4 none 0 (.d32 0xc20))).toInstrSpec (lea_r64_effect_step 0x101954 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc20)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10195c [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10195c) (movR32Imm32Effect 0x10195c 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10195c 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10195c 0xb9 (by decide) 0xf) pre_rip
  have f31 : InstrSpec 0x101961 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101961) (movR64Imm32Effect 0x101961 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101961 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101961 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f32 : InstrSpec 0x101968 [0xF3, 0x48, 0xA5] (RepPre 0x101968 (RepMovsqPre 0x101968)) (repMovsqEffect 0x101968)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101968).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101968 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f33 : InstrSpec 0x10196b [0x4C, 0x8D, 0xBC, 0x24, 0x98, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x10196b) (leaR64Effect 0x10196b 15 (.sib 4 none 0 (.d32 0xc98)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10196b 15 (.sib 4 none 0 (.d32 0xc98))).toInstrSpec (lea_r64_effect_step 0x10196b 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xc98)) (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x101973 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101973) (movR32Imm32Effect 0x101973 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101973 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101973 0xb9 (by decide) 0xf) pre_rip
  have f35 : InstrSpec 0x101978 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101978) (movR64R64Effect 0x101978 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101978 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101978 0x4c 0xff (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10197b [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x10197b) (movR64Imm32Effect 0x10197b 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10197b 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x10197b 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f37 : InstrSpec 0x101982 [0xF3, 0x48, 0xA5] (RepPre 0x101982 (RepMovsqPre 0x101982)) (repMovsqEffect 0x101982)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101982).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101982 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f38 : InstrSpec 0x101985 [0x48, 0x8D, 0xBC, 0x24, 0x10, 0x0D, 0x00, 0x00] (fun s => s.RIP = 0x101985) (leaR64Effect 0x101985 7 (.sib 4 none 0 (.d32 0xd10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101985 7 (.sib 4 none 0 (.d32 0xd10))).toInstrSpec (lea_r64_effect_step 0x101985 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd10)) (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10198d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10198d) (movR32Imm32Effect 0x10198d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10198d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10198d 0xb9 (by decide) 0xf) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101926) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10192e) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 53), (1, 92), (3, 3), (4, 4), (5, 5), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101933) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 53), (1, 92), (3, 3), (4, 4), (5, 5), (6, 94), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10193a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10193d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101945) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 53), (1, 99), (3, 3), (4, 4), (5, 5), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10194a) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 53), (1, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101951) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101954) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10195c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 53), (1, 106), (3, 3), (4, 4), (5, 5), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101961) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 53), (1, 106), (3, 3), (4, 4), (5, 5), (6, 108), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101968) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10196b) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101973) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101978) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (7, 115), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10197b) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (6, 117), (7, 115), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101982) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101985) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10198d) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101992) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1018b0_2 hstride code

theorem rest_l1018b0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1018b0 bytes_l1018b0) (entryMap (live .l1018b0))
      71 0x1018b0 bytes_l1018b0 b_l1018b0 := by
  have f0 : InstrSpec 0x1018b0 [0x48, 0x8D, 0x84, 0x24, 0xD8, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x1018b0) (leaR64Effect 0x1018b0 0 (.sib 4 none 0 (.d32 0x8d8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1018b0 0 (.sib 4 none 0 (.d32 0x8d8))).toInstrSpec (lea_r64_effect_step 0x1018b0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x8d8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1018b8 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1018b8) (movR32Imm32Effect 0x1018b8 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1018b8 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1018b8 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x1018bd [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x1018bd) (movR64R64Effect 0x1018bd 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1018bd 7 0).toInstrSpec (mov_r64_r64_effect_step 0x1018bd 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1018c0 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1018c0) (movR64Imm32Effect 0x1018c0 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1018c0 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1018c0 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f4 : InstrSpec 0x1018c7 [0xF3, 0x48, 0xA5] (RepPre 0x1018c7 (RepMovsqPre 0x1018c7)) (repMovsqEffect 0x1018c7)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1018c7).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1018c7 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x1018ca [0x48, 0x8D, 0xBC, 0x24, 0x50, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1018ca) (leaR64Effect 0x1018ca 7 (.sib 4 none 0 (.d32 0x950)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1018ca 7 (.sib 4 none 0 (.d32 0x950))).toInstrSpec (lea_r64_effect_step 0x1018ca 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x950)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1018d2 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1018d2) (movR32Imm32Effect 0x1018d2 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1018d2 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1018d2 0xb9 (by decide) 0xf) pre_rip
  have f7 : InstrSpec 0x1018d7 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1018d7) (movR64Imm32Effect 0x1018d7 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1018d7 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1018d7 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f8 : InstrSpec 0x1018de [0xF3, 0x48, 0xA5] (RepPre 0x1018de (RepMovsqPre 0x1018de)) (repMovsqEffect 0x1018de)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1018de).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1018de 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x1018e1 [0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1018e1) (leaR64Effect 0x1018e1 7 (.sib 4 none 0 (.d32 0x9c8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1018e1 7 (.sib 4 none 0 (.d32 0x9c8))).toInstrSpec (lea_r64_effect_step 0x1018e1 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x9c8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1018e9 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1018e9) (movR32Imm32Effect 0x1018e9 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1018e9 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1018e9 0xb9 (by decide) 0xf) pre_rip
  have f11 : InstrSpec 0x1018ee [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1018ee) (movR64Imm32Effect 0x1018ee 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1018ee 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1018ee 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f12 : InstrSpec 0x1018f5 [0xF3, 0x48, 0xA5] (RepPre 0x1018f5 (RepMovsqPre 0x1018f5)) (repMovsqEffect 0x1018f5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1018f5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1018f5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x1018f8 [0x48, 0x8D, 0xBC, 0x24, 0x40, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x1018f8) (leaR64Effect 0x1018f8 7 (.sib 4 none 0 (.d32 0xa40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1018f8 7 (.sib 4 none 0 (.d32 0xa40))).toInstrSpec (lea_r64_effect_step 0x1018f8 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa40)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101900 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101900) (movR32Imm32Effect 0x101900 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101900 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101900 0xb9 (by decide) 0xf) pre_rip
  have f15 : InstrSpec 0x101905 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101905) (movR64Imm32Effect 0x101905 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101905 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101905 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f16 : InstrSpec 0x10190c [0xF3, 0x48, 0xA5] (RepPre 0x10190c (RepMovsqPre 0x10190c)) (repMovsqEffect 0x10190c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10190c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10190c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x10190f [0x48, 0x8D, 0xBC, 0x24, 0xB8, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x10190f) (leaR64Effect 0x10190f 7 (.sib 4 none 0 (.d32 0xab8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10190f 7 (.sib 4 none 0 (.d32 0xab8))).toInstrSpec (lea_r64_effect_step 0x10190f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xab8)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101917 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101917) (movR32Imm32Effect 0x101917 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101917 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101917 0xb9 (by decide) 0xf) pre_rip
  have f19 : InstrSpec 0x10191c [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x10191c) (movR64Imm32Effect 0x10191c 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10191c 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x10191c 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018bd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018c0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018ca) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018d2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018d7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018de) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018e1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018e9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 71), (3, 3), (4, 4), (5, 5), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018ee) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018f5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018f8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101900) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 53), (1, 78), (3, 3), (4, 4), (5, 5), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101905) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 53), (1, 78), (3, 3), (4, 4), (5, 5), (6, 80), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10190c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10190f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101917) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10191c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (6, 87), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101923) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1018b0_1 hstride code

theorem block_l1018b0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1018b0 :=
  Rest.liftedBlock (rest_l1018b0 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1018b0 x hx)

theorem rest_l101a3c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101a3c bytes_l101a3c) (entryMap (live .l101a3c))
      4 0x101a3c bytes_l101a3c b_l101a3c := by
  have f0 : InstrSpec 0x101a3c [0x48, 0x8D, 0xBC, 0x24, 0x18, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x101a3c) (leaR64Effect 0x101a3c 7 (.sib 4 none 0 (.d32 0x518)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101a3c 7 (.sib 4 none 0 (.d32 0x518))).toInstrSpec (lea_r64_effect_step 0x101a3c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x518)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101a44 [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x101a44) (movR32Imm32Effect 0x101a44 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101a44 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x101a44 0xba (by decide) 0x3c0) pre_rip
  have f2 : InstrSpec 0x101a49 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x101a49) (movR64R64Effect 0x101a49 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101a49 6 15).toInstrSpec (mov_r64_r64_effect_step 0x101a49 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101a4c [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x101a4c 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a4f) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a4f)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x101a4c 13 0x101a4f).toInstrSpec (call_r64_rex_effect_step 0x101a4c 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a44) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a49) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a4c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101a3c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101a3c :=
  Rest.liftedBlock (rest_l101a3c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101a3c x hx)

theorem rest_l101a4f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101a4f bytes_l101a4f) (entryMap (live .l101a4f))
      5 0x101a4f bytes_l101a4f b_l101a4f := by
  have f0 : InstrSpec 0x101a4f [0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x101a4f) (leaR64Effect 0x101a4f 15 (.sib 4 none 0 (.d32 0x1058)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x101a4f 15 (.sib 4 none 0 (.d32 0x1058))).toInstrSpec (lea_r64_effect_step 0x101a4f 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101a57 [0xBA, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x101a57) (movR32Imm32Effect 0x101a57 5 2 0x780)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101a57 5 2 0x780).toInstrSpec (mov_r32_imm32_effect_step 0x101a57 0xba (by decide) 0x780) pre_rip
  have f2 : InstrSpec 0x101a5c [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101a5c) (movR64R64Effect 0x101a5c 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101a5c 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101a5c 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101a5f [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x101a5f) (movR64R64Effect 0x101a5f 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101a5f 6 12).toInstrSpec (mov_r64_r64_effect_step 0x101a5f 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101a62 [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x101a62 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a65) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a65)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x101a62 13 0x101a65).toInstrSpec (call_r64_rex_effect_step 0x101a62 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a57) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a5c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a5f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a62) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l101a4f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101a4f :=
  Rest.liftedBlock (rest_l101a4f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101a4f x hx)

theorem rest_l101a65 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101a65 bytes_l101a65) (entryMap (live .l101a65))
      18 0x101a65 bytes_l101a65 b_l101a65 := by
  have f0 : InstrSpec 0x101a65 [0x66, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a65 10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x101a65 + BitVec.ofNat 64 10)) 2) (movM16Imm16Effect 0x101a65 (.sib 4 none 0 (.d32 0xb8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x101a65 (.sib 4 none 0 (.d32 0xb8)) 0x0).toInstrSpec (mov_m16_imm16_effect_step 0x101a65 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101a6f [0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a6f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x101a6f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a6f (.sib 4 none 0 (.d32 0xb0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a6f (.sib 4 none 0 (.d32 0xb0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a6f 0x48 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101a7b [0x48, 0xC7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a7b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x101a7b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a7b (.sib 4 none 0 (.d32 0xa8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a7b (.sib 4 none 0 (.d32 0xa8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a7b 0x48 (by decide) (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101a87 [0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a87 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x101a87 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a87 (.sib 4 none 0 (.d32 0xa0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a87 (.sib 4 none 0 (.d32 0xa0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a87 0x48 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101a93 [0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a93 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x101a93 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a93 (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a93 (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a93 0x48 (by decide) (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x101a9f [0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a9f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x101a9f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a9f (.sib 4 none 0 (.d32 0x90)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a9f (.sib 4 none 0 (.d32 0x90)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a9f 0x48 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101aab [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101aab 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101aab + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101aab (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101aab (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101aab 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101ab7 [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101ab7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101ab7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101ab7 (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101ab7 (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101ab7 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101ac3 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101ac3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101ac3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101ac3 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101ac3 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101ac3 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101acc [0x48, 0xC7, 0x04, 0x24, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101acc 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101acc + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101acc (.sib 4 none 0 .none) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101acc (.sib 4 none 0 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x101acc 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101ad4 [0x4C, 0x8D, 0xA4, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101ad4) (leaR64Effect 0x101ad4 12 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x101ad4 12 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101ad4 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101adc [0x4C, 0x8D, 0x4C, 0x24, 0x78] (fun s => s.RIP = 0x101adc) (leaR64Effect 0x101adc 9 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x101adc 9 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x101adc 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101ae1 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ae1) (movR32Imm32Effect 0x101ae1 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101ae1 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x101ae1 0xba (by decide) 0x1) pre_rip
  have f13 : InstrSpec 0x101ae6 [0x41, 0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ae6) (movR32Imm32Effect 0x101ae6 6 8 0x1)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x101ae6 6 8 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x101ae6 0x41 0xb8 (by decide) (by decide) 0x1) pre_rip
  have f14 : InstrSpec 0x101aec [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x101aec) (movR64R64Effect 0x101aec 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101aec 7 12).toInstrSpec (mov_r64_r64_effect_step 0x101aec 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101aef [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x101aef) (movR64R64Effect 0x101aef 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101aef 6 14).toInstrSpec (mov_r64_r64_effect_step 0x101aef 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101af2 [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x101af2) (movR64R64Effect 0x101af2 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x101af2 1 15).toInstrSpec (mov_r64_r64_effect_step 0x101af2 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101af5 [0xE8, 0x86, 0xAD, 0x01, 0x00] (PushPre 0x101af5 5) (callEffect (fun _ => 0x11c880) 0x101afa)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101af5 0x11c880 0x101afa).toInstrSpec (call_rel32_effect_step 0x101af5 0x1ad86 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a6f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a7b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a87) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a93) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a9f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aab) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ac3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101acc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ad4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101adc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 5), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 5), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aec) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 5), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aef) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 75), (2, 67), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 75), (2, 67), (3, 3), (4, 77), (5, 5), (6, 73), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c880) f17 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l101a65 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101a65 :=
  Rest.liftedBlock (rest_l101a65 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101a65 x hx)

theorem rest_l101afa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101afa bytes_l101afa) (entryMap (live .l101afa))
      4 0x101afa bytes_l101afa b_l101afa := by
  have f0 : InstrSpec 0x101afa [0x4C, 0x8D, 0xB4, 0x24, 0x58, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x101afa) (leaR64Effect 0x101afa 14 (.sib 4 none 0 (.d32 0x1058)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x101afa 14 (.sib 4 none 0 (.d32 0x1058))).toInstrSpec (lea_r64_effect_step 0x101afa 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101b02 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101b02) (movR64R64Effect 0x101b02 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101b02 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101b02 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101b05 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x101b05) (movR64R64Effect 0x101b05 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101b05 6 12).toInstrSpec (mov_r64_r64_effect_step 0x101b05 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101b08 [0xE8, 0x43, 0xE3, 0x00, 0x00] (PushPre 0x101b08 5) (callEffect (fun _ => 0x10fe50) 0x101b0d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101b08 0x10fe50 0x101b0d).toInstrSpec (call_rel32_effect_step 0x101b08 0xe343 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b08) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101afa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101afa :=
  Rest.liftedBlock (rest_l101afa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101afa x hx)

theorem rest_l101b0d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101b0d bytes_l101b0d) (entryMap (live .l101b0d))
      3 0x101b0d bytes_l101b0d b_l101b0d := by
  have f0 : InstrSpec 0x101b0d [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101b0d) (leaR64Effect 0x101b0d 7 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101b0d 7 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101b0d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101b15 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x101b15) (movR64R64Effect 0x101b15 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101b15 6 14).toInstrSpec (mov_r64_r64_effect_step 0x101b15 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101b18 [0xE8, 0x33, 0xE8, 0x01, 0x00] (PushPre 0x101b18 5) (callEffect (fun _ => 0x120350) 0x101b1d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101b18 0x120350 0x101b1d).toInstrSpec (call_rel32_effect_step 0x101b18 0x1e833 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b15) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b18) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120350) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l101b0d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101b0d :=
  Rest.liftedBlock (rest_l101b0d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101b0d x hx)

theorem rest_l101b1d_2 [Bindings] (code : CodeMap) :
    Rest (n := 97) code lifted (codeRange 0x101b1d bytes_l101b1d) [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x101c4c bytes_l101b1d_2 b_l101b1d_2 := by
  have f40 : InstrSpec 0x101c4c [0x48, 0x81, 0xC4, 0xD8, 0x17, 0x00, 0x00] (fun s => s.RIP = 0x101c4c) (addR64Imm32Effect 0x101c4c 4 0x17d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101c4c 4 0x17d8).toInstrSpec (add_r64_imm32_effect_step 0x101c4c 0x48 0xc4 0x17d8 (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x101c53 [0x5B] (PopPre 0x101c53) (popR64Effect 0x101c53 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c53 1 3).toInstrSpec (pop_r64_effect_step 0x101c53 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f42 : InstrSpec 0x101c54 [0x41, 0x5C] (PopPre 0x101c54) (popR64Effect 0x101c54 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c54 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101c54 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f43 : InstrSpec 0x101c56 [0x41, 0x5D] (PopPre 0x101c56) (popR64Effect 0x101c56 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c56 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101c56 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f44 : InstrSpec 0x101c58 [0x41, 0x5E] (PopPre 0x101c58) (popR64Effect 0x101c58 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c58 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101c58 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f45 : InstrSpec 0x101c5a [0x41, 0x5F] (PopPre 0x101c5a) (popR64Effect 0x101c5a 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c5a 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101c5a 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f46 : InstrSpec 0x101c5c [0x5D] (PopPre 0x101c5c) (popR64Effect 0x101c5c 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c5c 1 5).toInstrSpec (pop_r64_effect_step 0x101c5c 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f47 : InstrSpec 0x101c5d [0xC3] (RetPre 0x101c5d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101c5d).toInstrSpec (ret_effect_step 0x101c5d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f40 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 97), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c53) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f41 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 100), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c54) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f42 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f42 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c56) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f43 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 107) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 106), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c58) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f44 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 109) f44 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 110) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 109), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c5a) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f45 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 112) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 113) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 112), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c5c) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f46 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 115) f46 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 116) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 115), (5, 114), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c5d) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f47 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 118) f47 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 119) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 118), (5, 114), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) f47 (by decide) rfl rfl rfl (by decide)

theorem rest_l101b1d_1 [Bindings] (code : CodeMap) :
    Rest (n := 77) code lifted (codeRange 0x101b1d bytes_l101b1d) [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]
      28 0x101bac bytes_l101b1d_1 b_l101b1d_1 := by
  have f20 : InstrSpec 0x101bac [0xC6, 0x84, 0x24, 0x64, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x164)) s (0x101bac + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bac (.sib 4 none 0 (.d32 0x164)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bac (.sib 4 none 0 (.d32 0x164)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bac (.sib 4 none 0 (.d32 0x164)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x101bb4 [0xC6, 0x84, 0x24, 0x65, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bb4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x165)) s (0x101bb4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bb4 (.sib 4 none 0 (.d32 0x165)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bb4 (.sib 4 none 0 (.d32 0x165)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bb4 (.sib 4 none 0 (.d32 0x165)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x101bbc [0xC6, 0x84, 0x24, 0x66, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bbc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x166)) s (0x101bbc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bbc (.sib 4 none 0 (.d32 0x166)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bbc (.sib 4 none 0 (.d32 0x166)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bbc (.sib 4 none 0 (.d32 0x166)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101bc4 [0xC6, 0x84, 0x24, 0x67, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bc4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x167)) s (0x101bc4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bc4 (.sib 4 none 0 (.d32 0x167)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bc4 (.sib 4 none 0 (.d32 0x167)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bc4 (.sib 4 none 0 (.d32 0x167)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x101bcc [0xC6, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bcc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x101bcc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bcc (.sib 4 none 0 (.d32 0x168)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bcc (.sib 4 none 0 (.d32 0x168)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bcc (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x101bd4 [0xC6, 0x84, 0x24, 0x69, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bd4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x169)) s (0x101bd4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bd4 (.sib 4 none 0 (.d32 0x169)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bd4 (.sib 4 none 0 (.d32 0x169)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bd4 (.sib 4 none 0 (.d32 0x169)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x101bdc [0xC6, 0x84, 0x24, 0x6A, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bdc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16a)) s (0x101bdc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bdc (.sib 4 none 0 (.d32 0x16a)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bdc (.sib 4 none 0 (.d32 0x16a)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bdc (.sib 4 none 0 (.d32 0x16a)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x101be4 [0xC6, 0x84, 0x24, 0x6B, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101be4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16b)) s (0x101be4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101be4 (.sib 4 none 0 (.d32 0x16b)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101be4 (.sib 4 none 0 (.d32 0x16b)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101be4 (.sib 4 none 0 (.d32 0x16b)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x101bec [0xC6, 0x84, 0x24, 0x6C, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16c)) s (0x101bec + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bec (.sib 4 none 0 (.d32 0x16c)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bec (.sib 4 none 0 (.d32 0x16c)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bec (.sib 4 none 0 (.d32 0x16c)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x101bf4 [0xC6, 0x84, 0x24, 0x6D, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bf4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16d)) s (0x101bf4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bf4 (.sib 4 none 0 (.d32 0x16d)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bf4 (.sib 4 none 0 (.d32 0x16d)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bf4 (.sib 4 none 0 (.d32 0x16d)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x101bfc [0xC6, 0x84, 0x24, 0x6E, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bfc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16e)) s (0x101bfc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bfc (.sib 4 none 0 (.d32 0x16e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bfc (.sib 4 none 0 (.d32 0x16e)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bfc (.sib 4 none 0 (.d32 0x16e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x101c04 [0xC6, 0x84, 0x24, 0x6F, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16f)) s (0x101c04 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c04 (.sib 4 none 0 (.d32 0x16f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c04 (.sib 4 none 0 (.d32 0x16f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c04 (.sib 4 none 0 (.d32 0x16f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x101c0c [0xC6, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c0c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x101c0c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c0c (.sib 4 none 0 (.d32 0x170)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c0c (.sib 4 none 0 (.d32 0x170)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c0c (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x101c14 [0xC6, 0x84, 0x24, 0x71, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c14 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x171)) s (0x101c14 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c14 (.sib 4 none 0 (.d32 0x171)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c14 (.sib 4 none 0 (.d32 0x171)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c14 (.sib 4 none 0 (.d32 0x171)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x101c1c [0xC6, 0x84, 0x24, 0x72, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c1c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x172)) s (0x101c1c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c1c (.sib 4 none 0 (.d32 0x172)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c1c (.sib 4 none 0 (.d32 0x172)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c1c (.sib 4 none 0 (.d32 0x172)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x101c24 [0xC6, 0x84, 0x24, 0x73, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c24 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x173)) s (0x101c24 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c24 (.sib 4 none 0 (.d32 0x173)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c24 (.sib 4 none 0 (.d32 0x173)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c24 (.sib 4 none 0 (.d32 0x173)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x101c2c [0xC6, 0x84, 0x24, 0x74, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c2c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x174)) s (0x101c2c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c2c (.sib 4 none 0 (.d32 0x174)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c2c (.sib 4 none 0 (.d32 0x174)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c2c (.sib 4 none 0 (.d32 0x174)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x101c34 [0xC6, 0x84, 0x24, 0x75, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c34 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x175)) s (0x101c34 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c34 (.sib 4 none 0 (.d32 0x175)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c34 (.sib 4 none 0 (.d32 0x175)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c34 (.sib 4 none 0 (.d32 0x175)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x101c3c [0xC6, 0x84, 0x24, 0x76, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c3c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x176)) s (0x101c3c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c3c (.sib 4 none 0 (.d32 0x176)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c3c (.sib 4 none 0 (.d32 0x176)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c3c (.sib 4 none 0 (.d32 0x176)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x101c44 [0xC6, 0x84, 0x24, 0x77, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c44 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x177)) s (0x101c44 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c44 (.sib 4 none 0 (.d32 0x177)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c44 (.sib 4 none 0 (.d32 0x177)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c44 (.sib 4 none 0 (.d32 0x177)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bb4) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bbc) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bc4) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bcc) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bd4) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bdc) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101be4) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bec) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bf4) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bfc) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c04) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c0c) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c14) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c1c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c24) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c2c) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c34) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c3c) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c44) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c4c) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l101b1d_2 code

theorem rest_l101b1d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101b1d bytes_l101b1d) (entryMap (live .l101b1d))
      48 0x101b1d bytes_l101b1d b_l101b1d := by
  have f0 : InstrSpec 0x101b1d [0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (LoadPre 0x101b1d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x101b1d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b1d 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101b1d 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_r64_m64_effect_step 0x101b1d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101b25 [0x48, 0x89, 0x43, 0x18] (StorePre 0x101b25 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x101b25 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b25 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101b25 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101b25 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101b29 [0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00] (LoadPre 0x101b29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x101b29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b29 0 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101b29 0 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_r64_m64_effect_step 0x101b29 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101b31 [0x48, 0x89, 0x43, 0x10] (StorePre 0x101b31 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x101b31 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b31 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101b31 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101b31 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101b35 [0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x101b35 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x101b35 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b35 0 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101b35 0 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_r64_m64_effect_step 0x101b35 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101b3d [0x48, 0x8B, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00] (LoadPre 0x101b3d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x101b3d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b3d 1 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101b3d 1 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_r64_m64_effect_step 0x101b3d 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101b45 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x101b45 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x101b45 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b45 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101b45 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101b45 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101b49 [0x48, 0x89, 0x03] (StorePre 0x101b49 3 (fun s => AddrMode.addr (.base 3 .none) s (0x101b49 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101b49 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101b49 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101b49 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101b4c [0xC6, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b4c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x101b4c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b4c (.sib 4 none 0 (.d32 0x158)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b4c (.sib 4 none 0 (.d32 0x158)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b4c (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101b54 [0xC6, 0x84, 0x24, 0x59, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x159)) s (0x101b54 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b54 (.sib 4 none 0 (.d32 0x159)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b54 (.sib 4 none 0 (.d32 0x159)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b54 (.sib 4 none 0 (.d32 0x159)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101b5c [0xC6, 0x84, 0x24, 0x5A, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15a)) s (0x101b5c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b5c (.sib 4 none 0 (.d32 0x15a)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b5c (.sib 4 none 0 (.d32 0x15a)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b5c (.sib 4 none 0 (.d32 0x15a)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x101b64 [0xC6, 0x84, 0x24, 0x5B, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b64 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15b)) s (0x101b64 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b64 (.sib 4 none 0 (.d32 0x15b)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b64 (.sib 4 none 0 (.d32 0x15b)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b64 (.sib 4 none 0 (.d32 0x15b)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101b6c [0xC6, 0x84, 0x24, 0x5C, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b6c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15c)) s (0x101b6c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b6c (.sib 4 none 0 (.d32 0x15c)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b6c (.sib 4 none 0 (.d32 0x15c)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b6c (.sib 4 none 0 (.d32 0x15c)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101b74 [0xC6, 0x84, 0x24, 0x5D, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b74 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15d)) s (0x101b74 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b74 (.sib 4 none 0 (.d32 0x15d)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b74 (.sib 4 none 0 (.d32 0x15d)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b74 (.sib 4 none 0 (.d32 0x15d)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101b7c [0xC6, 0x84, 0x24, 0x5E, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b7c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15e)) s (0x101b7c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b7c (.sib 4 none 0 (.d32 0x15e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b7c (.sib 4 none 0 (.d32 0x15e)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b7c (.sib 4 none 0 (.d32 0x15e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101b84 [0xC6, 0x84, 0x24, 0x5F, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b84 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15f)) s (0x101b84 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b84 (.sib 4 none 0 (.d32 0x15f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b84 (.sib 4 none 0 (.d32 0x15f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b84 (.sib 4 none 0 (.d32 0x15f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101b8c [0xC6, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b8c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x101b8c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b8c (.sib 4 none 0 (.d32 0x160)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b8c (.sib 4 none 0 (.d32 0x160)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b8c (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101b94 [0xC6, 0x84, 0x24, 0x61, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x161)) s (0x101b94 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b94 (.sib 4 none 0 (.d32 0x161)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b94 (.sib 4 none 0 (.d32 0x161)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b94 (.sib 4 none 0 (.d32 0x161)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101b9c [0xC6, 0x84, 0x24, 0x62, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x162)) s (0x101b9c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b9c (.sib 4 none 0 (.d32 0x162)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b9c (.sib 4 none 0 (.d32 0x162)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b9c (.sib 4 none 0 (.d32 0x162)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x101ba4 [0xC6, 0x84, 0x24, 0x63, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101ba4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x163)) s (0x101ba4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101ba4 (.sib 4 none 0 (.d32 0x163)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101ba4 (.sib 4 none 0 (.d32 0x163)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101ba4 (.sib 4 none 0 (.d32 0x163)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b25) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b29) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b31) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b35) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b3d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b45) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b49) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b4c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b54) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b5c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b64) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b6c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b74) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b7c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b84) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b8c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b94) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b9c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ba4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bac) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l101b1d_1 code

theorem block_l101b1d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101b1d :=
  Rest.liftedBlock (rest_l101b1d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101b1d x hx)

theorem rest_l101c5e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c5e bytes_l101c5e) (entryMap (live .l101c5e))
      1 0x101c5e bytes_l101c5e b_l101c5e := by
  have f0 : InstrSpec 0x101c5e [0xE8, 0xCD, 0xED, 0xFF, 0xFF] (PushPre 0x101c5e 5) (callEffect (fun _ => 0x100a30) 0x101c63)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101c5e 0x100a30 0x101c63).toInstrSpec (call_rel32_effect_step 0x101c5e 0xffffedcd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l101c5e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c5e :=
  Rest.liftedBlock (rest_l101c5e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c5e x hx)

theorem rest_l101c63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c63 bytes_l101c63) (entryMap (live .l101c63))
      20 0x101c63 bytes_l101c63 b_l101c63 := by
  have f0 : InstrSpec 0x101c63 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101c63) (fun _ => nopEffect 0x101c63 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101c63 10).toInstrSpec (nop_m_effect_step 0x101c63 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101c6d [0x0F, 0x1F, 0x00] (fun s => s.RIP = 0x101c6d) (fun _ => nopEffect 0x101c6d 3)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101c6d 3).toInstrSpec (nop_m_effect_step 0x101c6d [] (by decide) (by decide) (.base 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101c70 [0x41, 0x56] (PushPre 0x101c70 2) (pushR64Effect 0x101c70 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c70 2 14).toInstrSpec (push_r64_rex_effect_step 0x101c70 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101c72 [0x53] (PushPre 0x101c72 1) (pushR64Effect 0x101c72 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c72 1 3).toInstrSpec (push_r64_effect_step 0x101c72 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101c73 [0x48, 0x81, 0xEC, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101c73) (subR64Imm32Effect 0x101c73 4 0x1e8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x101c73 4 0x1e8).toInstrSpec (sub_r64_imm32_effect_step 0x101c73 0x48 0xec 0x1e8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101c7a [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x101c7a) (movR64R64Effect 0x101c7a 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101c7a 14 2).toInstrSpec (mov_r64_r64_effect_step 0x101c7a 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101c7d [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x101c7d) (movR64R64Effect 0x101c7d 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101c7d 3 7).toInstrSpec (mov_r64_r64_effect_step 0x101c7d 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101c80 [0x0F, 0xB6, 0x46, 0x20] (LoadPre 0x101c80 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x101c80 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x101c80 4 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101c80 4 0 (.base 6 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x101c80 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101c84 [0x88, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x101c84 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x101c84 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x101c84 7 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101c84 7 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m8_r8_effect_step 0x101c84 0 (by decide) (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101c8b [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x101c8b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101c8b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c8b 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101c8b 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101c8b 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101c8f [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x101c8f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x101c8f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101c8f 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c8f 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x101c8f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x101c97 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x101c97 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101c97 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c97 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101c97 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101c97 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101c9b [0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x101c9b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x101c9b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101c9b 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c9b 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x101c9b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101ca3 [0x48, 0x8B, 0x06] (LoadPre 0x101ca3 (fun s => AddrMode.addr (.base 6 .none) s (0x101ca3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101ca3 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101ca3 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101ca3 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101ca6 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x101ca6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101ca6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101ca6 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101ca6 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101ca6 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101caa [0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x101caa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x101caa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101caa 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101caa 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x101caa 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101cb2 [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x101cb2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x101cb2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101cb2 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101cb2 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x101cb2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101cba [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x101cba) (movR64R64Effect 0x101cba 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101cba 7 4).toInstrSpec (mov_r64_r64_effect_step 0x101cba 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101cbd [0x48, 0x8D, 0xB4, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101cbd) (leaR64Effect 0x101cbd 6 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101cbd 6 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x101cbd 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101cc5 [0xE8, 0x36, 0xE2, 0x00, 0x00] (PushPre 0x101cc5 5) (callEffect (fun _ => 0x10ff00) 0x101cca)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101cc5 0x10ff00 0x101cca).toInstrSpec (call_rel32_effect_step 0x101cc5 0xe236 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c6d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c70) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c72) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c73) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c7a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c7d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c80) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c84) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c8b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c8f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c97) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c9b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101caa) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cb2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cbd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cc5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 84), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff00) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 86) (by decide) (by decide) rfl rfl

theorem block_l101c63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c63 :=
  Rest.liftedBlock (rest_l101c63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c63 x hx)

theorem rest_l101cca [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101cca bytes_l101cca) (entryMap (live .l101cca))
      2 0x101cca bytes_l101cca b_l101cca := by
  have f0 : InstrSpec 0x101cca [0x80, 0x7C, 0x24, 0x78, 0x01] (LoadPre 0x101cca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101cca + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x101cca 5 (.sib 4 none 0 (.d8 0x78)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x101cca 5 (.sib 4 none 0 (.d8 0x78)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x101cca (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ccf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x101ccf 5 0xf6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101cca [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101cca :=
  Rest.liftedBlock (rest_l101cca code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101cca x hx)

theorem rest_l101cd5 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101cd5 bytes_l101cd5) (entryMap (live .l101cd5))
      17 0x101cd5 bytes_l101cd5 b_l101cd5 := by
  have f0 : InstrSpec 0x101cd5 [0x48, 0x8D, 0xBC, 0x24, 0x70, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101cd5) (leaR64Effect 0x101cd5 7 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101cd5 7 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (lea_r64_effect_step 0x101cd5 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101cdd [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x101cdd) (movR64R64Effect 0x101cdd 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101cdd 6 4).toInstrSpec (mov_r64_r64_effect_step 0x101cdd 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101ce0 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ce0) (movR32Imm32Effect 0x101ce0 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101ce0 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101ce0 0xb9 (by decide) 0xf) pre_rip
  have f3 : InstrSpec 0x101ce5 [0xF3, 0x48, 0xA5] (RepPre 0x101ce5 (RepMovsqPre 0x101ce5)) (repMovsqEffect 0x101ce5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101ce5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101ce5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x101ce8 [0x41, 0x0F, 0xB6, 0x46, 0x20] (LoadPre 0x101ce8 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x101ce8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101ce8 5 0 (.base 14 (.d8 0x20)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101ce8 5 0 (.base 14 (.d8 0x20))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101ce8 0x41 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101ced [0x88, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x101ced 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x101ced + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x101ced 7 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ced 7 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m8_r8_effect_step 0x101ced 0 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101cf4 [0x49, 0x8B, 0x46, 0x18] (LoadPre 0x101cf4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x101cf4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101cf4 0 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101cf4 0 (.base 14 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101cf4 0x49 (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101cf8 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x101cf8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x101cf8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101cf8 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101cf8 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x101cf8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101d00 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x101d00 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x101d00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101d00 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101d00 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101d00 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x101d04 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x101d04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x101d04 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d04 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101d04 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x101d04 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101d0c [0x49, 0x8B, 0x06] (LoadPre 0x101d0c (fun s => AddrMode.addr (.base 14 .none) s (0x101d0c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101d0c 0 (.base 14 .none))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101d0c 0 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101d0c 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101d0f [0x49, 0x8B, 0x4E, 0x08] (LoadPre 0x101d0f (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x101d0f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101d0f 1 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101d0f 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101d0f 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101d13 [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x101d13 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101d13 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d13 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101d13 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x101d13 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101d1b [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x101d1b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101d1b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d1b 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101d1b 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x101d1b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101d23 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x101d23) (movR64R64Effect 0x101d23 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d23 7 4).toInstrSpec (mov_r64_r64_effect_step 0x101d23 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101d26 [0x48, 0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d26) (leaR64Effect 0x101d26 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101d26 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x101d26 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101d2e [0xE8, 0xCD, 0xE1, 0x00, 0x00] (PushPre 0x101d2e 5) (callEffect (fun _ => 0x10ff00) 0x101d33)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101d2e 0x10ff00 0x101d33).toInstrSpec (call_rel32_effect_step 0x101d2e 0xe1cd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cdd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ced) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d00) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d04) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d0c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d0f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d13) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d1b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d23) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d26) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d2e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 79), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff00) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l101cd5 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101cd5 :=
  Rest.liftedBlock (rest_l101cd5 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101cd5 x hx)

theorem rest_l101d33 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d33 bytes_l101d33) (entryMap (live .l101d33))
      2 0x101d33 bytes_l101d33 b_l101d33 := by
  have f0 : InstrSpec 0x101d33 [0x80, 0x7C, 0x24, 0x78, 0x01] (LoadPre 0x101d33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101d33 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x101d33 5 (.sib 4 none 0 (.d8 0x78)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x101d33 5 (.sib 4 none 0 (.d8 0x78)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x101d33 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d38) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x101d38 5 0x8d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101d33 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d33 :=
  Rest.liftedBlock (rest_l101d33 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d33 x hx)

theorem rest_l101d3e [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d3e bytes_l101d3e) (entryMap (live .l101d3e))
      13 0x101d3e bytes_l101d3e b_l101d3e := by
  have f0 : InstrSpec 0x101d3e [0x48, 0x8D, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d3e) (leaR64Effect 0x101d3e 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x101d3e 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x101d3e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101d46 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x101d46) (movR64R64Effect 0x101d46 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d46 6 4).toInstrSpec (mov_r64_r64_effect_step 0x101d46 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101d49 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d49) (movR32Imm32Effect 0x101d49 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101d49 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101d49 0xb9 (by decide) 0xf) pre_rip
  have f3 : InstrSpec 0x101d4e [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x101d4e) (movR64R64Effect 0x101d4e 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d4e 7 0).toInstrSpec (mov_r64_r64_effect_step 0x101d4e 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101d51 [0xF3, 0x48, 0xA5] (RepPre 0x101d51 (RepMovsqPre 0x101d51)) (repMovsqEffect 0x101d51)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101d51).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101d51 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x101d54 [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x101d54) (movR64R64Effect 0x101d54 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101d54 14 4).toInstrSpec (mov_r64_r64_effect_step 0x101d54 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101d57 [0x48, 0x8D, 0xB4, 0x24, 0x70, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101d57) (leaR64Effect 0x101d57 6 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101d57 6 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (lea_r64_effect_step 0x101d57 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101d5f [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d5f) (movR32Imm32Effect 0x101d5f 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101d5f 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101d5f 0xb9 (by decide) 0xf) pre_rip
  have f8 : InstrSpec 0x101d64 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101d64) (movR64R64Effect 0x101d64 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d64 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101d64 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101d67 [0xF3, 0x48, 0xA5] (RepPre 0x101d67 (RepMovsqPre 0x101d67)) (repMovsqEffect 0x101d67)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101d67).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101d67 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f10 : InstrSpec 0x101d6a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101d6a) (movR64R64Effect 0x101d6a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d6a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101d6a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101d6d [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x101d6d) (movR64R64Effect 0x101d6d 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d6d 6 0).toInstrSpec (mov_r64_r64_effect_step 0x101d6d 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101d70 [0xE8, 0x9B, 0x86, 0x00, 0x00] (PushPre 0x101d70 5) (callEffect (fun _ => 0x10a410) 0x101d75)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101d70 0x10a410 0x101d75).toInstrSpec (call_rel32_effect_step 0x101d70 0x869b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d46) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d49) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d4e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d51) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d54) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d57) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 64), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d5f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 66), (3, 3), (4, 4), (5, 5), (6, 64), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d64) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 66), (3, 3), (4, 4), (5, 5), (6, 64), (7, 68), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d67) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d6a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d6d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d70) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (3, 3), (4, 75), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l101d3e [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d3e :=
  Rest.liftedBlock (rest_l101d3e hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d3e x hx)

theorem rest_l101d75 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d75 bytes_l101d75) (entryMap (live .l101d75))
      8 0x101d75 bytes_l101d75 b_l101d75 := by
  have f0 : InstrSpec 0x101d75 [0x48, 0x8D, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d75) (leaR64Effect 0x101d75 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x101d75 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x101d75 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101d7d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d7d) (movR32Imm32Effect 0x101d7d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101d7d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101d7d 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x101d82 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x101d82) (movR64R64Effect 0x101d82 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d82 7 0).toInstrSpec (mov_r64_r64_effect_step 0x101d82 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101d85 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x101d85) (movR64R64Effect 0x101d85 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d85 6 14).toInstrSpec (mov_r64_r64_effect_step 0x101d85 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101d88 [0xF3, 0x48, 0xA5] (RepPre 0x101d88 (RepMovsqPre 0x101d88)) (repMovsqEffect 0x101d88)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101d88).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101d88 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x101d8b [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x101d8b) (movR64R64Effect 0x101d8b 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d8b 7 4).toInstrSpec (mov_r64_r64_effect_step 0x101d8b 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101d8e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x101d8e) (movR64R64Effect 0x101d8e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d8e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x101d8e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101d91 [0xE8, 0xDA, 0xE2, 0x00, 0x00] (PushPre 0x101d91 5) (callEffect (fun _ => 0x110070) 0x101d96)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101d91 0x110070 0x101d96).toInstrSpec (call_rel32_effect_step 0x101d91 0xe2da (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d82) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d88) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d8b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d8e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d91) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (3, 3), (4, 66), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110070) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l101d75 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d75 :=
  Rest.liftedBlock (rest_l101d75 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d75 x hx)

theorem rest_l101d96 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d96 bytes_l101d96) (entryMap (live .l101d96))
      14 0x101d96 bytes_l101d96 b_l101d96 := by
  have f0 : InstrSpec 0x101d96 [0x0F, 0xB6, 0x44, 0x24, 0x20] (LoadPre 0x101d96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101d96 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d96 5 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101d96 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x101d96 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101d9b [0x88, 0x43, 0x20] (StorePre 0x101d9b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x101d9b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101d9b 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x101d9b 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x101d9b 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101d9e [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x101d9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101d9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101d9e 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101d9e 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101d9e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101da3 [0x48, 0x89, 0x43, 0x18] (StorePre 0x101da3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x101da3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101da3 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101da3 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101da3 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101da7 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x101da7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101da7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101da7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101da7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101da7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101dac [0x48, 0x89, 0x43, 0x10] (StorePre 0x101dac 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x101dac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101dac 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101dac 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101dac 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101db0 [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x101db0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101db0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101db0 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101db0 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101db0 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101db4 [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x101db4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101db4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101db4 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101db4 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101db4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101db9 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x101db9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x101db9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101db9 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101db9 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101db9 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101dbd [0x48, 0x89, 0x03] (StorePre 0x101dbd 3 (fun s => AddrMode.addr (.base 3 .none) s (0x101dbd + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101dbd 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101dbd 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101dbd 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101dc0 [0x48, 0x81, 0xC4, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101dc0) (addR64Imm32Effect 0x101dc0 4 0x1e8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101dc0 4 0x1e8).toInstrSpec (add_r64_imm32_effect_step 0x101dc0 0x48 0xc4 0x1e8 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101dc7 [0x5B] (PopPre 0x101dc7) (popR64Effect 0x101dc7 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101dc7 1 3).toInstrSpec (pop_r64_effect_step 0x101dc7 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x101dc8 [0x41, 0x5E] (PopPre 0x101dc8) (popR64Effect 0x101dc8 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101dc8 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101dc8 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x101dca [0xC3] (RetPre 0x101dca) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101dca).toInstrSpec (ret_effect_step 0x101dca) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d9b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d9e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101da3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101da7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dbd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 3), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 70), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 70), (4, 74), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dca) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 78) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 70), (4, 77), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f13 (by decide) rfl rfl rfl (by decide)

theorem block_l101d96 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d96 :=
  Rest.liftedBlock (rest_l101d96 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d96 x hx)

theorem rest_l101dcb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dcb bytes_l101dcb) (entryMap (live .l101dcb))
      1 0x101dcb bytes_l101dcb b_l101dcb := by
  have f0 : InstrSpec 0x101dcb [0xE8, 0x60, 0xEC, 0xFF, 0xFF] (PushPre 0x101dcb 5) (callEffect (fun _ => 0x100a30) 0x101dd0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101dcb 0x100a30 0x101dd0).toInstrSpec (call_rel32_effect_step 0x101dcb 0xffffec60 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l101dcb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dcb :=
  Rest.liftedBlock (rest_l101dcb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dcb x hx)

theorem rest_l101dd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dd0 bytes_l101dd0) (entryMap (live .l101dd0))
      6 0x101dd0 bytes_l101dd0 b_l101dd0 := by
  have f0 : InstrSpec 0x101dd0 [0x41, 0x56] (PushPre 0x101dd0 2) (pushR64Effect 0x101dd0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101dd0 2 14).toInstrSpec (push_r64_rex_effect_step 0x101dd0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101dd2 [0x53] (PushPre 0x101dd2 1) (pushR64Effect 0x101dd2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101dd2 1 3).toInstrSpec (push_r64_effect_step 0x101dd2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101dd3 [0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101dd3) (subR64Imm32Effect 0x101dd3 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x101dd3 4 0xe8).toInstrSpec (sub_r64_imm32_effect_step 0x101dd3 0x48 0xec 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101dda [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x101dda) (movR64R64Effect 0x101dda 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101dda 14 7).toInstrSpec (mov_r64_r64_effect_step 0x101dda 0x49 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101ddd [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ddd) (leaR64Effect 0x101ddd 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101ddd 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x101ddd 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101de5 [0xE8, 0xA6, 0x45, 0x00, 0x00] (PushPre 0x101de5 5) (callEffect (fun _ => 0x106390) 0x101dea)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101de5 0x106390 0x101dea).toInstrSpec (call_rel32_effect_step 0x101de5 0x45a6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dda) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ddd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101de5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106390) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l101dd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dd0 :=
  Rest.liftedBlock (rest_l101dd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dd0 x hx)

theorem rest_l101dea [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dea bytes_l101dea) (entryMap (live .l101dea))
      3 0x101dea bytes_l101dea b_l101dea := by
  have f0 : InstrSpec 0x101dea [0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x101dea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101dea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101dea 3 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x101dea 3 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x101dea 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101df2 [0x48, 0x83, 0xFB, 0x01] (fun s => s.RIP = 0x101df2) (cmpR64Imm8Effect 0x101df2 3 0x1)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101df2 3 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x101df2 0x48 0xfb 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x101df6 4 0x6a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101dea [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dea :=
  Rest.liftedBlock (rest_l101dea code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dea x hx)

theorem rest_l101df8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101df8 bytes_l101df8) (entryMap (live .l101df8))
      4 0x101df8 bytes_l101df8 b_l101df8 := by
  have f0 : InstrSpec 0x101df8 [0x48, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101df8) (leaR64Effect 0x101df8 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101df8 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (lea_r64_effect_step 0x101df8 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101e00 [0x48, 0x8D, 0x7C, 0x24, 0x0F] (fun s => s.RIP = 0x101e00) (leaR64Effect 0x101e00 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101e00 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x101e00 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e05 [0x31, 0xD2] (fun s => s.RIP = 0x101e05) (xorR32R32Effect 0x101e05 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101e05 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x101e05 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x101e07 [0xE8, 0xD4, 0xF7, 0x01, 0x00] (PushPre 0x101e07 5) (callEffect (fun _ => 0x1215e0) 0x101e0c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101e07 0x1215e0 0x101e0c).toInstrSpec (call_rel32_effect_step 0x101e07 0x1f7d4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e00) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e07) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101df8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101df8 :=
  Rest.liftedBlock (rest_l101df8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101df8 x hx)

theorem rest_l101e0c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e0c bytes_l101e0c) (entryMap (live .l101e0c))
      7 0x101e0c bytes_l101e0c b_l101e0c := by
  have f0 : InstrSpec 0x101e0c [0x0F, 0xB6, 0x4C, 0x24, 0x0F] (LoadPre 0x101e0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101e0c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x101e0c 1 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101e11 [0x48, 0x83, 0xF9, 0x06] (fun s => s.RIP = 0x101e11) (cmpR64Imm8Effect 0x101e11 1 0x6)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101e11 1 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x101e11 0x48 0xf9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e15 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x101e15) (atFlags (condHolds 2) (setccR8Effect 0x101e15 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x101e15 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x101e15 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x101e18 [0xB2, 0x3D] (fun s => s.RIP = 0x101e18) (movR8Imm8Effect 0x101e18 2 2 0x3d)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR8Imm8Effect_footprint 0x101e18 2 2 0x3d).toInstrSpec (mov_r8_imm8_effect_step 0x101e18 0xb2 (by decide) 0x3d) pre_rip
  have f4 : InstrSpec 0x101e1a [0xD2, 0xEA] (fun s => s.RIP = 0x101e1a) (shrR8ClEffect 0x101e1a 2 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR8ClEffect_footprint 0x101e1a 2 2).toInstrSpec (shr_r8_cl_effect_step 0x101e1a 0xea (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101e1c [0x84, 0xD0] (fun s => s.RIP = 0x101e1c) (testR8R8Effect 0x101e1c 2 0 2)
      [.gpr 0, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x101e1c 2 0 2).toInstrSpec (test_r8_r8_effect_step 0x101e1c 0xd0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e15) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e18) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 53), (2, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x101e1e 5 0x2c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101e0c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e0c :=
  Rest.liftedBlock (rest_l101e0c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e0c x hx)

theorem rest_l101e20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e20 bytes_l101e20) (entryMap (live .l101e20))
      7 0x101e20 bytes_l101e20 b_l101e20 := by
  have f0 : InstrSpec 0x101e20 [0xC7, 0x44, 0x24, 0x50, 0x03, 0x00, 0x00, 0x00] (StorePre 0x101e20 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101e20 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x101e20 8 (.sib 4 none 0 (.d8 0x50)) 0x3)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x101e20 8 (.sib 4 none 0 (.d8 0x50)) 0x3).toInstrSpec (mov_m32_imm32_effect_step 0x101e20 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101e28 [0x48, 0x8D, 0x54, 0x24, 0x50] (fun s => s.RIP = 0x101e28) (leaR64Effect 0x101e28 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x101e28 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101e28 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e2d [0xBE, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101e2d) (movR32Imm32Effect 0x101e2d 5 6 0xb)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x101e2d 5 6 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x101e2d 0xbe (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x101e32 [0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x101e32) (movR64Imm32Effect 0x101e32 7 0x202800)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x101e32 7 0x202800).toInstrSpec (mov_r64_imm32_effect_step 0x101e32 0x48 0xc7 (by decide) (by decide) (by decide) 0x202800) pre_rip
  have f4 : InstrSpec 0x101e39 [0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00] (fun s => s.RIP = 0x101e39) (movR64Imm32Effect 0x101e39 1 0x2027e0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x101e39 1 0x2027e0).toInstrSpec (mov_r64_imm32_effect_step 0x101e39 0x48 0xc1 (by decide) (by decide) (by decide) 0x2027e0) pre_rip
  have f5 : InstrSpec 0x101e40 [0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x101e40) (movR64Imm32Effect 0x101e40 8 0x202810)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x101e40 8 0x202810).toInstrSpec (mov_r64_imm32_effect_step 0x101e40 0x49 0xc0 (by decide) (by decide) (by decide) 0x202810) pre_rip
  have f6 : InstrSpec 0x101e47 [0xE8, 0x54, 0x77, 0x02, 0x00] (PushPre 0x101e47 5) (callEffect (fun _ => 0x1295a0) 0x101e4c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101e47 0x1295a0 0x101e4c).toInstrSpec (call_rel32_effect_step 0x101e47 0x27754 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x101e28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (4, 4), (5, 5)]) (p' := 0x101e2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56)]) (p' := 0x101e32) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x101e39) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x101e40) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x101e47) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1295a0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l101e20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e20 :=
  Rest.liftedBlock (rest_l101e20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e20 x hx)

theorem rest_l101e4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e4c bytes_l101e4c) (entryMap (live .l101e4c))
      4 0x101e4c bytes_l101e4c b_l101e4c := by
  have f0 : InstrSpec 0x101e4c [0x48, 0x8B, 0x14, 0xCD, 0xB8, 0x22, 0x20, 0x00] (LoadPre 0x101e4c (fun s => AddrMode.addr (.abs (some 1) 3 0x2022b8) s (0x101e4c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101e4c 2 (.abs (some 1) 3 0x2022b8))
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101e4c 2 (.abs (some 1) 3 0x2022b8)).toInstrSpec (mov_r64_m64_effect_step 0x101e4c 0x48 (by decide) 2 (.abs (some 1) 3 0x2022b8) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101e54 [0x48, 0x8D, 0x74, 0x24, 0x0F] (fun s => s.RIP = 0x101e54) (leaR64Effect 0x101e54 6 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101e54 6 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x101e54 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e59 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101e59) (movR64R64Effect 0x101e59 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101e59 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101e59 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101e5c [0xFF, 0x15, 0x6E, 0x1F, 0x10, 0x00] (GoesTo (CallMemPre 0x101e5c (.rip 0x101f6e)) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) 0x12a820) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101e5c (.rip 0x101f6e)).toInstrSpec (call_m64_effect_step 0x101e5c (.rip 0x101f6e) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e59) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101e4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e4c :=
  Rest.liftedBlock (rest_l101e4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e4c x hx)

theorem rest_l101e62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e62 bytes_l101e62) (entryMap (live .l101e62))
      5 0x101e62 bytes_l101e62 b_l101e62 := by
  have f0 : InstrSpec 0x101e62 [0x89, 0xD8] (fun s => s.RIP = 0x101e62) (movR32R32Effect 0x101e62 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101e62 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x101e62 0xd8 (by decide)) pre_rip
  have f1 : InstrSpec 0x101e64 [0x48, 0x81, 0xC4, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101e64) (addR64Imm32Effect 0x101e64 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101e64 4 0xe8).toInstrSpec (add_r64_imm32_effect_step 0x101e64 0x48 0xc4 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e6b [0x5B] (PopPre 0x101e6b) (popR64Effect 0x101e6b 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e6b 1 3).toInstrSpec (pop_r64_effect_step 0x101e6b 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101e6c [0x41, 0x5E] (PopPre 0x101e6c) (popR64Effect 0x101e6c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e6c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101e6c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101e6e [0xC3] (RetPre 0x101e6e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101e6e).toInstrSpec (ret_effect_step 0x101e6e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e64) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l101e62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e62 :=
  Rest.liftedBlock (rest_l101e62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e62 x hx)

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

theorem_by block_l101660_eval :
    program.runBlock (dialect code) ⟨.l101660, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1016be_eval :
    program.runBlock (dialect code) ⟨.l1016be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101712_eval :
    program.runBlock (dialect code) ⟨.l101712, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101752_eval :
    program.runBlock (dialect code) ⟨.l101752, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10175e_eval :
    program.runBlock (dialect code) ⟨.l10175e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1017a9_eval :
    program.runBlock (dialect code) ⟨.l1017a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1017b1_eval :
    program.runBlock (dialect code) ⟨.l1017b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101823_eval :
    program.runBlock (dialect code) ⟨.l101823, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101831_eval :
    program.runBlock (dialect code) ⟨.l101831, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10185f_eval :
    program.runBlock (dialect code) ⟨.l10185f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1018b0_eval :
    program.runBlock (dialect code) ⟨.l1018b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101a3c_eval :
    program.runBlock (dialect code) ⟨.l101a3c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101a4f_eval :
    program.runBlock (dialect code) ⟨.l101a4f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101a65_eval :
    program.runBlock (dialect code) ⟨.l101a65, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101afa_eval :
    program.runBlock (dialect code) ⟨.l101afa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101b0d_eval :
    program.runBlock (dialect code) ⟨.l101b0d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101b1d_eval :
    program.runBlock (dialect code) ⟨.l101b1d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101c5e_eval :
    program.runBlock (dialect code) ⟨.l101c5e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101c63_eval :
    program.runBlock (dialect code) ⟨.l101c63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101cca_eval :
    program.runBlock (dialect code) ⟨.l101cca, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101cd5_eval :
    program.runBlock (dialect code) ⟨.l101cd5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d33_eval :
    program.runBlock (dialect code) ⟨.l101d33, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d3e_eval :
    program.runBlock (dialect code) ⟨.l101d3e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d75_eval :
    program.runBlock (dialect code) ⟨.l101d75, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d96_eval :
    program.runBlock (dialect code) ⟨.l101d96, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dcb_eval :
    program.runBlock (dialect code) ⟨.l101dcb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dd0_eval :
    program.runBlock (dialect code) ⟨.l101dd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dea_eval :
    program.runBlock (dialect code) ⟨.l101dea, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101df8_eval :
    program.runBlock (dialect code) ⟨.l101df8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e0c_eval :
    program.runBlock (dialect code) ⟨.l101e0c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e20_eval :
    program.runBlock (dialect code) ⟨.l101e20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e4c_eval :
    program.runBlock (dialect code) ⟨.l101e4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e62_eval :
    program.runBlock (dialect code) ⟨.l101e62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
