import K256.Proofs.Generate.LIR.CallPre
import K256.Proofs.Generate.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Generate.LIR.Generated.Values

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

theorem rest_l11c880 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c880 bytes_l11c880) (entryMap (live .l11c880))
      16 0x11c880 bytes_l11c880 b_l11c880 := by
  have f0 : InstrSpec 0x11c880 [0x55] (PushPre 0x11c880 1) (pushR64Effect 0x11c880 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c880 1 5).toInstrSpec (push_r64_effect_step 0x11c880 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x11c881 [0x41, 0x57] (PushPre 0x11c881 2) (pushR64Effect 0x11c881 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c881 2 15).toInstrSpec (push_r64_rex_effect_step 0x11c881 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x11c883 [0x41, 0x56] (PushPre 0x11c883 2) (pushR64Effect 0x11c883 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c883 2 14).toInstrSpec (push_r64_rex_effect_step 0x11c883 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x11c885 [0x41, 0x55] (PushPre 0x11c885 2) (pushR64Effect 0x11c885 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c885 2 13).toInstrSpec (push_r64_rex_effect_step 0x11c885 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11c887 [0x41, 0x54] (PushPre 0x11c887 2) (pushR64Effect 0x11c887 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c887 2 12).toInstrSpec (push_r64_rex_effect_step 0x11c887 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x11c889 [0x53] (PushPre 0x11c889 1) (pushR64Effect 0x11c889 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c889 1 3).toInstrSpec (push_r64_effect_step 0x11c889 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x11c88a [0x48, 0x81, 0xEC, 0x88, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x11c88a) (subR64Imm32Effect 0x11c88a 4 0xc88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x11c88a 4 0xc88).toInstrSpec (sub_r64_imm32_effect_step 0x11c88a 0x48 0xec 0xc88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11c891 [0x4C, 0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x11c891 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11c891 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c891 9 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c891 9 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x11c891 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11c899 [0x48, 0x89, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x11c899 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11c899 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c899 6 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c899 6 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x11c899 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x11c8a1 [0x48, 0x89, 0xBC, 0x24, 0x48, 0x02, 0x00, 0x00] (StorePre 0x11c8a1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x11c8a1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8a1 7 (.sib 4 none 0 (.d32 0x248)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c8a1 7 (.sib 4 none 0 (.d32 0x248))).toInstrSpec (mov_m64_r64_effect_step 0x11c8a1 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x248)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11c8a9 [0x48, 0x8B, 0xB4, 0x24, 0xC0, 0x0C, 0x00, 0x00] (LoadPre 0x11c8a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc0)) s (0x11c8a9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c8a9 6 (.sib 4 none 0 (.d32 0xcc0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11c8a9 6 (.sib 4 none 0 (.d32 0xcc0))).toInstrSpec (mov_r64_m64_effect_step 0x11c8a9 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xcc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11c8b1 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x11c8b1) (testR64R64Effect 0x11c8b1 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11c8b1 2 2).toInstrSpec (test_r64_r64_effect_step 0x11c8b1 0x48 0xd2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11c8b4 [0x4C, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x11c8b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11c8b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8b4 8 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c8b4 8 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x11c8b4 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x11c8bc [0x48, 0x89, 0x94, 0x24, 0xA0, 0x01, 0x00, 0x00] (StorePre 0x11c8bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x11c8bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8bc 2 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c8bc 2 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_m64_r64_effect_step 0x11c8bc 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x11c8c4 [0x48, 0x89, 0x8C, 0x24, 0xC0, 0x01, 0x00, 0x00] (StorePre 0x11c8c4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x11c8c4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8c4 1 (.sib 4 none 0 (.d32 0x1c0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c8c4 1 (.sib 4 none 0 (.d32 0x1c0))).toInstrSpec (mov_m64_r64_effect_step 0x11c8c4 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1c0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c881) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c883) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c885) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c887) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c889) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c88a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c891) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c899) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8a1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8a9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 70), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8b1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 70), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8b4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 70), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8bc) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 70), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8c4) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 70), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8cc) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 77) (jcc_rel32_effect_step 0x11c8cc 4 0xe5f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c880 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c880 :=
  Rest.liftedBlock (rest_l11c880 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c880 x hx)

theorem rest_l11c8d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c8d2 bytes_l11c8d2) (entryMap (live .l11c8d2))
      14 0x11c8d2 bytes_l11c8d2 b_l11c8d2 := by
  have f0 : InstrSpec 0x11c8d2 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x11c8d2) (movR64R64Effect 0x11c8d2 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c8d2 0 6).toInstrSpec (mov_r64_r64_effect_step 0x11c8d2 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c8d5 [0x48, 0xC1, 0xE0, 0x06] (fun s => s.RIP = 0x11c8d5) (shlR64Effect 0x11c8d5 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x11c8d5 4 0 6).toInstrSpec (shl_r64_imm8_effect_step 0x11c8d5 0x48 0xe0 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c8d9 [0x48, 0x8D, 0x04, 0x70] (fun s => s.RIP = 0x11c8d9) (leaR64Effect 0x11c8d9 0 (.sib 0 (some 6) 1 .none))
      [.gpr 0, .gpr 6] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11c8d9 0 (.sib 0 (some 6) 1 .none)).toInstrSpec (lea_r64_effect_step 0x11c8d9 0x48 (by decide) 0 (.sib 0 (some 6) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c8dd [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x11c8dd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11c8dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c8dd 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c8dd 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x11c8dd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11c8e2 [0x48, 0x69, 0xC2, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c8e2) (imulR64R64Imm32Effect 0x11c8e2 7 0 2 0x98)
      [.gpr 2] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c8e2 7 0 2 0x98).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c8e2 0x48 (by decide) 0xc2 (by decide) 0x98) pre_rip
  have f5 : InstrSpec 0x11c8e9 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x11c8e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11c8e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8e9 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c8e9 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x11c8e9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11c8f1 [0x49, 0x69, 0xC0, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c8f1) (imulR64R64Imm32Effect 0x11c8f1 7 0 8 0x98)
      [.gpr 8] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c8f1 7 0 8 0x98).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c8f1 0x49 (by decide) 0xc0 (by decide) 0x98) pre_rip
  have f7 : InstrSpec 0x11c8f8 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x11c8f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11c8f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c8f8 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c8f8 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x11c8f8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11c8fd [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x11c8fd) (xorR32R32Effect 0x11c8fd 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c8fd 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x11c8fd 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11c900 [0x4C, 0x8D, 0xA4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c900) (leaR64Effect 0x11c900 12 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x11c900 12 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11c900 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11c908 [0x4C, 0x8D, 0xBC, 0x24, 0xD0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c908) (leaR64Effect 0x11c908 15 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x11c908 15 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (lea_r64_effect_step 0x11c908 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11c910 [0x48, 0x89, 0xCD] (fun s => s.RIP = 0x11c910) (movR64R64Effect 0x11c910 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x11c910 5 1).toInstrSpec (mov_r64_r64_effect_step 0x11c910 0x48 0xcd (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11c913 [0x31, 0xF6] (fun s => s.RIP = 0x11c913) (xorR32R32Effect 0x11c913 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c913 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x11c913 0xf6 (by decide)) pre_rip
  have f13 : InstrSpec 0x11c915 [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c915) (fun _ => nopEffect 0x11c915 11)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11c915 11).toInstrSpec (nop_m_effect_step 0x11c915 [0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8d5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8d9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8dd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8e2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8f1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8f8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c8fd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (13, 13), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c900) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (12, 68), (13, 13), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c908) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c910) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c913) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (5, 72), (6, 74), (8, 8), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c915) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (5, 72), (6, 74), (8, 8), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c920) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l11c8d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c8d2 :=
  Rest.liftedBlock (rest_l11c8d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c8d2 x hx)

theorem rest_l11c920 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c920 bytes_l11c920) (entryMap (live .l11c920))
      11 0x11c920 bytes_l11c920 b_l11c920 := by
  have f0 : InstrSpec 0x11c920 [0x48, 0x89, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x11c920 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11c920 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c920 6 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c920 6 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x11c920 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11c928 [0x48, 0x89, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x11c928 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11c928 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c928 5 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c928 5 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x11c928 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11c930 [0x4C, 0x89, 0x74, 0x24, 0x08] (StorePre 0x11c930 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c930 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c930 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c930 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11c930 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11c935 [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x11c935 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11c935 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c935 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c935 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x11c935 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11c93d [0x4A, 0x8D, 0x04, 0x31] (fun s => s.RIP = 0x11c93d) (leaR64Effect 0x11c93d 0 (.sib 1 (some 14) 0 .none))
      [.gpr 1, .gpr 14] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11c93d 0 (.sib 1 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x11c93d 0x4a (by decide) 0 (.sib 1 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c941 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x11c941 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11c941 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c941 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c941 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x11c941 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11c946 [0x4A, 0x8D, 0x6C, 0x31, 0x78] (fun s => s.RIP = 0x11c946) (leaR64Effect 0x11c946 5 (.sib 1 (some 14) 0 (.d8 0x78)))
      [.gpr 1, .gpr 14] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x11c946 5 (.sib 1 (some 14) 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x11c946 0x4a (by decide) 5 (.sib 1 (some 14) 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11c94b [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c94b) (movR64R64Effect 0x11c94b 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c94b 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c94b 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11c94e [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11c94e) (movR64R64Effect 0x11c94e 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c94e 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11c94e 0x48 0xee (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11c951 [0x48, 0xC7, 0xC2, 0x00, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x11c951) (movR64Imm32Effect 0x11c951 2 0x202200)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11c951 2 0x202200).toInstrSpec (mov_r64_imm32_effect_step 0x11c951 0x48 0xc2 (by decide) (by decide) (by decide) 0x202200) pre_rip
  have f10 : InstrSpec 0x11c958 [0xE8, 0x93, 0xEF, 0xFF, 0xFF] (PushPre 0x11c958 5) (callEffect (fun _ => 0x11b8f0) 0x11c95d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c958 0x11b8f0 0x11c95d).toInstrSpec (call_rel32_effect_step 0x11c958 0xffffef93 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c928) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c930) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c935) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c93d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c941) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c946) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (1, 56), (3, 3), (4, 4), (5, 61), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c94b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 56), (3, 3), (4, 4), (5, 61), (6, 6), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c94e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (1, 56), (3, 3), (4, 4), (5, 61), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c951) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (1, 56), (2, 67), (3, 3), (4, 4), (5, 61), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c958) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 56), (2, 67), (3, 3), (4, 69), (5, 61), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f0) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l11c920 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c920 :=
  Rest.liftedBlock (rest_l11c920 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c920 x hx)

theorem rest_l11c95d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c95d bytes_l11c95d) (entryMap (live .l11c95d))
      5 0x11c95d bytes_l11c95d b_l11c95d := by
  have f0 : InstrSpec 0x11c95d [0x48, 0x8D, 0x9C, 0x24, 0x10, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x11c95d) (leaR64Effect 0x11c95d 3 (.sib 4 none 0 (.d32 0xc10)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x11c95d 3 (.sib 4 none 0 (.d32 0xc10))).toInstrSpec (lea_r64_effect_step 0x11c95d 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xc10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c965 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x11c965) (movR64R64Effect 0x11c965 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c965 7 3).toInstrSpec (mov_r64_r64_effect_step 0x11c965 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c968 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c968) (movR64R64Effect 0x11c968 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c968 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c968 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c96b [0x48, 0xC7, 0xC2, 0x20, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x11c96b) (movR64Imm32Effect 0x11c96b 2 0x202220)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11c96b 2 0x202220).toInstrSpec (mov_r64_imm32_effect_step 0x11c96b 0x48 0xc2 (by decide) (by decide) (by decide) 0x202220) pre_rip
  have f4 : InstrSpec 0x11c972 [0xE8, 0x49, 0xD0, 0xFE, 0xFF] (PushPre 0x11c972 5) (callEffect (fun _ => 0x1099c0) 0x11c977)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c972 0x1099c0 0x11c977).toInstrSpec (call_rel32_effect_step 0x11c972 0xfffed049 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c965) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c968) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c96b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c972) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c95d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c95d :=
  Rest.liftedBlock (rest_l11c95d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c95d x hx)

theorem rest_l11c977 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c977 bytes_l11c977) (entryMap (live .l11c977))
      4 0x11c977 bytes_l11c977 b_l11c977 := by
  have f0 : InstrSpec 0x11c977 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c977) (movR64R64Effect 0x11c977 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c977 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c977 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c97a [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11c97a) (movR64R64Effect 0x11c97a 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c97a 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11c97a 0x48 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c97d [0x48, 0xC7, 0xC2, 0x40, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x11c97d) (movR64Imm32Effect 0x11c97d 2 0x202240)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11c97d 2 0x202240).toInstrSpec (mov_r64_imm32_effect_step 0x11c97d 0x48 0xc2 (by decide) (by decide) (by decide) 0x202240) pre_rip
  have f3 : InstrSpec 0x11c984 [0xE8, 0x67, 0xEF, 0xFF, 0xFF] (PushPre 0x11c984 5) (callEffect (fun _ => 0x11b8f0) 0x11c989)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c984 0x11b8f0 0x11c989).toInstrSpec (call_rel32_effect_step 0x11c984 0xffffef67 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c97a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c97d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c984) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11c977 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c977 :=
  Rest.liftedBlock (rest_l11c977 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c977 x hx)

theorem rest_l11c989 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c989 bytes_l11c989) (entryMap (live .l11c989))
      5 0x11c989 bytes_l11c989 b_l11c989 := by
  have f0 : InstrSpec 0x11c989 [0x4C, 0x8D, 0xAC, 0x24, 0x28, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11c989) (leaR64Effect 0x11c989 13 (.sib 4 none 0 (.d32 0x328)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x11c989 13 (.sib 4 none 0 (.d32 0x328))).toInstrSpec (lea_r64_effect_step 0x11c989 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x328)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c991 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11c991) (movR64R64Effect 0x11c991 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c991 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11c991 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c994 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c994) (movR64R64Effect 0x11c994 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c994 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c994 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c997 [0x48, 0xC7, 0xC2, 0x60, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x11c997) (movR64Imm32Effect 0x11c997 2 0x202260)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11c997 2 0x202260).toInstrSpec (mov_r64_imm32_effect_step 0x11c997 0x48 0xc2 (by decide) (by decide) (by decide) 0x202260) pre_rip
  have f4 : InstrSpec 0x11c99e [0xE8, 0x1D, 0xD0, 0xFE, 0xFF] (PushPre 0x11c99e 5) (callEffect (fun _ => 0x1099c0) 0x11c9a3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c99e 0x1099c0 0x11c9a3).toInstrSpec (call_rel32_effect_step 0x11c99e 0xfffed01d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c991) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c994) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c997) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c99e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c989 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c989 :=
  Rest.liftedBlock (rest_l11c989 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c989 x hx)

theorem rest_l11c9a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c9a3 bytes_l11c9a3) (entryMap (live .l11c9a3))
      6 0x11c9a3 bytes_l11c9a3 b_l11c9a3 := by
  have f0 : InstrSpec 0x11c9a3 [0x4C, 0x8D, 0xB4, 0x24, 0x18, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11c9a3) (leaR64Effect 0x11c9a3 14 (.sib 4 none 0 (.d32 0x418)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x11c9a3 14 (.sib 4 none 0 (.d32 0x418))).toInstrSpec (lea_r64_effect_step 0x11c9a3 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x418)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c9ab [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c9ab) (movR64R64Effect 0x11c9ab 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c9ab 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c9ab 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c9ae [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11c9ae) (movR64R64Effect 0x11c9ae 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c9ae 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11c9ae 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c9b1 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x11c9b1) (movR64R64Effect 0x11c9b1 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11c9b1 2 13).toInstrSpec (mov_r64_r64_effect_step 0x11c9b1 0x4c 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c9b4 [0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x11c9b4) (movR64Imm32Effect 0x11c9b4 1 0x2021a0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x11c9b4 1 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x11c9b4 0x48 0xc1 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f5 : InstrSpec 0x11c9bb [0xE8, 0xF0, 0x3F, 0xFF, 0xFF] (PushPre 0x11c9bb 5) (callEffect (fun _ => 0x1109b0) 0x11c9c0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c9bb 0x1109b0 0x11c9c0).toInstrSpec (call_rel32_effect_step 0x11c9bb 0xffff3ff0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9ae) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9b1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9b4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9bb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b0) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l11c9a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c9a3 :=
  Rest.liftedBlock (rest_l11c9a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c9a3 x hx)

theorem rest_l11c9c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c9c0 bytes_l11c9c0) (entryMap (live .l11c9c0))
      4 0x11c9c0 bytes_l11c9c0 b_l11c9c0 := by
  have f0 : InstrSpec 0x11c9c0 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c9c0) (movR64R64Effect 0x11c9c0 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c9c0 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c9c0 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c9c3 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c9c3) (movR64R64Effect 0x11c9c3 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c9c3 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c9c3 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c9c6 [0x48, 0xC7, 0xC2, 0x80, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x11c9c6) (movR64Imm32Effect 0x11c9c6 2 0x202280)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11c9c6 2 0x202280).toInstrSpec (mov_r64_imm32_effect_step 0x11c9c6 0x48 0xc2 (by decide) (by decide) (by decide) 0x202280) pre_rip
  have f3 : InstrSpec 0x11c9cd [0xE8, 0xEE, 0xCF, 0xFE, 0xFF] (PushPre 0x11c9cd 5) (callEffect (fun _ => 0x1099c0) 0x11c9d2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c9cd 0x1099c0 0x11c9d2).toInstrSpec (call_rel32_effect_step 0x11c9cd 0xfffecfee (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9c6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9cd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11c9c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c9c0 :=
  Rest.liftedBlock (rest_l11c9c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c9c0 x hx)

theorem rest_l11c9d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c9d2 bytes_l11c9d2) (entryMap (live .l11c9d2))
      5 0x11c9d2 bytes_l11c9d2 b_l11c9d2 := by
  have f0 : InstrSpec 0x11c9d2 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11c9d2) (movR64R64Effect 0x11c9d2 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c9d2 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11c9d2 0x4c 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c9d5 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11c9d5) (movR64R64Effect 0x11c9d5 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c9d5 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11c9d5 0x48 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c9d8 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x11c9d8) (movR64R64Effect 0x11c9d8 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11c9d8 2 12).toInstrSpec (mov_r64_r64_effect_step 0x11c9d8 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c9db [0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x11c9db) (movR64Imm32Effect 0x11c9db 1 0x2021a0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x11c9db 1 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x11c9db 0x48 0xc1 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f4 : InstrSpec 0x11c9e2 [0xE8, 0xC9, 0x3F, 0xFF, 0xFF] (PushPre 0x11c9e2 5) (callEffect (fun _ => 0x1109b0) 0x11c9e7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c9e2 0x1109b0 0x11c9e7).toInstrSpec (call_rel32_effect_step 0x11c9e2 0xffff3fc9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9d5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9db) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9e2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c9d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c9d2 :=
  Rest.liftedBlock (rest_l11c9d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c9d2 x hx)

theorem rest_l11c9e7_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x11c9e7 bytes_l11c9e7) [(0, 83), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x11ca6d bytes_l11c9e7_1 b_l11c9e7_1 := by
  have f20 : InstrSpec 0x11ca6d [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x11ca6d) (leaR64Effect 0x11ca6d 7 (.sib 4 none 0 (.d32 0x2b0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11ca6d 7 (.sib 4 none 0 (.d32 0x2b0))).toInstrSpec (lea_r64_effect_step 0x11ca6d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x2b0)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x11ca75 [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x11ca75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11ca75 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ca75 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ca75 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x11ca75 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x11ca7a [0xE8, 0x91, 0x15, 0xFF, 0xFF] (PushPre 0x11ca7a 5) (callEffect (fun _ => 0x10e010) 0x11ca7f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11ca7a 0x10e010 0x11ca7f).toInstrSpec (call_rel32_effect_step 0x11ca7a 0xffff1591 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (7, 86), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca75) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 83), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (6, 88), (7, 86), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca7a) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 83), (1, 63), (2, 55), (3, 69), (4, 90), (5, 67), (6, 88), (7, 86), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e010) f22 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 92) (by decide) (by decide) rfl rfl

theorem rest_l11c9e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c9e7 bytes_l11c9e7) (entryMap (live .l11c9e7))
      23 0x11c9e7 bytes_l11c9e7 b_l11c9e7 := by
  have f0 : InstrSpec 0x11c9e7 [0x48, 0x8B, 0x84, 0x24, 0x30, 0x04, 0x00, 0x00] (LoadPre 0x11c9e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x430)) s (0x11c9e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c9e7 0 (.sib 4 none 0 (.d32 0x430)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11c9e7 0 (.sib 4 none 0 (.d32 0x430))).toInstrSpec (mov_r64_m64_effect_step 0x11c9e7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x430)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c9ef [0x48, 0x8D, 0x94, 0x24, 0xF0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c9ef) (leaR64Effect 0x11c9ef 2 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11c9ef 2 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (lea_r64_effect_step 0x11c9ef 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c9f7 [0x48, 0x89, 0x42, 0x18] (StorePre 0x11c9f7 4 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x11c9f7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c9f7 0 (.base 2 (.d8 0x18)))
      [.gpr 0, .gpr 2] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c9f7 0 (.base 2 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11c9f7 0x48 (by decide) 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11c9fb [0x48, 0x8B, 0x84, 0x24, 0x28, 0x04, 0x00, 0x00] (LoadPre 0x11c9fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x428)) s (0x11c9fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c9fb 0 (.sib 4 none 0 (.d32 0x428)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11c9fb 0 (.sib 4 none 0 (.d32 0x428))).toInstrSpec (mov_r64_m64_effect_step 0x11c9fb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x428)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11ca03 [0x48, 0x89, 0x42, 0x10] (StorePre 0x11ca03 4 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x11ca03 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ca03 0 (.base 2 (.d8 0x10)))
      [.gpr 0, .gpr 2] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ca03 0 (.base 2 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11ca03 0x48 (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x11ca07 [0x48, 0x8B, 0x84, 0x24, 0x18, 0x04, 0x00, 0x00] (LoadPre 0x11ca07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x418)) s (0x11ca07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca07 0 (.sib 4 none 0 (.d32 0x418)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11ca07 0 (.sib 4 none 0 (.d32 0x418))).toInstrSpec (mov_r64_m64_effect_step 0x11ca07 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x418)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11ca0f [0x48, 0x8B, 0x8C, 0x24, 0x20, 0x04, 0x00, 0x00] (LoadPre 0x11ca0f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x420)) s (0x11ca0f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca0f 1 (.sib 4 none 0 (.d32 0x420)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11ca0f 1 (.sib 4 none 0 (.d32 0x420))).toInstrSpec (mov_r64_m64_effect_step 0x11ca0f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x420)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x11ca17 [0x48, 0x89, 0x4A, 0x08] (StorePre 0x11ca17 4 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x11ca17 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ca17 1 (.base 2 (.d8 0x8)))
      [.gpr 1, .gpr 2] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ca17 1 (.base 2 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11ca17 0x48 (by decide) 1 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11ca1b [0x48, 0x89, 0x02] (StorePre 0x11ca1b 3 (fun s => AddrMode.addr (.base 2 .none) s (0x11ca1b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11ca1b 0 (.base 2 .none))
      [.gpr 0, .gpr 2] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ca1b 0 (.base 2 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11ca1b 0x48 (by decide) 0 (.base 2 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x11ca1e [0x48, 0x8B, 0xAC, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11ca1e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11ca1e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca1e 5 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x11ca1e 5 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_r64_m64_effect_step 0x11ca1e 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11ca26 [0x48, 0x8B, 0x9C, 0x24, 0xD8, 0x01, 0x00, 0x00] (LoadPre 0x11ca26 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x11ca26 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca26 3 (.sib 4 none 0 (.d32 0x1d8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11ca26 3 (.sib 4 none 0 (.d32 0x1d8))).toInstrSpec (mov_r64_m64_effect_step 0x11ca26 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11ca2e [0x4C, 0x8B, 0xAC, 0x24, 0xE0, 0x01, 0x00, 0x00] (LoadPre 0x11ca2e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11ca2e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca2e 13 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x11ca2e 13 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_r64_m64_effect_step 0x11ca2e 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x11ca36 [0x4C, 0x8B, 0xA4, 0x24, 0xE8, 0x01, 0x00, 0x00] (LoadPre 0x11ca36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x11ca36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca36 12 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x11ca36 12 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (mov_r64_m64_effect_step 0x11ca36 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x11ca3e [0x4C, 0x8B, 0xB4, 0x24, 0xF0, 0x01, 0x00, 0x00] (LoadPre 0x11ca3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x11ca3e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca3e 14 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x11ca3e 14 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (mov_r64_m64_effect_step 0x11ca3e 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x11ca46 [0x48, 0x8B, 0x84, 0x24, 0xF8, 0x01, 0x00, 0x00] (LoadPre 0x11ca46 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f8)) s (0x11ca46 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca46 0 (.sib 4 none 0 (.d32 0x1f8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11ca46 0 (.sib 4 none 0 (.d32 0x1f8))).toInstrSpec (mov_r64_m64_effect_step 0x11ca46 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1f8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x11ca4e [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x11ca4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ca4e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ca4e 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ca4e 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x11ca4e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11ca53 [0x48, 0x8B, 0x84, 0x24, 0x00, 0x02, 0x00, 0x00] (LoadPre 0x11ca53 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x200)) s (0x11ca53 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca53 0 (.sib 4 none 0 (.d32 0x200)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11ca53 0 (.sib 4 none 0 (.d32 0x200))).toInstrSpec (mov_r64_m64_effect_step 0x11ca53 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x200)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x11ca5b [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x11ca5b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ca5b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ca5b 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ca5b 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11ca5b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x11ca60 [0x48, 0x8B, 0x84, 0x24, 0x08, 0x02, 0x00, 0x00] (LoadPre 0x11ca60 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x208)) s (0x11ca60 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca60 0 (.sib 4 none 0 (.d32 0x208)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11ca60 0 (.sib 4 none 0 (.d32 0x208))).toInstrSpec (mov_r64_m64_effect_step 0x11ca60 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x208)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x11ca68 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x11ca68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11ca68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ca68 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ca68 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x11ca68 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9ef) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 55), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9f7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (2, 55), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c9fb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 55), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca03) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (2, 55), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca07) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 55), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca0f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 55), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca17) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 63), (2, 55), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca1b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (2, 55), (4, 4), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca1e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 63), (2, 55), (4, 4), (5, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca26) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca2e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (13, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca36) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca3e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca46) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca4e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca53) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca5b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca60) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca68) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 83), (1, 63), (2, 55), (3, 69), (4, 4), (5, 67), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca6d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11c9e7_1 code

theorem block_l11c9e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c9e7 :=
  Rest.liftedBlock (rest_l11c9e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c9e7 x hx)

theorem rest_l11ca7f_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x11ca7f bytes_l11ca7f) [(0, 85), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      19 0x11cae5 bytes_l11ca7f_1 b_l11ca7f_1 := by
  have f20 : InstrSpec 0x11cae5 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x11cae5) (movR64R64Effect 0x11cae5 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11cae5 1 13).toInstrSpec (mov_r64_r64_effect_step 0x11cae5 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x11cae8 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x11cae8) (notR64Effect 0x11cae8 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x11cae8 1).toInstrSpec (not_r64_effect_step 0x11cae8 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11caeb [0x48, 0x01, 0xC1] (fun s => s.RIP = 0x11caeb) (addR64R64Effect 0x11caeb 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11caeb 1 0).toInstrSpec (add_r64_r64_effect_step 0x11caeb 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11caee [0x4C, 0x21, 0xE9] (fun s => s.RIP = 0x11caee) (andR64R64Effect 0x11caee 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11caee 1 13).toInstrSpec (and_r64_r64_effect_step 0x11caee 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x11caf1 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x11caf1) (shrR64Effect 0x11caf1 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11caf1 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x11caf1 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x11caf5 [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11caf5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11caf5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11caf5 1 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11caf5 1 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11caf5 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x11cafd [0x31, 0xC0] (fun s => s.RIP = 0x11cafd) (xorR32R32Effect 0x11cafd 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11cafd 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x11cafd 0xc0 (by decide)) pre_rip
  have f27 : InstrSpec 0x11caff [0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11caff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11caff + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11caff 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11caff 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (sub_r64_m64_effect_step 0x11caff 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x11cb07 [0x48, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x11cb07) (sarR64Effect 0x11cb07 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x11cb07 4 0 63).toInstrSpec (sar_r64_imm8_effect_step 0x11cb07 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x11cb0b [0x4C, 0x29, 0xE0] (fun s => s.RIP = 0x11cb0b) (subR64R64Effect 0x11cb0b 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11cb0b 0 12).toInstrSpec (sub_r64_r64_effect_step 0x11cb0b 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x11cb0e [0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x11cb0e) (movR64Imm64Effect 0x11cb0e 3 0x7fffffffffffffff)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x11cb0e 3 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x11cb0e 0x48 0xbb (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f31 : InstrSpec 0x11cb18 [0x48, 0x01, 0xD8] (fun s => s.RIP = 0x11cb18) (addR64R64Effect 0x11cb18 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11cb18 0 3).toInstrSpec (add_r64_r64_effect_step 0x11cb18 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x11cb1b [0x4C, 0x09, 0xE0] (fun s => s.RIP = 0x11cb1b) (orR64R64Effect 0x11cb1b 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11cb1b 0 12).toInstrSpec (or_r64_r64_effect_step 0x11cb1b 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x11cb1e [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x11cb1e) (shrR64Effect 0x11cb1e 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cb1e 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x11cb1e 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x11cb22 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11cb22 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb22 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cb22 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cb22 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11cb22 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x11cb2a [0x0F, 0xB6, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11cb2a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb2a + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11cb2a 8 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11cb2a 8 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (movzx_r32_m8_effect_step 0x11cb2a 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x11cb32 [0x24, 0x01] (fun s => s.RIP = 0x11cb32) (andAlImm8Effect 0x11cb32 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x11cb32 0x1).toInstrSpec (and_al_imm8_effect_step 0x11cb32 0x1) pre_rip
  have f37 : InstrSpec 0x11cb34 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x11cb34) (movzxR32R8Effect 0x11cb34 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x11cb34 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x11cb34 0xf8 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x11cb37 [0xE8, 0x14, 0xB2, 0x00, 0x00] (PushPre 0x11cb37 5) (callEffect (fun _ => 0x127d50) 0x11cb3c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11cb37 0x127d50 0x11cb3c).toInstrSpec (call_rel32_effect_step 0x11cb37 0xb214 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 85), (1, 88), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cae8) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 85), (1, 90), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caeb) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 85), (1, 92), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caee) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 85), (1, 94), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caf1) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 85), (1, 96), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caf5) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 85), (1, 96), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cafd) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 99), (1, 96), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caff) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 96), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb07) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 96), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb0b) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 105), (1, 96), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb0e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f30 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 105), (1, 96), (2, 2), (3, 107), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb18) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 96), (2, 2), (3, 107), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb1b) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f32 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 111), (1, 96), (2, 2), (3, 107), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb1e) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 96), (2, 2), (3, 107), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb22) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 113), (1, 96), (2, 2), (3, 107), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb2a) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 116), (1, 96), (2, 2), (3, 107), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb32) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 118), (1, 96), (2, 2), (3, 107), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb34) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 118), (1, 96), (2, 2), (3, 107), (4, 4), (5, 72), (6, 6), (7, 120), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb37) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f38 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 118), (1, 96), (2, 2), (3, 107), (4, 122), (5, 72), (6, 6), (7, 120), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f38 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 124) (by decide) (by decide) rfl rfl

theorem rest_l11ca7f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11ca7f bytes_l11ca7f) (entryMap (live .l11ca7f))
      39 0x11ca7f bytes_l11ca7f b_l11ca7f := by
  have f0 : InstrSpec 0x11ca7f [0x48, 0xB8, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF] (fun s => s.RIP = 0x11ca7f) (movR64Imm64Effect 0x11ca7f 0 0xdfe92f46681b20a0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x11ca7f 0 0xdfe92f46681b20a0).toInstrSpec (mov_r64_imm64_effect_step 0x11ca7f 0x48 0xb8 (by decide) (by decide) 0xdfe92f46681b20a0) pre_rip
  have f1 : InstrSpec 0x11ca89 [0x48, 0x89, 0x6C, 0x24, 0x58] (StorePre 0x11ca89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11ca89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ca89 5 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ca89 5 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x11ca89 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11ca8e [0x48, 0x29, 0xE8] (fun s => s.RIP = 0x11ca8e) (subR64R64Effect 0x11ca8e 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11ca8e 0 5).toInstrSpec (sub_r64_r64_effect_step 0x11ca8e 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11ca91 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x11ca91) (andR64R64Effect 0x11ca91 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11ca91 0 5).toInstrSpec (and_r64_r64_effect_step 0x11ca91 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11ca94 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x11ca94) (shrR64Effect 0x11ca94 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11ca94 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x11ca94 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11ca98 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11ca98 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11ca98 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ca98 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ca98 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11ca98 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11caa0 [0x31, 0xC0] (fun s => s.RIP = 0x11caa0) (xorR32R32Effect 0x11caa0 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11caa0 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x11caa0 0xc0 (by decide)) pre_rip
  have f7 : InstrSpec 0x11caa2 [0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11caa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11caa2 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11caa2 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11caa2 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (sub_r64_m64_effect_step 0x11caa2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11caaa [0x48, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x11caaa) (sarR64Effect 0x11caaa 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x11caaa 4 0 63).toInstrSpec (sar_r64_imm8_effect_step 0x11caaa 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11caae [0x48, 0x89, 0x5C, 0x24, 0x70] (StorePre 0x11caae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11caae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11caae 3 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11caae 3 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x11caae 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11cab3 [0x48, 0x29, 0xD8] (fun s => s.RIP = 0x11cab3) (subR64R64Effect 0x11cab3 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11cab3 0 3).toInstrSpec (sub_r64_r64_effect_step 0x11cab3 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11cab6 [0x48, 0xBD, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57, 0x5D] (fun s => s.RIP = 0x11cab6) (movR64Imm64Effect 0x11cab6 5 0x5d576e7357a4501d)
      [] [] [.reg 5, .rip] :=
    (movR64Imm64Effect_footprint 0x11cab6 5 0x5d576e7357a4501d).toInstrSpec (mov_r64_imm64_effect_step 0x11cab6 0x48 0xbd (by decide) (by decide) 0x5d576e7357a4501d) pre_rip
  have f12 : InstrSpec 0x11cac0 [0x48, 0x01, 0xE8] (fun s => s.RIP = 0x11cac0) (addR64R64Effect 0x11cac0 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11cac0 0 5).toInstrSpec (add_r64_r64_effect_step 0x11cac0 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11cac3 [0x48, 0x09, 0xD8] (fun s => s.RIP = 0x11cac3) (orR64R64Effect 0x11cac3 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11cac3 0 3).toInstrSpec (or_r64_r64_effect_step 0x11cac3 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11cac6 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x11cac6) (shrR64Effect 0x11cac6 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cac6 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x11cac6 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11caca [0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11caca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11caca + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11caca 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11caca 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11caca 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11cad2 [0x31, 0xC0] (fun s => s.RIP = 0x11cad2) (xorR32R32Effect 0x11cad2 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11cad2 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x11cad2 0xc0 (by decide)) pre_rip
  have f17 : InstrSpec 0x11cad4 [0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11cad4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cad4 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11cad4 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11cad4 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (sub_r64_m64_effect_step 0x11cad4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x11cadc [0x48, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x11cadc) (sarR64Effect 0x11cadc 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x11cadc 4 0 63).toInstrSpec (sar_r64_imm8_effect_step 0x11cadc 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11cae0 [0x4C, 0x89, 0x6C, 0x24, 0x50] (StorePre 0x11cae0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11cae0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11cae0 13 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cae0 13 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x11cae0 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca89) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca8e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca91) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca94) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ca98) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caa0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caa2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caaa) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caae) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cab3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cab6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cac0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cac3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cac6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11caca) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cad2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cad4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cadc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cae0) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 85), (2, 2), (3, 3), (4, 4), (5, 72), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cae5) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11ca7f_1 code

theorem block_l11ca7f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11ca7f :=
  Rest.liftedBlock (rest_l11ca7f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11ca7f x hx)

theorem rest_l11cb3c_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x11cb3c bytes_l11cb3c) [(0, 85), (1, 70), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      20 0x11cb9f bytes_l11cb3c_1 b_l11cb3c_1 := by
  have f20 : InstrSpec 0x11cb9f [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x11cb9f) (movR64R64Effect 0x11cb9f 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11cb9f 1 2).toInstrSpec (mov_r64_r64_effect_step 0x11cb9f 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x11cba2 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x11cba2) (notR64Effect 0x11cba2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x11cba2 1).toInstrSpec (not_r64_effect_step 0x11cba2 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11cba5 [0x48, 0x01, 0xC1] (fun s => s.RIP = 0x11cba5) (addR64R64Effect 0x11cba5 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11cba5 1 0).toInstrSpec (add_r64_r64_effect_step 0x11cba5 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11cba8 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x11cba8) (andR64R64Effect 0x11cba8 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11cba8 1 2).toInstrSpec (and_r64_r64_effect_step 0x11cba8 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x11cbab [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x11cbab) (shrR64Effect 0x11cbab 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cbab 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x11cbab 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x11cbaf [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11cbaf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbaf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cbaf 1 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cbaf 1 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11cbaf 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x11cbb7 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11cbb7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbb7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cbb7 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11cbb7 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_r64_m64_effect_step 0x11cbb7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x11cbbf [0x31, 0xC9] (fun s => s.RIP = 0x11cbbf) (xorR32R32Effect 0x11cbbf 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11cbbf 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x11cbbf 0xc9 (by decide)) pre_rip
  have f28 : InstrSpec 0x11cbc1 [0x48, 0x29, 0xC1] (fun s => s.RIP = 0x11cbc1) (subR64R64Effect 0x11cbc1 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11cbc1 1 0).toInstrSpec (sub_r64_r64_effect_step 0x11cbc1 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x11cbc4 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x11cbc4) (sarR64Effect 0x11cbc4 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x11cbc4 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x11cbc4 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x11cbc8 [0x48, 0x8B, 0x6C, 0x24, 0x28] (LoadPre 0x11cbc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11cbc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cbc8 5 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x11cbc8 5 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x11cbc8 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x11cbcd [0x48, 0x29, 0xE9] (fun s => s.RIP = 0x11cbcd) (subR64R64Effect 0x11cbcd 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11cbcd 1 5).toInstrSpec (sub_r64_r64_effect_step 0x11cbcd 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x11cbd0 [0x48, 0x01, 0xD9] (fun s => s.RIP = 0x11cbd0) (addR64R64Effect 0x11cbd0 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11cbd0 1 3).toInstrSpec (add_r64_r64_effect_step 0x11cbd0 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x11cbd3 [0x48, 0x09, 0xE9] (fun s => s.RIP = 0x11cbd3) (orR64R64Effect 0x11cbd3 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11cbd3 1 5).toInstrSpec (or_r64_r64_effect_step 0x11cbd3 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x11cbd6 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x11cbd6) (shrR64Effect 0x11cbd6 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cbd6 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x11cbd6 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x11cbda [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11cbda 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbda + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cbda 1 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cbda 1 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11cbda 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x11cbe2 [0x0F, 0xB6, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11cbe2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbe2 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11cbe2 8 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11cbe2 8 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (movzx_r32_m8_effect_step 0x11cbe2 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x11cbea [0x24, 0x01] (fun s => s.RIP = 0x11cbea) (andAlImm8Effect 0x11cbea 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x11cbea 0x1).toInstrSpec (and_al_imm8_effect_step 0x11cbea 0x1) pre_rip
  have f38 : InstrSpec 0x11cbec [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x11cbec) (movzxR32R8Effect 0x11cbec 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x11cbec 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x11cbec 0xf8 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x11cbef [0xE8, 0x5C, 0xB1, 0x00, 0x00] (PushPre 0x11cbef 5) (callEffect (fun _ => 0x127d50) 0x11cbf4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11cbef 0x127d50 0x11cbf4).toInstrSpec (call_rel32_effect_step 0x11cbef 0xb15c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 85), (1, 89), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cba2) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 85), (1, 91), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cba5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 85), (1, 93), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cba8) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 85), (1, 95), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbab) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 85), (1, 97), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbaf) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 85), (1, 97), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbb7) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 100), (1, 97), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbbf) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 100), (1, 102), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbc1) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 100), (1, 104), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbc4) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 100), (1, 106), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbc8) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f30 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 100), (1, 106), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbcd) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 100), (1, 110), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbd0) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 100), (1, 112), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbd3) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 100), (1, 114), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbd6) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 100), (1, 116), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbda) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.exec (n := 118) (ρ' := [(0, 100), (1, 116), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbe2) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 116), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbea) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 121), (1, 116), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbec) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 121), (1, 116), (2, 87), (3, 3), (4, 4), (5, 108), (6, 6), (7, 123), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbef) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f39 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 121), (1, 116), (2, 87), (3, 3), (4, 125), (5, 108), (6, 6), (7, 123), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f39 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 127) (by decide) (by decide) rfl rfl

theorem rest_l11cb3c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11cb3c bytes_l11cb3c) (entryMap (live .l11cb3c))
      40 0x11cb3c bytes_l11cb3c b_l11cb3c := by
  have f0 : InstrSpec 0x11cb3c [0x88, 0x44, 0x24, 0x30] (StorePre 0x11cb3c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11cb3c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11cb3c 4 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11cb3c 4 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m8_r8_effect_step 0x11cb3c 0 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11cb40 [0x48, 0xB8, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF] (fun s => s.RIP = 0x11cb40) (movR64Imm64Effect 0x11cb40 0 0xdfe92f46681b20a0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x11cb40 0 0xdfe92f46681b20a0).toInstrSpec (mov_r64_imm64_effect_step 0x11cb40 0x48 0xb8 (by decide) (by decide) 0xdfe92f46681b20a0) pre_rip
  have f2 : InstrSpec 0x11cb4a [0x4C, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x11cb4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11cb4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cb4a 14 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cb4a 14 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x11cb4a 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11cb52 [0x4C, 0x29, 0xF0] (fun s => s.RIP = 0x11cb52) (subR64R64Effect 0x11cb52 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11cb52 0 14).toInstrSpec (sub_r64_r64_effect_step 0x11cb52 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11cb55 [0x4C, 0x21, 0xF0] (fun s => s.RIP = 0x11cb55) (andR64R64Effect 0x11cb55 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11cb55 0 14).toInstrSpec (and_r64_r64_effect_step 0x11cb55 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11cb58 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x11cb58) (shrR64Effect 0x11cb58 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cb58 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x11cb58 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11cb5c [0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11cb5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb5c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cb5c 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cb5c 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11cb5c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x11cb64 [0x31, 0xC0] (fun s => s.RIP = 0x11cb64) (xorR32R32Effect 0x11cb64 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11cb64 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x11cb64 0xc0 (by decide)) pre_rip
  have f8 : InstrSpec 0x11cb66 [0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11cb66 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb66 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11cb66 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11cb66 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (sub_r64_m64_effect_step 0x11cb66 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11cb6e [0x48, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x11cb6e) (sarR64Effect 0x11cb6e 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x11cb6e 4 0 63).toInstrSpec (sar_r64_imm8_effect_step 0x11cb6e 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11cb72 [0x48, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x11cb72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11cb72 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cb72 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cb72 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x11cb72 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11cb77 [0x48, 0x29, 0xC8] (fun s => s.RIP = 0x11cb77) (subR64R64Effect 0x11cb77 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11cb77 0 1).toInstrSpec (sub_r64_r64_effect_step 0x11cb77 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11cb7a [0x48, 0x01, 0xE8] (fun s => s.RIP = 0x11cb7a) (addR64R64Effect 0x11cb7a 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11cb7a 0 5).toInstrSpec (add_r64_r64_effect_step 0x11cb7a 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11cb7d [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x11cb7d) (orR64R64Effect 0x11cb7d 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11cb7d 0 1).toInstrSpec (or_r64_r64_effect_step 0x11cb7d 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11cb80 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x11cb80) (shrR64Effect 0x11cb80 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cb80 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x11cb80 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11cb84 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11cb84 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb84 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cb84 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cb84 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11cb84 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11cb8c [0x31, 0xC0] (fun s => s.RIP = 0x11cb8c) (xorR32R32Effect 0x11cb8c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11cb8c 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x11cb8c 0xc0 (by decide)) pre_rip
  have f17 : InstrSpec 0x11cb8e [0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11cb8e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb8e + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11cb8e 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11cb8e 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (sub_r64_m64_effect_step 0x11cb8e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x11cb96 [0x48, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x11cb96) (sarR64Effect 0x11cb96 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x11cb96 4 0 63).toInstrSpec (sar_r64_imm8_effect_step 0x11cb96 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11cb9a [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x11cb9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11cb9a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cb9a 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11cb9a 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11cb9a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb40) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb4a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb52) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb55) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb58) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb5c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb64) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb66) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb6e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb72) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb77) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb7a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb7d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb80) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb84) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb8c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb8e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb96) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 70), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb9a) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (1, 70), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cb9f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11cb3c_1 code

theorem block_l11cb3c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11cb3c :=
  Rest.liftedBlock (rest_l11cb3c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11cb3c x hx)

theorem rest_l11cbf4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11cbf4 bytes_l11cbf4) (entryMap (live .l11cbf4))
      12 0x11cbf4 bytes_l11cbf4 b_l11cbf4 := by
  have f0 : InstrSpec 0x11cbf4 [0x88, 0x44, 0x24, 0x48] (StorePre 0x11cbf4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11cbf4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11cbf4 4 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11cbf4 4 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m8_r8_effect_step 0x11cbf4 0 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11cbf8 [0x48, 0x8B, 0x5C, 0x24, 0x58] (LoadPre 0x11cbf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11cbf8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cbf8 3 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11cbf8 3 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x11cbf8 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11cbfd [0x48, 0x89, 0x9C, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11cbfd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbfd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cbfd 3 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cbfd 3 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11cbfd 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11cc05 [0x4C, 0x8B, 0x6C, 0x24, 0x70] (LoadPre 0x11cc05 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11cc05 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cc05 13 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x11cc05 13 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x11cc05 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11cc0a [0x4C, 0x89, 0xAC, 0x24, 0xD8, 0x01, 0x00, 0x00] (StorePre 0x11cc0a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x11cc0a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc0a 13 (.sib 4 none 0 (.d32 0x1d8)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cc0a 13 (.sib 4 none 0 (.d32 0x1d8))).toInstrSpec (mov_m64_r64_effect_step 0x11cc0a 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x11cc12 [0x4C, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x11cc12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11cc12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cc12 14 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x11cc12 14 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x11cc12 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11cc17 [0x4C, 0x89, 0xB4, 0x24, 0xE0, 0x01, 0x00, 0x00] (StorePre 0x11cc17 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11cc17 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc17 14 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cc17 14 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_m64_r64_effect_step 0x11cc17 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x11cc1f [0x4C, 0x89, 0xA4, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x11cc1f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x11cc1f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc1f 12 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cc1f 12 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (mov_m64_r64_effect_step 0x11cc1f 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11cc27 [0x48, 0x8D, 0xBC, 0x24, 0x18, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11cc27) (leaR64Effect 0x11cc27 7 (.sib 4 none 0 (.d32 0x418)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11cc27 7 (.sib 4 none 0 (.d32 0x418))).toInstrSpec (lea_r64_effect_step 0x11cc27 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x418)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11cc2f [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11cc2f) (movR64R64Effect 0x11cc2f 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cc2f 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11cc2f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11cc32 [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x11cc32) (movR64Imm32Effect 0x11cc32 2 0x2021a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11cc32 2 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x11cc32 0x48 0xc2 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f11 : InstrSpec 0x11cc39 [0xE8, 0x42, 0x3F, 0xFF, 0xFF] (PushPre 0x11cc39 5) (callEffect (fun _ => 0x110b80) 0x11cc3e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11cc39 0x110b80 0x11cc3e).toInstrSpec (call_rel32_effect_step 0x11cc39 0xffff3f42 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (4, 4), (5, 5), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbf8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cbfd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc05) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (12, 12), (13, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc0a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (12, 12), (13, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc12) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (12, 12), (13, 57), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc17) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (12, 12), (13, 57), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc1f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (12, 12), (13, 57), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc27) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (7, 64), (12, 12), (13, 57), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc2f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 57), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc32) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (2, 68), (3, 54), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 57), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc39) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (2, 68), (3, 54), (4, 70), (5, 5), (6, 66), (7, 64), (12, 12), (13, 57), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b80) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 72) (by decide) (by decide) rfl rfl

theorem block_l11cbf4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11cbf4 :=
  Rest.liftedBlock (rest_l11cbf4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11cbf4 x hx)

theorem rest_l11cc3e_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x11cc3e bytes_l11cc3e) [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 80), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x11ccb4 bytes_l11cc3e_1 b_l11cc3e_1 := by
  have f20 : InstrSpec 0x11ccb4 [0x4C, 0x8B, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x11ccb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11ccb4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ccb4 12 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x11ccb4 12 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x11ccb4 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x11ccbc [0x4C, 0x89, 0xA4, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11ccbc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11ccbc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccbc 12 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ccbc 12 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x11ccbc 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x11ccc4 [0x4C, 0x8B, 0x6C, 0x24, 0x40] (LoadPre 0x11ccc4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ccc4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ccc4 13 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x11ccc4 13 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x11ccc4 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x11ccc9 [0x4C, 0x89, 0xAC, 0x24, 0xD8, 0x01, 0x00, 0x00] (StorePre 0x11ccc9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x11ccc9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccc9 13 (.sib 4 none 0 (.d32 0x1d8)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ccc9 13 (.sib 4 none 0 (.d32 0x1d8))).toInstrSpec (mov_m64_r64_effect_step 0x11ccc9 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x11ccd1 [0x4C, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x11ccd1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ccd1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ccd1 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x11ccd1 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11ccd1 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x11ccd6 [0x4C, 0x89, 0xB4, 0x24, 0xE0, 0x01, 0x00, 0x00] (StorePre 0x11ccd6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11ccd6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccd6 14 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ccd6 14 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_m64_r64_effect_step 0x11ccd6 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x11ccde [0x48, 0x89, 0xAC, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x11ccde 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x11ccde + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccde 5 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ccde 5 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (mov_m64_r64_effect_step 0x11ccde 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x11cce6 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11cce6) (leaR64Effect 0x11cce6 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11cce6 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11cce6 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x11ccee [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11ccee) (movR64R64Effect 0x11ccee 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11ccee 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11ccee 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x11ccf1 [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x11ccf1) (movR64Imm32Effect 0x11ccf1 2 0x2021a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11ccf1 2 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x11ccf1 0x48 0xc2 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f30 : InstrSpec 0x11ccf8 [0xE8, 0x83, 0x3E, 0xFF, 0xFF] (PushPre 0x11ccf8 5) (callEffect (fun _ => 0x110b80) 0x11ccfd)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11ccf8 0x110b80 0x11ccfd).toInstrSpec (call_rel32_effect_step 0x11ccf8 0xffff3e83 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 88), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccbc) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 88), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccc4) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 88), (13, 91), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccc9) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 88), (13, 91), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccd1) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f24 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 88), (13, 91), (14, 94), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccd6) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 88), (13, 91), (14, 94), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccde) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 88), (13, 91), (14, 94), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cce6) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f27 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (7, 98), (12, 88), (13, 91), (14, 94), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccee) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f28 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (6, 100), (7, 98), (12, 88), (13, 91), (14, 94), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccf1) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 56), (1, 76), (2, 102), (3, 84), (4, 4), (5, 5), (6, 100), (7, 98), (12, 88), (13, 91), (14, 94), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccf8) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f30 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 56), (1, 76), (2, 102), (3, 84), (4, 104), (5, 5), (6, 100), (7, 98), (12, 88), (13, 91), (14, 94), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b80) f30 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 106) (by decide) (by decide) rfl rfl

theorem rest_l11cc3e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11cc3e bytes_l11cc3e) (entryMap (live .l11cc3e))
      31 0x11cc3e bytes_l11cc3e b_l11cc3e := by
  have f0 : InstrSpec 0x11cc3e [0x0F, 0xB6, 0x44, 0x24, 0x30] (LoadPre 0x11cc3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11cc3e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11cc3e 5 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11cc3e 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m8_effect_step 0x11cc3e 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11cc43 [0x88, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11cc43 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cc43 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x11cc43 7 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11cc43 7 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m8_r8_effect_step 0x11cc43 0 (by decide) (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11cc4a [0x0F, 0xB6, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11cc4a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cc4a + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11cc4a 8 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11cc4a 8 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (movzx_r32_m8_effect_step 0x11cc4a 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11cc52 [0x48, 0x8B, 0x8C, 0x24, 0x18, 0x04, 0x00, 0x00] (LoadPre 0x11cc52 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x418)) s (0x11cc52 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cc52 1 (.sib 4 none 0 (.d32 0x418)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cc52 1 (.sib 4 none 0 (.d32 0x418))).toInstrSpec (mov_r64_m64_effect_step 0x11cc52 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x418)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11cc5a [0x48, 0x8B, 0x94, 0x24, 0x20, 0x04, 0x00, 0x00] (LoadPre 0x11cc5a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x420)) s (0x11cc5a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cc5a 2 (.sib 4 none 0 (.d32 0x420)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11cc5a 2 (.sib 4 none 0 (.d32 0x420))).toInstrSpec (mov_r64_m64_effect_step 0x11cc5a 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x420)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11cc62 [0x84, 0xC0] (fun s => s.RIP = 0x11cc62) (testR8R8Effect 0x11cc62 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11cc62 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11cc62 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11cc64 [0x48, 0x0F, 0x45, 0xD9] (fun s => s.RIP = 0x11cc64) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc64 4 3 1))
      [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 3, .rip] :=
    (cmovR64R64Effect_footprint 0x11cc64 4 3 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11cc64 5 0x48 (by decide) 0xd9 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11cc68 [0x84, 0xC0] (fun s => s.RIP = 0x11cc68) (testR8R8Effect 0x11cc68 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11cc68 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11cc68 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11cc6a [0x4C, 0x0F, 0x45, 0xEA] (fun s => s.RIP = 0x11cc6a) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc6a 4 13 2))
      [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 13, .rip] :=
    (cmovR64R64Effect_footprint 0x11cc6a 4 13 2 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11cc6a 5 0x4c (by decide) 0xea (by decide) c)) pre_rip
  have f9 : InstrSpec 0x11cc6e [0x48, 0x8B, 0x8C, 0x24, 0x28, 0x04, 0x00, 0x00] (LoadPre 0x11cc6e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x428)) s (0x11cc6e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cc6e 1 (.sib 4 none 0 (.d32 0x428)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cc6e 1 (.sib 4 none 0 (.d32 0x428))).toInstrSpec (mov_r64_m64_effect_step 0x11cc6e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x428)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11cc76 [0x84, 0xC0] (fun s => s.RIP = 0x11cc76) (testR8R8Effect 0x11cc76 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11cc76 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11cc76 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11cc78 [0x4C, 0x0F, 0x45, 0xF1] (fun s => s.RIP = 0x11cc78) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc78 4 14 1))
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 14, .rip] :=
    (cmovR64R64Effect_footprint 0x11cc78 4 14 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11cc78 5 0x4c (by decide) 0xf1 (by decide) c)) pre_rip
  have f12 : InstrSpec 0x11cc7c [0x48, 0x8B, 0x8C, 0x24, 0x30, 0x04, 0x00, 0x00] (LoadPre 0x11cc7c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x430)) s (0x11cc7c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cc7c 1 (.sib 4 none 0 (.d32 0x430)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cc7c 1 (.sib 4 none 0 (.d32 0x430))).toInstrSpec (mov_r64_m64_effect_step 0x11cc7c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x430)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x11cc84 [0x84, 0xC0] (fun s => s.RIP = 0x11cc84) (testR8R8Effect 0x11cc84 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11cc84 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11cc84 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11cc86 [0x4C, 0x0F, 0x45, 0xE1] (fun s => s.RIP = 0x11cc86) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc86 4 12 1))
      [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 12, .rip] :=
    (cmovR64R64Effect_footprint 0x11cc86 4 12 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11cc86 5 0x4c (by decide) 0xe1 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x11cc8a [0x48, 0x89, 0x9C, 0x24, 0x70, 0x02, 0x00, 0x00] (StorePre 0x11cc8a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x270)) s (0x11cc8a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc8a 3 (.sib 4 none 0 (.d32 0x270)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cc8a 3 (.sib 4 none 0 (.d32 0x270))).toInstrSpec (mov_m64_r64_effect_step 0x11cc8a 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x270)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11cc92 [0x4C, 0x89, 0xAC, 0x24, 0x78, 0x02, 0x00, 0x00] (StorePre 0x11cc92 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x278)) s (0x11cc92 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc92 13 (.sib 4 none 0 (.d32 0x278)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cc92 13 (.sib 4 none 0 (.d32 0x278))).toInstrSpec (mov_m64_r64_effect_step 0x11cc92 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x278)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x11cc9a [0x48, 0xBB, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x11cc9a) (movR64Imm64Effect 0x11cc9a 3 0x3ffffffffffffc)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x11cc9a 3 0x3ffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x11cc9a 0x48 0xbb (by decide) (by decide) 0x3ffffffffffffc) pre_rip
  have f18 : InstrSpec 0x11cca4 [0x4C, 0x89, 0xB4, 0x24, 0x80, 0x02, 0x00, 0x00] (StorePre 0x11cca4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x280)) s (0x11cca4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cca4 14 (.sib 4 none 0 (.d32 0x280)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cca4 14 (.sib 4 none 0 (.d32 0x280))).toInstrSpec (mov_m64_r64_effect_step 0x11cca4 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x280)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11ccac [0x4C, 0x89, 0xA4, 0x24, 0x88, 0x02, 0x00, 0x00] (StorePre 0x11ccac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x288)) s (0x11ccac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccac 12 (.sib 4 none 0 (.d32 0x288)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ccac 12 (.sib 4 none 0 (.d32 0x288))).toInstrSpec (mov_m64_r64_effect_step 0x11ccac 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x288)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc43) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc4a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc52) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc5a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 56), (1, 58), (2, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc62) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 56), (1, 58), (2, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc64) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 56), (1, 58), (2, 60), (3, 64), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc68) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 56), (1, 58), (2, 60), (3, 64), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc6a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 56), (1, 58), (2, 60), (3, 64), (4, 4), (5, 5), (12, 12), (13, 68), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc6e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 56), (1, 70), (2, 60), (3, 64), (4, 4), (5, 5), (12, 12), (13, 68), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc76) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 56), (1, 70), (2, 60), (3, 64), (4, 4), (5, 5), (12, 12), (13, 68), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc78) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 56), (1, 70), (2, 60), (3, 64), (4, 4), (5, 5), (12, 12), (13, 68), (14, 74), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc7c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 64), (4, 4), (5, 5), (12, 12), (13, 68), (14, 74), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc84) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 64), (4, 4), (5, 5), (12, 12), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc86) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 64), (4, 4), (5, 5), (12, 80), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc8a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 64), (4, 4), (5, 5), (12, 80), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc92) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 64), (4, 4), (5, 5), (12, 80), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cc9a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 80), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cca4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 80), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccac) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 56), (1, 76), (2, 60), (3, 84), (4, 4), (5, 5), (12, 80), (13, 68), (14, 74), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ccb4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11cc3e_1 code

theorem block_l11cc3e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11cc3e :=
  Rest.liftedBlock (rest_l11cc3e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11cc3e x hx)

theorem rest_l11ccfd_4 [Bindings] (code : CodeMap) :
    Rest (n := 199) code lifted (codeRange 0x11ccfd bytes_l11ccfd) [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 196), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      19 0x11ce9c bytes_l11ccfd_4 b_l11ccfd_4 := by
  have f80 : InstrSpec 0x11ce9c [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x11ce9c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce9c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce9c 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce9c 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce9c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f81 : InstrSpec 0x11cea1 [0x49, 0x8B, 0x34, 0x32] (LoadPre 0x11cea1 (fun s => AddrMode.addr (.sib 10 (some 6) 0 .none) s (0x11cea1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11cea1 6 (.sib 10 (some 6) 0 .none))
      [.gpr 10, .gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11cea1 6 (.sib 10 (some 6) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11cea1 0x49 (by decide) 6 (.sib 10 (some 6) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f82 : InstrSpec 0x11cea5 [0x48, 0x89, 0xB4, 0x24, 0xA0, 0x03, 0x00, 0x00] (StorePre 0x11cea5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3a0)) s (0x11cea5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cea5 6 (.sib 4 none 0 (.d32 0x3a0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cea5 6 (.sib 4 none 0 (.d32 0x3a0))).toInstrSpec (mov_m64_r64_effect_step 0x11cea5 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x3a0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f83 : InstrSpec 0x11cead [0x49, 0xBC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x11cead) (movR64Imm64Effect 0x11cead 12 0xfffffffffffff)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x11cead 12 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x11cead 0x49 0xbc (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f84 : InstrSpec 0x11ceb7 [0x4C, 0x21, 0xE0] (fun s => s.RIP = 0x11ceb7) (andR64R64Effect 0x11ceb7 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11ceb7 0 12).toInstrSpec (and_r64_r64_effect_step 0x11ceb7 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x11ceba [0x48, 0x89, 0x84, 0x24, 0xC8, 0x03, 0x00, 0x00] (StorePre 0x11ceba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3c8)) s (0x11ceba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ceba 0 (.sib 4 none 0 (.d32 0x3c8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ceba 0 (.sib 4 none 0 (.d32 0x3c8))).toInstrSpec (mov_m64_r64_effect_step 0x11ceba 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x3c8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f86 : InstrSpec 0x11cec2 [0x4C, 0x21, 0xE1] (fun s => s.RIP = 0x11cec2) (andR64R64Effect 0x11cec2 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11cec2 1 12).toInstrSpec (and_r64_r64_effect_step 0x11cec2 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x11cec5 [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x03, 0x00, 0x00] (StorePre 0x11cec5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3d0)) s (0x11cec5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cec5 1 (.sib 4 none 0 (.d32 0x3d0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cec5 1 (.sib 4 none 0 (.d32 0x3d0))).toInstrSpec (mov_m64_r64_effect_step 0x11cec5 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x3d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f88 : InstrSpec 0x11cecd [0x4C, 0x21, 0xE2] (fun s => s.RIP = 0x11cecd) (andR64R64Effect 0x11cecd 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11cecd 2 12).toInstrSpec (and_r64_r64_effect_step 0x11cecd 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x11ced0 [0x48, 0x89, 0x94, 0x24, 0xD8, 0x03, 0x00, 0x00] (StorePre 0x11ced0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3d8)) s (0x11ced0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ced0 2 (.sib 4 none 0 (.d32 0x3d8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ced0 2 (.sib 4 none 0 (.d32 0x3d8))).toInstrSpec (mov_m64_r64_effect_step 0x11ced0 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x3d8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x11ced8 [0x4C, 0x21, 0xE7] (fun s => s.RIP = 0x11ced8) (andR64R64Effect 0x11ced8 7 12)
      [.gpr 7, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11ced8 7 12).toInstrSpec (and_r64_r64_effect_step 0x11ced8 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x11cedb [0x48, 0x89, 0xBC, 0x24, 0xE0, 0x03, 0x00, 0x00] (StorePre 0x11cedb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3e0)) s (0x11cedb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cedb 7 (.sib 4 none 0 (.d32 0x3e0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cedb 7 (.sib 4 none 0 (.d32 0x3e0))).toInstrSpec (mov_m64_r64_effect_step 0x11cedb 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x3e0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f92 : InstrSpec 0x11cee3 [0x4C, 0x89, 0x84, 0x24, 0xE8, 0x03, 0x00, 0x00] (StorePre 0x11cee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3e8)) s (0x11cee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cee3 8 (.sib 4 none 0 (.d32 0x3e8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cee3 8 (.sib 4 none 0 (.d32 0x3e8))).toInstrSpec (mov_m64_r64_effect_step 0x11cee3 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x3e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f93 : InstrSpec 0x11ceeb [0x0F, 0xB6, 0x4C, 0x24, 0x30] (LoadPre 0x11ceeb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11ceeb + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11ceeb 5 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x11ceeb 5 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m8_effect_step 0x11ceeb 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f94 : InstrSpec 0x11cef0 [0x48, 0x8D, 0xAC, 0x24, 0x28, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11cef0) (leaR64Effect 0x11cef0 5 (.sib 4 none 0 (.d32 0x328)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x11cef0 5 (.sib 4 none 0 (.d32 0x328))).toInstrSpec (lea_r64_effect_step 0x11cef0 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x328)) (by decide) (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x11cef8 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11cef8) (movR64R64Effect 0x11cef8 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cef8 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11cef8 0x48 0xef (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x11cefb [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x11cefb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11cefb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cefb 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11cefb 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x11cefb 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x11cf00 [0x48, 0x8D, 0x94, 0x24, 0xA0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11cf00) (leaR64Effect 0x11cf00 2 (.sib 4 none 0 (.d32 0x3a0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11cf00 2 (.sib 4 none 0 (.d32 0x3a0))).toInstrSpec (lea_r64_effect_step 0x11cf00 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x3a0)) (by decide) (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x11cf08 [0xE8, 0xB3, 0x2D, 0xFF, 0xFF] (PushPre 0x11cf08 5) (callEffect (fun _ => 0x10fcc0) 0x11cf0d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11cf08 0x10fcc0 0x11cf0d).toInstrSpec (call_rel32_effect_step 0x11cf08 0xffff2db3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f80 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 199), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cea1) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f81 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cea5) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.exec (n := 203) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cead) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f83 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ceb7) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f84 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 206), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ceba) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.exec (n := 208) (ρ' := [(0, 206), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cec2) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f86 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 206), (1, 209), (2, 134), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cec5) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.exec (n := 211) (ρ' := [(0, 206), (1, 209), (2, 134), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cecd) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f88 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 206), (1, 209), (2, 212), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ced0) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.exec (n := 214) (ρ' := [(0, 206), (1, 209), (2, 212), (3, 3), (4, 4), (5, 82), (6, 201), (7, 171), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ced8) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f90 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 206), (1, 209), (2, 212), (3, 3), (4, 4), (5, 82), (6, 201), (7, 215), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cedb) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.exec (n := 217) (ρ' := [(0, 206), (1, 209), (2, 212), (3, 3), (4, 4), (5, 82), (6, 201), (7, 215), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cee3) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 218) (RestInside.exec (n := 218) (ρ' := [(0, 206), (1, 209), (2, 212), (3, 3), (4, 4), (5, 82), (6, 201), (7, 215), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ceeb) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 206), (1, 219), (2, 212), (3, 3), (4, 4), (5, 82), (6, 201), (7, 215), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cef0) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f94 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 206), (1, 219), (2, 212), (3, 3), (4, 4), (5, 221), (6, 201), (7, 215), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cef8) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f95 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 206), (1, 219), (2, 212), (3, 3), (4, 4), (5, 221), (6, 201), (7, 223), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cefb) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f96 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 206), (1, 219), (2, 212), (3, 3), (4, 4), (5, 221), (6, 225), (7, 223), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf00) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f97 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 206), (1, 219), (2, 227), (3, 3), (4, 4), (5, 221), (6, 225), (7, 223), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf08) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f98 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 206), (1, 219), (2, 227), (3, 3), (4, 229), (5, 221), (6, 225), (7, 223), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f98 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 231) (by decide) (by decide) rfl rfl

theorem rest_l11ccfd_3 [Bindings] (code : CodeMap) :
    Rest (n := 164) code lifted (codeRange 0x11ccfd bytes_l11ccfd) [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 162), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      39 0x11ce32 bytes_l11ccfd_3 b_l11ccfd_3 := by
  have f60 : InstrSpec 0x11ce32 [0x4F, 0x8B, 0x44, 0x02, 0x50] (LoadPre 0x11ce32 (fun s => AddrMode.addr (.sib 10 (some 8) 0 (.d8 0x50)) s (0x11ce32 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce32 8 (.sib 10 (some 8) 0 (.d8 0x50)))
      [.gpr 10, .gpr 8] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11ce32 8 (.sib 10 (some 8) 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x11ce32 0x4f (by decide) 0 (.sib 10 (some 8) 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x11ce37 [0x4D, 0x89, 0x01] (StorePre 0x11ce37 3 (fun s => AddrMode.addr (.base 9 .none) s (0x11ce37 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11ce37 8 (.base 9 .none))
      [.gpr 8, .gpr 9] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ce37 8 (.base 9 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11ce37 0x4d (by decide) 0 (.base 9 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f62 : InstrSpec 0x11ce3a [0x49, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x11ce3a) (movR64Imm64Effect 0x11ce3a 14 0xffffffffffff)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x11ce3a 14 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x11ce3a 0x49 0xbe (by decide) (by decide) 0xffffffffffff) pre_rip
  have f63 : InstrSpec 0x11ce44 [0x4C, 0x21, 0xF6] (fun s => s.RIP = 0x11ce44) (andR64R64Effect 0x11ce44 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11ce44 6 14).toInstrSpec (and_r64_r64_effect_step 0x11ce44 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x11ce47 [0x48, 0x01, 0xDF] (fun s => s.RIP = 0x11ce47) (addR64R64Effect 0x11ce47 7 3)
      [.gpr 7, .gpr 3] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ce47 7 3).toInstrSpec (add_r64_r64_effect_step 0x11ce47 0x48 0xdf (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x11ce4a [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x11ce4a) (movR64R64Effect 0x11ce4a 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11ce4a 8 7).toInstrSpec (mov_r64_r64_effect_step 0x11ce4a 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x11ce4d [0x49, 0xC1, 0xE8, 0x34] (fun s => s.RIP = 0x11ce4d) (shrR64Effect 0x11ce4d 4 8 52)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x11ce4d 4 8 52).toInstrSpec (shr_r64_imm8_effect_step 0x11ce4d 0x49 0xe8 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x11ce51 [0x49, 0x01, 0xF0] (fun s => s.RIP = 0x11ce51) (addR64R64Effect 0x11ce51 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ce51 8 6).toInstrSpec (add_r64_r64_effect_step 0x11ce51 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x11ce54 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x11ce54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce54 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce54 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce54 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce54 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f69 : InstrSpec 0x11ce59 [0x49, 0x8B, 0x74, 0x32, 0x08] (LoadPre 0x11ce59 (fun s => AddrMode.addr (.sib 10 (some 6) 0 (.d8 0x8)) s (0x11ce59 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce59 6 (.sib 10 (some 6) 0 (.d8 0x8)))
      [.gpr 10, .gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce59 6 (.sib 10 (some 6) 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce59 0x49 (by decide) 6 (.sib 10 (some 6) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f70 : InstrSpec 0x11ce5e [0x48, 0x89, 0xB4, 0x24, 0xA8, 0x03, 0x00, 0x00] (StorePre 0x11ce5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3a8)) s (0x11ce5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ce5e 6 (.sib 4 none 0 (.d32 0x3a8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ce5e 6 (.sib 4 none 0 (.d32 0x3a8))).toInstrSpec (mov_m64_r64_effect_step 0x11ce5e 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x3a8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f71 : InstrSpec 0x11ce66 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x11ce66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce66 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce66 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce66 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x11ce6b [0x49, 0x8B, 0x74, 0x32, 0x10] (LoadPre 0x11ce6b (fun s => AddrMode.addr (.sib 10 (some 6) 0 (.d8 0x10)) s (0x11ce6b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce6b 6 (.sib 10 (some 6) 0 (.d8 0x10)))
      [.gpr 10, .gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce6b 6 (.sib 10 (some 6) 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11ce6b 0x49 (by decide) 6 (.sib 10 (some 6) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x11ce70 [0x48, 0x89, 0xB4, 0x24, 0xB0, 0x03, 0x00, 0x00] (StorePre 0x11ce70 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3b0)) s (0x11ce70 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ce70 6 (.sib 4 none 0 (.d32 0x3b0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ce70 6 (.sib 4 none 0 (.d32 0x3b0))).toInstrSpec (mov_m64_r64_effect_step 0x11ce70 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x3b0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f74 : InstrSpec 0x11ce78 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x11ce78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce78 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce78 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce78 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce78 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f75 : InstrSpec 0x11ce7d [0x49, 0x8B, 0x74, 0x32, 0x18] (LoadPre 0x11ce7d (fun s => AddrMode.addr (.sib 10 (some 6) 0 (.d8 0x18)) s (0x11ce7d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce7d 6 (.sib 10 (some 6) 0 (.d8 0x18)))
      [.gpr 10, .gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce7d 6 (.sib 10 (some 6) 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11ce7d 0x49 (by decide) 6 (.sib 10 (some 6) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x11ce82 [0x48, 0x89, 0xB4, 0x24, 0xB8, 0x03, 0x00, 0x00] (StorePre 0x11ce82 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3b8)) s (0x11ce82 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ce82 6 (.sib 4 none 0 (.d32 0x3b8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ce82 6 (.sib 4 none 0 (.d32 0x3b8))).toInstrSpec (mov_m64_r64_effect_step 0x11ce82 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x3b8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f77 : InstrSpec 0x11ce8a [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x11ce8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce8a 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce8a 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce8a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f78 : InstrSpec 0x11ce8f [0x49, 0x8B, 0x74, 0x32, 0x20] (LoadPre 0x11ce8f (fun s => AddrMode.addr (.sib 10 (some 6) 0 (.d8 0x20)) s (0x11ce8f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce8f 6 (.sib 10 (some 6) 0 (.d8 0x20)))
      [.gpr 10, .gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11ce8f 6 (.sib 10 (some 6) 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11ce8f 0x49 (by decide) 6 (.sib 10 (some 6) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f79 : InstrSpec 0x11ce94 [0x48, 0x89, 0xB4, 0x24, 0xC0, 0x03, 0x00, 0x00] (StorePre 0x11ce94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3c0)) s (0x11ce94 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ce94 6 (.sib 4 none 0 (.d32 0x3c0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ce94 6 (.sib 4 none 0 (.d32 0x3c0))).toInstrSpec (mov_m64_r64_effect_step 0x11ce94 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x3c0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f60 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 164), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce37) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.exec (n := 166) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 164), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce3a) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f62 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 164), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce44) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f63 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 169), (7, 142), (8, 164), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce47) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f64 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 169), (7, 171), (8, 164), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce4a) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f65 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 169), (7, 171), (8, 173), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce4d) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f66 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 169), (7, 171), (8, 175), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce51) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f67 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 169), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce54) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f68 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 179), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce59) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f69 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 181), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce5e) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.exec (n := 183) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 181), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce66) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f71 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 184), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce6b) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f72 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 186), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce70) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.exec (n := 188) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 186), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce78) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f74 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 189), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce7d) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f75 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 191), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce82) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.exec (n := 193) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 191), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce8a) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f77 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 194), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce8f) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f78 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 196), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce94) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.exec (n := 198) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 196), (7, 171), (8, 177), (9, 144), (10, 92), (12, 62), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce9c) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11ccfd_4 code

theorem rest_l11ccfd_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x11ccfd bytes_l11ccfd) [(0, 110), (1, 124), (2, 126), (3, 3), (4, 4), (5, 82), (6, 94), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      59 0x11cdd5 bytes_l11ccfd_2 b_l11ccfd_2 := by
  have f40 : InstrSpec 0x11cdd5 [0x48, 0xC1, 0xEA, 0x34] (fun s => s.RIP = 0x11cdd5) (shrR64Effect 0x11cdd5 4 2 52)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cdd5 4 2 52).toInstrSpec (shr_r64_imm8_effect_step 0x11cdd5 0x48 0xea 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x11cdd9 [0x48, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x11cdd9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cdd9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cdd9 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11cdd9 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11cdd9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x11cdde [0x49, 0x2B, 0x54, 0x3A, 0x38] (LoadPre 0x11cdde (fun s => AddrMode.addr (.sib 10 (some 7) 0 (.d8 0x38)) s (0x11cdde + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cdde 2 (.sib 10 (some 7) 0 (.d8 0x38)))
      [.gpr 2, .gpr 10, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11cdde 2 (.sib 10 (some 7) 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x11cdde 0x49 (by decide) 2 (.sib 10 (some 7) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x11cde3 [0x48, 0x01, 0xDA] (fun s => s.RIP = 0x11cde3) (addR64R64Effect 0x11cde3 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11cde3 2 3).toInstrSpec (add_r64_r64_effect_step 0x11cde3 0x48 0xda (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x11cde6 [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x11cde6) (movR64R64Effect 0x11cde6 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cde6 7 2).toInstrSpec (mov_r64_r64_effect_step 0x11cde6 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x11cde9 [0x48, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x11cde9) (shrR64Effect 0x11cde9 4 7 52)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cde9 4 7 52).toInstrSpec (shr_r64_imm8_effect_step 0x11cde9 0x48 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x11cded [0x4C, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x11cded (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cded + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cded 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x11cded 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11cded 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x11cdf2 [0x4B, 0x2B, 0x7C, 0x0A, 0x40] (LoadPre 0x11cdf2 (fun s => AddrMode.addr (.sib 10 (some 9) 0 (.d8 0x40)) s (0x11cdf2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cdf2 7 (.sib 10 (some 9) 0 (.d8 0x40)))
      [.gpr 7, .gpr 10, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11cdf2 7 (.sib 10 (some 9) 0 (.d8 0x40))).toInstrSpec (sub_r64_m64_effect_step 0x11cdf2 0x4b (by decide) 7 (.sib 10 (some 9) 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f48 : InstrSpec 0x11cdf7 [0x4C, 0x8D, 0x8C, 0x24, 0xF0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11cdf7) (leaR64Effect 0x11cdf7 9 (.sib 4 none 0 (.d32 0x3f0)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x11cdf7 9 (.sib 4 none 0 (.d32 0x3f0))).toInstrSpec (lea_r64_effect_step 0x11cdf7 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x3f0)) (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x11cdff [0x4D, 0x89, 0x41, 0x20] (StorePre 0x11cdff 4 (fun s => AddrMode.addr (.base 9 (.d8 0x20)) s (0x11cdff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11cdff 8 (.base 9 (.d8 0x20)))
      [.gpr 8, .gpr 9] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cdff 8 (.base 9 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11cdff 0x4d (by decide) 0 (.base 9 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x11ce03 [0x4C, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x11ce03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce03 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce03 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11ce03 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce03 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x11ce08 [0x4F, 0x8B, 0x44, 0x02, 0x68] (LoadPre 0x11ce08 (fun s => AddrMode.addr (.sib 10 (some 8) 0 (.d8 0x68)) s (0x11ce08 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce08 8 (.sib 10 (some 8) 0 (.d8 0x68)))
      [.gpr 10, .gpr 8] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11ce08 8 (.sib 10 (some 8) 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x11ce08 0x4f (by decide) 0 (.sib 10 (some 8) 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x11ce0d [0x4D, 0x89, 0x41, 0x18] (StorePre 0x11ce0d 4 (fun s => AddrMode.addr (.base 9 (.d8 0x18)) s (0x11ce0d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ce0d 8 (.base 9 (.d8 0x18)))
      [.gpr 8, .gpr 9] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ce0d 8 (.base 9 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11ce0d 0x4d (by decide) 0 (.base 9 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x11ce11 [0x4C, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x11ce11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce11 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11ce11 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce11 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x11ce16 [0x4F, 0x8B, 0x44, 0x02, 0x60] (LoadPre 0x11ce16 (fun s => AddrMode.addr (.sib 10 (some 8) 0 (.d8 0x60)) s (0x11ce16 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce16 8 (.sib 10 (some 8) 0 (.d8 0x60)))
      [.gpr 10, .gpr 8] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11ce16 8 (.sib 10 (some 8) 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x11ce16 0x4f (by decide) 0 (.sib 10 (some 8) 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x11ce1b [0x4D, 0x89, 0x41, 0x10] (StorePre 0x11ce1b 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x11ce1b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ce1b 8 (.base 9 (.d8 0x10)))
      [.gpr 8, .gpr 9] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ce1b 8 (.base 9 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11ce1b 0x4d (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x11ce1f [0x4C, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x11ce1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce1f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce1f 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11ce1f 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce1f 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f57 : InstrSpec 0x11ce24 [0x4F, 0x8B, 0x44, 0x02, 0x58] (LoadPre 0x11ce24 (fun s => AddrMode.addr (.sib 10 (some 8) 0 (.d8 0x58)) s (0x11ce24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce24 8 (.sib 10 (some 8) 0 (.d8 0x58)))
      [.gpr 10, .gpr 8] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11ce24 8 (.sib 10 (some 8) 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x11ce24 0x4f (by decide) 0 (.sib 10 (some 8) 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x11ce29 [0x4D, 0x89, 0x41, 0x08] (StorePre 0x11ce29 4 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x11ce29 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ce29 8 (.base 9 (.d8 0x8)))
      [.gpr 8, .gpr 9] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ce29 8 (.base 9 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11ce29 0x4d (by decide) 0 (.base 9 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x11ce2d [0x4C, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x11ce2d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce2d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce2d 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11ce2d 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ce2d 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 110), (1, 124), (2, 128), (3, 3), (4, 4), (5, 82), (6, 94), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdd9) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 110), (1, 124), (2, 128), (3, 3), (4, 4), (5, 82), (6, 94), (7, 130), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdde) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 110), (1, 124), (2, 132), (3, 3), (4, 4), (5, 82), (6, 94), (7, 130), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cde3) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 130), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cde6) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 136), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cde9) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 138), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cded) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 138), (8, 122), (9, 140), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdf2) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f47 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 122), (9, 140), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdf7) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f48 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 122), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdff) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 122), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce03) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f50 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 147), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce08) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f51 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 149), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce0d) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.exec (n := 151) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 149), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce11) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f53 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 152), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce16) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f54 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 154), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce1b) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 154), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce1f) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f56 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 157), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce24) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f57 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 159), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce29) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 159), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce2d) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f59 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 110), (1, 124), (2, 134), (3, 3), (4, 4), (5, 82), (6, 94), (7, 142), (8, 162), (9, 144), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ce32) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11ccfd_3 code

theorem rest_l11ccfd_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x11ccfd bytes_l11ccfd) [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]
      79 0x11cd6c bytes_l11ccfd_1 b_l11ccfd_1 := by
  have f20 : InstrSpec 0x11cd6c [0x48, 0xBE, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00] (fun s => s.RIP = 0x11cd6c) (movR64Imm64Effect 0x11cd6c 6 0x3fffffffffffc)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x11cd6c 6 0x3fffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x11cd6c 0x48 0xbe (by decide) (by decide) 0x3fffffffffffc) pre_rip
  have f21 : InstrSpec 0x11cd76 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x11cd76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cd76 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cd76 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11cd76 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11cd76 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x11cd7b [0x4C, 0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x11cd7b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11cd7b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd7b 10 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11cd7b 10 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x11cd7b 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x11cd83 [0x49, 0x2B, 0x74, 0x02, 0x48] (LoadPre 0x11cd83 (fun s => AddrMode.addr (.sib 10 (some 0) 0 (.d8 0x48)) s (0x11cd83 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cd83 6 (.sib 10 (some 0) 0 (.d8 0x48)))
      [.gpr 6, .gpr 10, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11cd83 6 (.sib 10 (some 0) 0 (.d8 0x48))).toInstrSpec (sub_r64_m64_effect_step 0x11cd83 0x49 (by decide) 6 (.sib 10 (some 0) 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x11cd88 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x11cd88) (movR64R64Effect 0x11cd88 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11cd88 0 6).toInstrSpec (mov_r64_r64_effect_step 0x11cd88 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x11cd8b [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x11cd8b) (shrR64Effect 0x11cd8b 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cd8b 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x11cd8b 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x11cd8f [0x49, 0xBD, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cd8f) (movR64Imm64Effect 0x11cd8f 13 0x1000003d1)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x11cd8f 13 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x11cd8f 0x49 0xbd (by decide) (by decide) 0x1000003d1) pre_rip
  have f27 : InstrSpec 0x11cd99 [0x49, 0x0F, 0xAF, 0xC5] (fun s => s.RIP = 0x11cd99) (imulR64R64Effect 0x11cd99 4 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x11cd99 4 0 13).toInstrSpec (imul_r64_r64_effect_step 0x11cd99 0x49 (by decide) 0xc5 (by decide)) pre_rip
  have f28 : InstrSpec 0x11cd9d [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x11cd9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cd9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cd9d 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cd9d 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11cd9d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x11cda2 [0x49, 0x2B, 0x44, 0x0A, 0x28] (LoadPre 0x11cda2 (fun s => AddrMode.addr (.sib 10 (some 1) 0 (.d8 0x28)) s (0x11cda2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cda2 0 (.sib 10 (some 1) 0 (.d8 0x28)))
      [.gpr 0, .gpr 10, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11cda2 0 (.sib 10 (some 1) 0 (.d8 0x28))).toInstrSpec (sub_r64_m64_effect_step 0x11cda2 0x49 (by decide) 0 (.sib 10 (some 1) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x11cda7 [0x49, 0xBE, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x11cda7) (movR64Imm64Effect 0x11cda7 14 0x3ffffbfffff0bc)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x11cda7 14 0x3ffffbfffff0bc).toInstrSpec (mov_r64_imm64_effect_step 0x11cda7 0x49 0xbe (by decide) (by decide) 0x3ffffbfffff0bc) pre_rip
  have f31 : InstrSpec 0x11cdb1 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x11cdb1) (addR64R64Effect 0x11cdb1 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11cdb1 0 14).toInstrSpec (add_r64_r64_effect_step 0x11cdb1 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x11cdb4 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x11cdb4) (movR64R64Effect 0x11cdb4 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11cdb4 1 0).toInstrSpec (mov_r64_r64_effect_step 0x11cdb4 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x11cdb7 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x11cdb7) (shrR64Effect 0x11cdb7 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11cdb7 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x11cdb7 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x11cdbb [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x11cdbb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cdbb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cdbb 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11cdbb 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11cdbb 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x11cdc0 [0x49, 0x2B, 0x4C, 0x12, 0x30] (LoadPre 0x11cdc0 (fun s => AddrMode.addr (.sib 10 (some 2) 0 (.d8 0x30)) s (0x11cdc0 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cdc0 1 (.sib 10 (some 2) 0 (.d8 0x30)))
      [.gpr 1, .gpr 10, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11cdc0 1 (.sib 10 (some 2) 0 (.d8 0x30))).toInstrSpec (sub_r64_m64_effect_step 0x11cdc0 0x49 (by decide) 1 (.sib 10 (some 2) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x11cdc5 [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x11cdc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cdc5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cdc5 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11cdc5 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11cdc5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x11cdca [0x4D, 0x8B, 0x44, 0x12, 0x70] (LoadPre 0x11cdca (fun s => AddrMode.addr (.sib 10 (some 2) 0 (.d8 0x70)) s (0x11cdca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cdca 8 (.sib 10 (some 2) 0 (.d8 0x70)))
      [.gpr 10, .gpr 2] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11cdca 8 (.sib 10 (some 2) 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x11cdca 0x4d (by decide) 0 (.sib 10 (some 2) 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x11cdcf [0x48, 0x01, 0xD9] (fun s => s.RIP = 0x11cdcf) (addR64R64Effect 0x11cdcf 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11cdcf 1 3).toInstrSpec (add_r64_r64_effect_step 0x11cdcf 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x11cdd2 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x11cdd2) (movR64R64Effect 0x11cdd2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11cdd2 2 1).toInstrSpec (mov_r64_r64_effect_step 0x11cdd2 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (6, 88), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd76) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (6, 88), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd7b) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 90), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (6, 88), (10, 92), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd83) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 90), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 68), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd88) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 96), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 68), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd8b) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 98), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 68), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd8f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f26 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 98), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd99) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 102), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd9d) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 102), (1, 104), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cda2) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 106), (1, 104), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cda7) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f30 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 106), (1, 104), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdb1) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 110), (1, 104), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdb4) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 110), (1, 112), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdb7) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 110), (1, 114), (2, 76), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdbb) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 110), (1, 114), (2, 116), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdc0) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 110), (1, 118), (2, 116), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdc5) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 110), (1, 118), (2, 120), (3, 3), (4, 4), (5, 82), (6, 94), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdca) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f37 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 110), (1, 118), (2, 120), (3, 3), (4, 4), (5, 82), (6, 94), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdcf) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 110), (1, 124), (2, 120), (3, 3), (4, 4), (5, 82), (6, 94), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdd2) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f39 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 110), (1, 124), (2, 126), (3, 3), (4, 4), (5, 82), (6, 94), (8, 122), (10, 92), (12, 62), (13, 100), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cdd5) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11ccfd_2 code

theorem rest_l11ccfd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11ccfd bytes_l11ccfd) (entryMap (live .l11ccfd))
      99 0x11ccfd bytes_l11ccfd b_l11ccfd := by
  have f0 : InstrSpec 0x11ccfd [0x0F, 0xB6, 0x44, 0x24, 0x48] (LoadPre 0x11ccfd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11ccfd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11ccfd 5 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11ccfd 5 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m8_effect_step 0x11ccfd 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11cd02 [0x88, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x11cd02 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cd02 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x11cd02 7 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11cd02 7 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m8_r8_effect_step 0x11cd02 0 (by decide) (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11cd09 [0x0F, 0xB6, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11cd09 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cd09 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11cd09 8 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11cd09 8 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (movzx_r32_m8_effect_step 0x11cd09 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11cd11 [0x48, 0x8B, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x11cd11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11cd11 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd11 1 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cd11 1 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_r64_m64_effect_step 0x11cd11 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11cd19 [0x84, 0xC0] (fun s => s.RIP = 0x11cd19) (testR8R8Effect 0x11cd19 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11cd19 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11cd19 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11cd1b [0x4C, 0x0F, 0x45, 0xE1] (fun s => s.RIP = 0x11cd1b) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd1b 4 12 1))
      [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 12, .rip] :=
    (cmovR64R64Effect_footprint 0x11cd1b 4 12 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11cd1b 5 0x4c (by decide) 0xe1 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x11cd1f [0x48, 0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x11cd1f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x11cd1f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd1f 1 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cd1f 1 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_r64_m64_effect_step 0x11cd1f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x11cd27 [0x84, 0xC0] (fun s => s.RIP = 0x11cd27) (testR8R8Effect 0x11cd27 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11cd27 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11cd27 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11cd29 [0x4C, 0x0F, 0x45, 0xE9] (fun s => s.RIP = 0x11cd29) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd29 4 13 1))
      [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 13, .rip] :=
    (cmovR64R64Effect_footprint 0x11cd29 4 13 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11cd29 5 0x4c (by decide) 0xe9 (by decide) c)) pre_rip
  have f9 : InstrSpec 0x11cd2d [0x48, 0x8B, 0x8C, 0x24, 0x38, 0x01, 0x00, 0x00] (LoadPre 0x11cd2d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x11cd2d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd2d 1 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cd2d 1 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_r64_m64_effect_step 0x11cd2d 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11cd35 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x11cd35) (movR64R64Effect 0x11cd35 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11cd35 2 14).toInstrSpec (mov_r64_r64_effect_step 0x11cd35 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11cd38 [0x84, 0xC0] (fun s => s.RIP = 0x11cd38) (testR8R8Effect 0x11cd38 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11cd38 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11cd38 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11cd3a [0x48, 0x0F, 0x45, 0xD1] (fun s => s.RIP = 0x11cd3a) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd3a 4 2 1))
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x11cd3a 4 2 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11cd3a 5 0x48 (by decide) 0xd1 (by decide) c)) pre_rip
  have f13 : InstrSpec 0x11cd3e [0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x11cd3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x11cd3e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd3e 1 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11cd3e 1 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x11cd3e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x11cd46 [0x84, 0xC0] (fun s => s.RIP = 0x11cd46) (testR8R8Effect 0x11cd46 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11cd46 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11cd46 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11cd48 [0x48, 0x0F, 0x45, 0xE9] (fun s => s.RIP = 0x11cd48) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd48 4 5 1))
      [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 5, .rip] :=
    (cmovR64R64Effect_footprint 0x11cd48 4 5 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11cd48 5 0x48 (by decide) 0xe9 (by decide) c)) pre_rip
  have f16 : InstrSpec 0x11cd4c [0x4C, 0x89, 0xA4, 0x24, 0x90, 0x02, 0x00, 0x00] (StorePre 0x11cd4c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x290)) s (0x11cd4c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cd4c 12 (.sib 4 none 0 (.d32 0x290)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cd4c 12 (.sib 4 none 0 (.d32 0x290))).toInstrSpec (mov_m64_r64_effect_step 0x11cd4c 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x290)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x11cd54 [0x4C, 0x89, 0xAC, 0x24, 0x98, 0x02, 0x00, 0x00] (StorePre 0x11cd54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x298)) s (0x11cd54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cd54 13 (.sib 4 none 0 (.d32 0x298)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cd54 13 (.sib 4 none 0 (.d32 0x298))).toInstrSpec (mov_m64_r64_effect_step 0x11cd54 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x298)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x11cd5c [0x48, 0x89, 0x94, 0x24, 0xA0, 0x02, 0x00, 0x00] (StorePre 0x11cd5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2a0)) s (0x11cd5c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cd5c 2 (.sib 4 none 0 (.d32 0x2a0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cd5c 2 (.sib 4 none 0 (.d32 0x2a0))).toInstrSpec (mov_m64_r64_effect_step 0x11cd5c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x2a0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11cd64 [0x48, 0x89, 0xAC, 0x24, 0xA8, 0x02, 0x00, 0x00] (StorePre 0x11cd64 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2a8)) s (0x11cd64 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cd64 5 (.sib 4 none 0 (.d32 0x2a8)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11cd64 5 (.sib 4 none 0 (.d32 0x2a8))).toInstrSpec (mov_m64_r64_effect_step 0x11cd64 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x2a8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd09) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd11) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd19) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd1b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (12, 62), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd1f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 56), (1, 64), (3, 3), (4, 4), (5, 5), (12, 62), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd27) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 56), (1, 64), (3, 3), (4, 4), (5, 5), (12, 62), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd29) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 56), (1, 64), (3, 3), (4, 4), (5, 5), (12, 62), (13, 68), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd2d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 56), (1, 70), (3, 3), (4, 4), (5, 5), (12, 62), (13, 68), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd35) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 56), (1, 70), (2, 72), (3, 3), (4, 4), (5, 5), (12, 62), (13, 68), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd38) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 56), (1, 70), (2, 72), (3, 3), (4, 4), (5, 5), (12, 62), (13, 68), (14, 14), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd3a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 56), (1, 70), (2, 76), (3, 3), (4, 4), (5, 5), (12, 62), (13, 68), (14, 14), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd3e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 5), (12, 62), (13, 68), (14, 14), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd46) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 5), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd48) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd4c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd54) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd5c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd64) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 56), (1, 78), (2, 76), (3, 3), (4, 4), (5, 82), (12, 62), (13, 68), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cd6c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11ccfd_1 code

theorem block_l11ccfd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11ccfd :=
  Rest.liftedBlock (rest_l11ccfd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11ccfd x hx)

theorem rest_l11cf0d [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11cf0d bytes_l11cf0d) (entryMap (live .l11cf0d))
      15 0x11cf0d bytes_l11cf0d b_l11cf0d := by
  have f0 : InstrSpec 0x11cf0d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cf0d) (movR32Imm32Effect 0x11cf0d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cf0d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cf0d 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11cf12 [0x48, 0x8D, 0xBC, 0x24, 0x50, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x11cf12) (leaR64Effect 0x11cf12 7 (.sib 4 none 0 (.d32 0x850)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11cf12 7 (.sib 4 none 0 (.d32 0x850))).toInstrSpec (lea_r64_effect_step 0x11cf12 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x850)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11cf1a [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11cf1a) (movR64R64Effect 0x11cf1a 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cf1a 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11cf1a 0x48 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11cf1d [0xF3, 0x48, 0xA5] (RepPre 0x11cf1d (RepMovsqPre 0x11cf1d)) (repMovsqEffect 0x11cf1d)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cf1d).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cf1d 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11cf20 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cf20) (movR32Imm32Effect 0x11cf20 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cf20 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cf20 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11cf25 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11cf25) (leaR64Effect 0x11cf25 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11cf25 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11cf25 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11cf2d [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11cf2d) (movR64R64Effect 0x11cf2d 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cf2d 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11cf2d 0x48 0xee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11cf30 [0xF3, 0x48, 0xA5] (RepPre 0x11cf30 (RepMovsqPre 0x11cf30)) (repMovsqEffect 0x11cf30)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cf30).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cf30 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x11cf33 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cf33) (movR32Imm32Effect 0x11cf33 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cf33 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cf33 0xb9 (by decide) 0xf) pre_rip
  have f9 : InstrSpec 0x11cf38 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11cf38) (movR64R64Effect 0x11cf38 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cf38 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11cf38 0x4c 0xff (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11cf3b [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11cf3b) (movR64R64Effect 0x11cf3b 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cf3b 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11cf3b 0x48 0xee (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11cf3e [0xF3, 0x48, 0xA5] (RepPre 0x11cf3e (RepMovsqPre 0x11cf3e)) (repMovsqEffect 0x11cf3e)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cf3e).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cf3e 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f12 : InstrSpec 0x11cf41 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11cf41) (movR64R64Effect 0x11cf41 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cf41 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11cf41 0x4c 0xff (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11cf44 [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11cf44) (leaR64Effect 0x11cf44 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11cf44 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11cf44 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11cf4c [0xE8, 0xBF, 0xD4, 0xFE, 0xFF] (PushPre 0x11cf4c 5) (callEffect (fun _ => 0x10a410) 0x11cf51)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11cf4c 0x10a410 0x11cf51).toInstrSpec (call_rel32_effect_step 0x11cf4c 0xfffed4bf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf12) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf1a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf1d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf20) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf25) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf2d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf30) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf33) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf38) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (3, 3), (4, 4), (5, 5), (7, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf3b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 67), (3, 3), (4, 4), (5, 5), (6, 71), (7, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf3e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf41) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf44) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 76), (7, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf4c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(3, 3), (4, 78), (5, 5), (6, 76), (7, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l11cf0d [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11cf0d :=
  Rest.liftedBlock (rest_l11cf0d hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11cf0d x hx)

theorem rest_l11cf51_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x11cf51 bytes_l11cf51) [(0, 64), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x11cfa9 bytes_l11cf51_1 b_l11cf51_1 := by
  have f20 : InstrSpec 0x11cfa9 [0xE8, 0x62, 0xD4, 0xFE, 0xFF] (PushPre 0x11cfa9 5) (callEffect (fun _ => 0x10a410) 0x11cfae)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11cfa9 0x10a410 0x11cfae).toInstrSpec (call_rel32_effect_step 0x11cfa9 0xfffed462 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 64), (3, 3), (4, 89), (5, 5), (6, 87), (7, 85), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f20 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 91) (by decide) (by decide) rfl rfl

theorem rest_l11cf51 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11cf51 bytes_l11cf51) (entryMap (live .l11cf51))
      21 0x11cf51 bytes_l11cf51 b_l11cf51 := by
  have f0 : InstrSpec 0x11cf51 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cf51) (movR32Imm32Effect 0x11cf51 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cf51 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cf51 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11cf56 [0x4C, 0x8D, 0xAC, 0x24, 0x18, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11cf56) (leaR64Effect 0x11cf56 13 (.sib 4 none 0 (.d32 0x418)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x11cf56 13 (.sib 4 none 0 (.d32 0x418))).toInstrSpec (lea_r64_effect_step 0x11cf56 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x418)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11cf5e [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11cf5e) (movR64R64Effect 0x11cf5e 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cf5e 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11cf5e 0x4c 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11cf61 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11cf61) (movR64R64Effect 0x11cf61 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cf61 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11cf61 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11cf64 [0xF3, 0x48, 0xA5] (RepPre 0x11cf64 (RepMovsqPre 0x11cf64)) (repMovsqEffect 0x11cf64)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cf64).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cf64 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x11cf67 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cf67) (movR32Imm32Effect 0x11cf67 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cf67 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cf67 0xb9 (by decide) 0xf) pre_rip
  have f6 : InstrSpec 0x11cf6c [0x48, 0x8D, 0x84, 0x24, 0xC8, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x11cf6c) (leaR64Effect 0x11cf6c 0 (.sib 4 none 0 (.d32 0x8c8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11cf6c 0 (.sib 4 none 0 (.d32 0x8c8))).toInstrSpec (lea_r64_effect_step 0x11cf6c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x8c8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11cf74 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11cf74) (movR64R64Effect 0x11cf74 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cf74 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11cf74 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11cf77 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11cf77) (movR64R64Effect 0x11cf77 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cf77 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11cf77 0x4c 0xee (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11cf7a [0xF3, 0x48, 0xA5] (RepPre 0x11cf7a (RepMovsqPre 0x11cf7a)) (repMovsqEffect 0x11cf7a)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cf7a).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cf7a 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f10 : InstrSpec 0x11cf7d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cf7d) (movR32Imm32Effect 0x11cf7d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cf7d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cf7d 0xb9 (by decide) 0xf) pre_rip
  have f11 : InstrSpec 0x11cf82 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11cf82) (leaR64Effect 0x11cf82 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11cf82 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11cf82 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11cf8a [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11cf8a) (movR64R64Effect 0x11cf8a 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cf8a 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11cf8a 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11cf8d [0xF3, 0x48, 0xA5] (RepPre 0x11cf8d (RepMovsqPre 0x11cf8d)) (repMovsqEffect 0x11cf8d)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cf8d).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cf8d 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f14 : InstrSpec 0x11cf90 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cf90) (movR32Imm32Effect 0x11cf90 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cf90 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cf90 0xb9 (by decide) 0xf) pre_rip
  have f15 : InstrSpec 0x11cf95 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11cf95) (movR64R64Effect 0x11cf95 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cf95 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11cf95 0x4c 0xff (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11cf98 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11cf98) (movR64R64Effect 0x11cf98 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cf98 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11cf98 0x48 0xee (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11cf9b [0xF3, 0x48, 0xA5] (RepPre 0x11cf9b (RepMovsqPre 0x11cf9b)) (repMovsqEffect 0x11cf9b)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cf9b).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cf9b 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f18 : InstrSpec 0x11cf9e [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11cf9e) (movR64R64Effect 0x11cf9e 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cf9e 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11cf9e 0x4c 0xff (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11cfa1 [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11cfa1) (leaR64Effect 0x11cfa1 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11cfa1 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11cfa1 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf56) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf5e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf61) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf64) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf67) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf6c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf74) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 62), (3, 3), (4, 4), (5, 5), (7, 66), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf77) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 62), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf7a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf7d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf82) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 71), (3, 3), (4, 4), (5, 5), (7, 73), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf8a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 64), (1, 71), (3, 3), (4, 4), (5, 5), (6, 75), (7, 73), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf8d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf90) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 64), (1, 78), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf95) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 64), (1, 78), (3, 3), (4, 4), (5, 5), (7, 80), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf98) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 64), (1, 78), (3, 3), (4, 4), (5, 5), (6, 82), (7, 80), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf9b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cf9e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (7, 85), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfa1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (6, 87), (7, 85), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfa9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11cf51_1 code

theorem block_l11cf51 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11cf51 :=
  Rest.liftedBlock (rest_l11cf51 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11cf51 x hx)

theorem rest_l11cfae [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11cfae bytes_l11cfae) (entryMap (live .l11cfae))
      20 0x11cfae bytes_l11cfae b_l11cfae := by
  have f0 : InstrSpec 0x11cfae [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cfae) (movR32Imm32Effect 0x11cfae 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cfae 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cfae 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11cfb3 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11cfb3) (movR64R64Effect 0x11cfb3 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cfb3 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11cfb3 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11cfb6 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11cfb6) (movR64R64Effect 0x11cfb6 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cfb6 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11cfb6 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11cfb9 [0xF3, 0x48, 0xA5] (RepPre 0x11cfb9 (RepMovsqPre 0x11cfb9)) (repMovsqEffect 0x11cfb9)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cfb9).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cfb9 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11cfbc [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cfbc) (movR32Imm32Effect 0x11cfbc 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cfbc 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cfbc 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11cfc1 [0x48, 0x8D, 0x84, 0x24, 0x40, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x11cfc1) (leaR64Effect 0x11cfc1 0 (.sib 4 none 0 (.d32 0x940)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11cfc1 0 (.sib 4 none 0 (.d32 0x940))).toInstrSpec (lea_r64_effect_step 0x11cfc1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x940)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11cfc9 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11cfc9) (movR64R64Effect 0x11cfc9 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cfc9 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11cfc9 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11cfcc [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11cfcc) (movR64R64Effect 0x11cfcc 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cfcc 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11cfcc 0x4c 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11cfcf [0xF3, 0x48, 0xA5] (RepPre 0x11cfcf (RepMovsqPre 0x11cfcf)) (repMovsqEffect 0x11cfcf)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cfcf).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cfcf 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11cfd2 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cfd2) (movR32Imm32Effect 0x11cfd2 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cfd2 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cfd2 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11cfd7 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11cfd7) (leaR64Effect 0x11cfd7 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11cfd7 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11cfd7 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11cfdf [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11cfdf) (movR64R64Effect 0x11cfdf 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cfdf 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11cfdf 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11cfe2 [0xF3, 0x48, 0xA5] (RepPre 0x11cfe2 (RepMovsqPre 0x11cfe2)) (repMovsqEffect 0x11cfe2)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cfe2).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cfe2 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11cfe5 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11cfe5) (movR32Imm32Effect 0x11cfe5 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11cfe5 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11cfe5 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11cfea [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11cfea) (movR64R64Effect 0x11cfea 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cfea 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11cfea 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11cfed [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11cfed) (movR64R64Effect 0x11cfed 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11cfed 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11cfed 0x48 0xee (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11cff0 [0xF3, 0x48, 0xA5] (RepPre 0x11cff0 (RepMovsqPre 0x11cff0)) (repMovsqEffect 0x11cff0)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11cff0).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11cff0 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11cff3 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11cff3) (movR64R64Effect 0x11cff3 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11cff3 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11cff3 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11cff6 [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11cff6) (leaR64Effect 0x11cff6 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11cff6 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11cff6 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11cffe [0xE8, 0x0D, 0xD4, 0xFE, 0xFF] (PushPre 0x11cffe 5) (callEffect (fun _ => 0x10a410) 0x11d003)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11cffe 0x10a410 0x11d003).toInstrSpec (call_rel32_effect_step 0x11cffe 0xfffed40d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfb3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfb6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfb9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfbc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfc1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfc9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfcc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfcf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfd2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfd7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfdf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfe2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfe5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfea) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cfed) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cff0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cff3) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cff6) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11cffe) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11cfae [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11cfae :=
  Rest.liftedBlock (rest_l11cfae hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11cfae x hx)

theorem rest_l11d003 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d003 bytes_l11d003) (entryMap (live .l11d003))
      20 0x11d003 bytes_l11d003 b_l11d003 := by
  have f0 : InstrSpec 0x11d003 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d003) (movR32Imm32Effect 0x11d003 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d003 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d003 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d008 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11d008) (movR64R64Effect 0x11d008 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d008 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11d008 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d00b [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d00b) (movR64R64Effect 0x11d00b 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d00b 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d00b 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d00e [0xF3, 0x48, 0xA5] (RepPre 0x11d00e (RepMovsqPre 0x11d00e)) (repMovsqEffect 0x11d00e)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d00e).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d00e 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d011 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d011) (movR32Imm32Effect 0x11d011 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d011 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d011 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d016 [0x48, 0x8D, 0x84, 0x24, 0xB8, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x11d016) (leaR64Effect 0x11d016 0 (.sib 4 none 0 (.d32 0x9b8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d016 0 (.sib 4 none 0 (.d32 0x9b8))).toInstrSpec (lea_r64_effect_step 0x11d016 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x9b8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d01e [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d01e) (movR64R64Effect 0x11d01e 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d01e 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d01e 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d021 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11d021) (movR64R64Effect 0x11d021 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d021 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11d021 0x4c 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d024 [0xF3, 0x48, 0xA5] (RepPre 0x11d024 (RepMovsqPre 0x11d024)) (repMovsqEffect 0x11d024)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d024).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d024 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d027 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d027) (movR32Imm32Effect 0x11d027 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d027 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d027 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d02c [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d02c) (leaR64Effect 0x11d02c 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d02c 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d02c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d034 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d034) (movR64R64Effect 0x11d034 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d034 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d034 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d037 [0xF3, 0x48, 0xA5] (RepPre 0x11d037 (RepMovsqPre 0x11d037)) (repMovsqEffect 0x11d037)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d037).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d037 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d03a [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d03a) (movR32Imm32Effect 0x11d03a 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d03a 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d03a 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d03f [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d03f) (movR64R64Effect 0x11d03f 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d03f 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d03f 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d042 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d042) (movR64R64Effect 0x11d042 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d042 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d042 0x48 0xee (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d045 [0xF3, 0x48, 0xA5] (RepPre 0x11d045 (RepMovsqPre 0x11d045)) (repMovsqEffect 0x11d045)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d045).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d045 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d048 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d048) (movR64R64Effect 0x11d048 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d048 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d048 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d04b [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d04b) (leaR64Effect 0x11d04b 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d04b 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d04b 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d053 [0xE8, 0xB8, 0xD3, 0xFE, 0xFF] (PushPre 0x11d053 5) (callEffect (fun _ => 0x10a410) 0x11d058)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d053 0x10a410 0x11d058).toInstrSpec (call_rel32_effect_step 0x11d053 0xfffed3b8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d008) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d00b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d00e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d011) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d016) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d01e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d021) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d024) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d027) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d02c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d034) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d037) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d03a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d03f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d042) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d045) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d048) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d04b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d053) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d003 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d003 :=
  Rest.liftedBlock (rest_l11d003 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d003 x hx)

theorem rest_l11d058 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d058 bytes_l11d058) (entryMap (live .l11d058))
      20 0x11d058 bytes_l11d058 b_l11d058 := by
  have f0 : InstrSpec 0x11d058 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d058) (movR32Imm32Effect 0x11d058 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d058 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d058 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d05d [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11d05d) (movR64R64Effect 0x11d05d 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d05d 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11d05d 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d060 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d060) (movR64R64Effect 0x11d060 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d060 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d060 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d063 [0xF3, 0x48, 0xA5] (RepPre 0x11d063 (RepMovsqPre 0x11d063)) (repMovsqEffect 0x11d063)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d063).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d063 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d066 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d066) (movR32Imm32Effect 0x11d066 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d066 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d066 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d06b [0x48, 0x8D, 0x84, 0x24, 0x30, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x11d06b) (leaR64Effect 0x11d06b 0 (.sib 4 none 0 (.d32 0xa30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d06b 0 (.sib 4 none 0 (.d32 0xa30))).toInstrSpec (lea_r64_effect_step 0x11d06b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa30)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d073 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d073) (movR64R64Effect 0x11d073 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d073 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d073 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d076 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11d076) (movR64R64Effect 0x11d076 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d076 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11d076 0x4c 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d079 [0xF3, 0x48, 0xA5] (RepPre 0x11d079 (RepMovsqPre 0x11d079)) (repMovsqEffect 0x11d079)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d079).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d079 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d07c [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d07c) (movR32Imm32Effect 0x11d07c 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d07c 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d07c 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d081 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d081) (leaR64Effect 0x11d081 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d081 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d081 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d089 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d089) (movR64R64Effect 0x11d089 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d089 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d089 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d08c [0xF3, 0x48, 0xA5] (RepPre 0x11d08c (RepMovsqPre 0x11d08c)) (repMovsqEffect 0x11d08c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d08c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d08c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d08f [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d08f) (movR32Imm32Effect 0x11d08f 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d08f 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d08f 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d094 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d094) (movR64R64Effect 0x11d094 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d094 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d094 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d097 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d097) (movR64R64Effect 0x11d097 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d097 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d097 0x48 0xee (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d09a [0xF3, 0x48, 0xA5] (RepPre 0x11d09a (RepMovsqPre 0x11d09a)) (repMovsqEffect 0x11d09a)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d09a).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d09a 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d09d [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d09d) (movR64R64Effect 0x11d09d 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d09d 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d09d 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d0a0 [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d0a0) (leaR64Effect 0x11d0a0 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d0a0 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d0a0 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d0a8 [0xE8, 0x63, 0xD3, 0xFE, 0xFF] (PushPre 0x11d0a8 5) (callEffect (fun _ => 0x10a410) 0x11d0ad)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d0a8 0x10a410 0x11d0ad).toInstrSpec (call_rel32_effect_step 0x11d0a8 0xfffed363 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d05d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d060) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d063) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d066) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d06b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d073) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d076) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d079) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d07c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d081) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d089) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d08c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d08f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d094) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d097) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d09a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d09d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0a0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0a8) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d058 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d058 :=
  Rest.liftedBlock (rest_l11d058 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d058 x hx)

theorem rest_l11d0ad [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d0ad bytes_l11d0ad) (entryMap (live .l11d0ad))
      20 0x11d0ad bytes_l11d0ad b_l11d0ad := by
  have f0 : InstrSpec 0x11d0ad [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d0ad) (movR32Imm32Effect 0x11d0ad 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d0ad 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d0ad 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d0b2 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11d0b2) (movR64R64Effect 0x11d0b2 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d0b2 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11d0b2 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d0b5 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d0b5) (movR64R64Effect 0x11d0b5 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d0b5 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d0b5 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d0b8 [0xF3, 0x48, 0xA5] (RepPre 0x11d0b8 (RepMovsqPre 0x11d0b8)) (repMovsqEffect 0x11d0b8)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d0b8).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d0b8 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d0bb [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d0bb) (movR32Imm32Effect 0x11d0bb 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d0bb 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d0bb 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d0c0 [0x48, 0x8D, 0x84, 0x24, 0xA8, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x11d0c0) (leaR64Effect 0x11d0c0 0 (.sib 4 none 0 (.d32 0xaa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d0c0 0 (.sib 4 none 0 (.d32 0xaa8))).toInstrSpec (lea_r64_effect_step 0x11d0c0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xaa8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d0c8 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d0c8) (movR64R64Effect 0x11d0c8 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d0c8 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d0c8 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d0cb [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11d0cb) (movR64R64Effect 0x11d0cb 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d0cb 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11d0cb 0x4c 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d0ce [0xF3, 0x48, 0xA5] (RepPre 0x11d0ce (RepMovsqPre 0x11d0ce)) (repMovsqEffect 0x11d0ce)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d0ce).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d0ce 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d0d1 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d0d1) (movR32Imm32Effect 0x11d0d1 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d0d1 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d0d1 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d0d6 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d0d6) (leaR64Effect 0x11d0d6 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d0d6 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d0d6 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d0de [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d0de) (movR64R64Effect 0x11d0de 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d0de 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d0de 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d0e1 [0xF3, 0x48, 0xA5] (RepPre 0x11d0e1 (RepMovsqPre 0x11d0e1)) (repMovsqEffect 0x11d0e1)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d0e1).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d0e1 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d0e4 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d0e4) (movR32Imm32Effect 0x11d0e4 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d0e4 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d0e4 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d0e9 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d0e9) (movR64R64Effect 0x11d0e9 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d0e9 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d0e9 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d0ec [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d0ec) (movR64R64Effect 0x11d0ec 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d0ec 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d0ec 0x48 0xee (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d0ef [0xF3, 0x48, 0xA5] (RepPre 0x11d0ef (RepMovsqPre 0x11d0ef)) (repMovsqEffect 0x11d0ef)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d0ef).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d0ef 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d0f2 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d0f2) (movR64R64Effect 0x11d0f2 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d0f2 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d0f2 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d0f5 [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d0f5) (leaR64Effect 0x11d0f5 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d0f5 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d0f5 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d0fd [0xE8, 0x0E, 0xD3, 0xFE, 0xFF] (PushPre 0x11d0fd 5) (callEffect (fun _ => 0x10a410) 0x11d102)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d0fd 0x10a410 0x11d102).toInstrSpec (call_rel32_effect_step 0x11d0fd 0xfffed30e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0b2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0b8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0bb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0c8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0cb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0ce) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0d1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0d6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0de) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0e1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0e4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0e9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0ec) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0ef) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0f2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0f5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d0fd) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d0ad [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d0ad :=
  Rest.liftedBlock (rest_l11d0ad hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d0ad x hx)

theorem rest_l11d102 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d102 bytes_l11d102) (entryMap (live .l11d102))
      20 0x11d102 bytes_l11d102 b_l11d102 := by
  have f0 : InstrSpec 0x11d102 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d102) (movR32Imm32Effect 0x11d102 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d102 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d102 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d107 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11d107) (movR64R64Effect 0x11d107 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d107 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11d107 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d10a [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d10a) (movR64R64Effect 0x11d10a 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d10a 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d10a 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d10d [0xF3, 0x48, 0xA5] (RepPre 0x11d10d (RepMovsqPre 0x11d10d)) (repMovsqEffect 0x11d10d)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d10d).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d10d 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d110 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d110) (movR32Imm32Effect 0x11d110 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d110 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d110 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d115 [0x48, 0x8D, 0x84, 0x24, 0x20, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x11d115) (leaR64Effect 0x11d115 0 (.sib 4 none 0 (.d32 0xb20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d115 0 (.sib 4 none 0 (.d32 0xb20))).toInstrSpec (lea_r64_effect_step 0x11d115 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb20)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d11d [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d11d) (movR64R64Effect 0x11d11d 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d11d 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d11d 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d120 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11d120) (movR64R64Effect 0x11d120 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d120 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11d120 0x4c 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d123 [0xF3, 0x48, 0xA5] (RepPre 0x11d123 (RepMovsqPre 0x11d123)) (repMovsqEffect 0x11d123)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d123).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d123 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d126 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d126) (movR32Imm32Effect 0x11d126 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d126 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d126 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d12b [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d12b) (leaR64Effect 0x11d12b 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d12b 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d12b 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d133 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d133) (movR64R64Effect 0x11d133 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d133 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d133 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d136 [0xF3, 0x48, 0xA5] (RepPre 0x11d136 (RepMovsqPre 0x11d136)) (repMovsqEffect 0x11d136)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d136).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d136 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d139 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d139) (movR32Imm32Effect 0x11d139 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d139 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d139 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d13e [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d13e) (movR64R64Effect 0x11d13e 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d13e 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d13e 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d141 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d141) (movR64R64Effect 0x11d141 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d141 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d141 0x48 0xee (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d144 [0xF3, 0x48, 0xA5] (RepPre 0x11d144 (RepMovsqPre 0x11d144)) (repMovsqEffect 0x11d144)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d144).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d144 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d147 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d147) (movR64R64Effect 0x11d147 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d147 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d147 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d14a [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d14a) (leaR64Effect 0x11d14a 6 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d14a 6 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d14a 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d152 [0xE8, 0xB9, 0xD2, 0xFE, 0xFF] (PushPre 0x11d152 5) (callEffect (fun _ => 0x10a410) 0x11d157)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d152 0x10a410 0x11d157).toInstrSpec (call_rel32_effect_step 0x11d152 0xfffed2b9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d107) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d10a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d10d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d110) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d115) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d11d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d120) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d123) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d126) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d12b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d133) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d136) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d139) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d13e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d141) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d144) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d147) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d14a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d152) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d102 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d102 :=
  Rest.liftedBlock (rest_l11d102 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d102 x hx)

theorem rest_l11d157_3 [Bindings] (code : CodeMap) :
    Rest (n := 160) code lifted (codeRange 0x11d157 bytes_l11d157) [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x11d293 bytes_l11d157_3 b_l11d157_3 := by
  have f60 : InstrSpec 0x11d293 [0x48, 0x89, 0x94, 0x24, 0x58, 0x03, 0x00, 0x00] (StorePre 0x11d293 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x358)) s (0x11d293 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d293 2 (.sib 4 none 0 (.d32 0x358)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d293 2 (.sib 4 none 0 (.d32 0x358))).toInstrSpec (mov_m64_r64_effect_step 0x11d293 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x358)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x11d29b [0x4C, 0x21, 0xE6] (fun s => s.RIP = 0x11d29b) (andR64R64Effect 0x11d29b 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11d29b 6 12).toInstrSpec (and_r64_r64_effect_step 0x11d29b 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x11d29e [0x48, 0x89, 0xB4, 0x24, 0x60, 0x03, 0x00, 0x00] (StorePre 0x11d29e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x360)) s (0x11d29e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d29e 6 (.sib 4 none 0 (.d32 0x360)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d29e 6 (.sib 4 none 0 (.d32 0x360))).toInstrSpec (mov_m64_r64_effect_step 0x11d29e 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x360)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f63 : InstrSpec 0x11d2a6 [0x4C, 0x21, 0xE7] (fun s => s.RIP = 0x11d2a6) (andR64R64Effect 0x11d2a6 7 12)
      [.gpr 7, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11d2a6 7 12).toInstrSpec (and_r64_r64_effect_step 0x11d2a6 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x11d2a9 [0x4C, 0x8D, 0xA4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d2a9) (leaR64Effect 0x11d2a9 12 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x11d2a9 12 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d2a9 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x11d2b1 [0x48, 0x89, 0xBC, 0x24, 0x68, 0x03, 0x00, 0x00] (StorePre 0x11d2b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x368)) s (0x11d2b1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d2b1 7 (.sib 4 none 0 (.d32 0x368)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d2b1 7 (.sib 4 none 0 (.d32 0x368))).toInstrSpec (mov_m64_r64_effect_step 0x11d2b1 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x368)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x11d2b9 [0x4C, 0x89, 0x84, 0x24, 0x70, 0x03, 0x00, 0x00] (StorePre 0x11d2b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x370)) s (0x11d2b9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d2b9 8 (.sib 4 none 0 (.d32 0x370)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d2b9 8 (.sib 4 none 0 (.d32 0x370))).toInstrSpec (mov_m64_r64_effect_step 0x11d2b9 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x370)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x11d2c1 [0x0F, 0xB6, 0x4C, 0x24, 0x48] (LoadPre 0x11d2c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11d2c1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11d2c1 5 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x11d2c1 5 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m8_effect_step 0x11d2c1 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f68 : InstrSpec 0x11d2c6 [0x48, 0x8D, 0x9C, 0x24, 0x10, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x11d2c6) (leaR64Effect 0x11d2c6 3 (.sib 4 none 0 (.d32 0xc10)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x11d2c6 3 (.sib 4 none 0 (.d32 0xc10))).toInstrSpec (lea_r64_effect_step 0x11d2c6 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xc10)) (by decide) (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x11d2ce [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x11d2ce) (movR64R64Effect 0x11d2ce 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d2ce 7 3).toInstrSpec (mov_r64_r64_effect_step 0x11d2ce 0x48 0xdf (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x11d2d1 [0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x11d2d1) (leaR64Effect 0x11d2d1 6 (.sib 4 none 0 (.d32 0x2b0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d2d1 6 (.sib 4 none 0 (.d32 0x2b0))).toInstrSpec (lea_r64_effect_step 0x11d2d1 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x2b0)) (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x11d2d9 [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x11d2d9) (movR64R64Effect 0x11d2d9 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11d2d9 2 5).toInstrSpec (mov_r64_r64_effect_step 0x11d2d9 0x48 0xea (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x11d2dc [0xE8, 0xDF, 0x29, 0xFF, 0xFF] (PushPre 0x11d2dc 5) (callEffect (fun _ => 0x10fcc0) 0x11d2e1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d2dc 0x10fcc0 0x11d2e1).toInstrSpec (call_rel32_effect_step 0x11d2dc 0xffff29df (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 160) (RestInside.exec (n := 160) (ρ' := [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d29b) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f61 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 161), (7, 147), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d29e) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.exec (n := 163) (ρ' := [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 161), (7, 147), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2a6) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f63 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 161), (7, 164), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2a9) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f64 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 161), (7, 164), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2b1) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.exec (n := 168) (ρ' := [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 161), (7, 164), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2b9) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 169) (RestInside.exec (n := 169) (ρ' := [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 161), (7, 164), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2c1) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 155), (1, 170), (2, 158), (3, 3), (4, 4), (5, 5), (6, 161), (7, 164), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2c6) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f68 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 155), (1, 170), (2, 158), (3, 172), (4, 4), (5, 5), (6, 161), (7, 164), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2ce) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f69 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 155), (1, 170), (2, 158), (3, 172), (4, 4), (5, 5), (6, 161), (7, 174), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2d1) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f70 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 155), (1, 170), (2, 158), (3, 172), (4, 4), (5, 5), (6, 176), (7, 174), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2d9) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f71 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 155), (1, 170), (2, 178), (3, 172), (4, 4), (5, 5), (6, 176), (7, 174), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2dc) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f72 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 155), (1, 170), (2, 178), (3, 172), (4, 180), (5, 5), (6, 176), (7, 174), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f72 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 182) (by decide) (by decide) rfl rfl

theorem rest_l11d157_2 [Bindings] (code : CodeMap) :
    Rest (n := 126) code lifted (codeRange 0x11d157 bytes_l11d157) [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x11d23f bytes_l11d157_2 b_l11d157_2 := by
  have f40 : InstrSpec 0x11d23f [0x4C, 0x8D, 0x8C, 0x24, 0x00, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11d23f) (leaR64Effect 0x11d23f 9 (.sib 4 none 0 (.d32 0x300)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x11d23f 9 (.sib 4 none 0 (.d32 0x300))).toInstrSpec (lea_r64_effect_step 0x11d23f 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x300)) (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x11d247 [0x4D, 0x8B, 0x41, 0x20] (LoadPre 0x11d247 (fun s => AddrMode.addr (.base 9 (.d8 0x20)) s (0x11d247 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11d247 8 (.base 9 (.d8 0x20)))
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11d247 8 (.base 9 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11d247 0x4d (by decide) 0 (.base 9 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x11d24b [0x4C, 0x8D, 0x94, 0x24, 0x78, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11d24b) (leaR64Effect 0x11d24b 10 (.sib 4 none 0 (.d32 0x378)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x11d24b 10 (.sib 4 none 0 (.d32 0x378))).toInstrSpec (lea_r64_effect_step 0x11d24b 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x378)) (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x11d253 [0x4D, 0x89, 0x42, 0x20] (StorePre 0x11d253 4 (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x11d253 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d253 8 (.base 10 (.d8 0x20)))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d253 8 (.base 10 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11d253 0x4d (by decide) 0 (.base 10 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x11d257 [0x4D, 0x8B, 0x41, 0x18] (LoadPre 0x11d257 (fun s => AddrMode.addr (.base 9 (.d8 0x18)) s (0x11d257 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11d257 8 (.base 9 (.d8 0x18)))
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11d257 8 (.base 9 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11d257 0x4d (by decide) 0 (.base 9 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x11d25b [0x4D, 0x89, 0x42, 0x18] (StorePre 0x11d25b 4 (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x11d25b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d25b 8 (.base 10 (.d8 0x18)))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d25b 8 (.base 10 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11d25b 0x4d (by decide) 0 (.base 10 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x11d25f [0x4D, 0x8B, 0x41, 0x10] (LoadPre 0x11d25f (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x11d25f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11d25f 8 (.base 9 (.d8 0x10)))
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11d25f 8 (.base 9 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11d25f 0x4d (by decide) 0 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x11d263 [0x4D, 0x89, 0x42, 0x10] (StorePre 0x11d263 4 (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x11d263 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d263 8 (.base 10 (.d8 0x10)))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d263 8 (.base 10 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11d263 0x4d (by decide) 0 (.base 10 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x11d267 [0x4D, 0x8B, 0x41, 0x08] (LoadPre 0x11d267 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x11d267 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11d267 8 (.base 9 (.d8 0x8)))
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11d267 8 (.base 9 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11d267 0x4d (by decide) 0 (.base 9 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x11d26b [0x4D, 0x89, 0x42, 0x08] (StorePre 0x11d26b 4 (fun s => AddrMode.addr (.base 10 (.d8 0x8)) s (0x11d26b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d26b 8 (.base 10 (.d8 0x8)))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d26b 8 (.base 10 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11d26b 0x4d (by decide) 0 (.base 10 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x11d26f [0x4D, 0x8B, 0x01] (LoadPre 0x11d26f (fun s => AddrMode.addr (.base 9 .none) s (0x11d26f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11d26f 8 (.base 9 .none))
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11d26f 8 (.base 9 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11d26f 0x4d (by decide) 0 (.base 9 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x11d272 [0x4D, 0x89, 0x02] (StorePre 0x11d272 3 (fun s => AddrMode.addr (.base 10 .none) s (0x11d272 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11d272 8 (.base 10 .none))
      [.gpr 8, .gpr 10] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d272 8 (.base 10 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11d272 0x4d (by decide) 0 (.base 10 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x11d275 [0x4C, 0x21, 0xD9] (fun s => s.RIP = 0x11d275) (andR64R64Effect 0x11d275 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11d275 1 11).toInstrSpec (and_r64_r64_effect_step 0x11d275 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x11d278 [0x48, 0x01, 0xDF] (fun s => s.RIP = 0x11d278) (addR64R64Effect 0x11d278 7 3)
      [.gpr 7, .gpr 3] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11d278 7 3).toInstrSpec (add_r64_r64_effect_step 0x11d278 0x48 0xdf (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x11d27b [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x11d27b) (movR64R64Effect 0x11d27b 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11d27b 8 7).toInstrSpec (mov_r64_r64_effect_step 0x11d27b 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x11d27e [0x49, 0xC1, 0xE8, 0x34] (fun s => s.RIP = 0x11d27e) (shrR64Effect 0x11d27e 4 8 52)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x11d27e 4 8 52).toInstrSpec (shr_r64_imm8_effect_step 0x11d27e 0x49 0xe8 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x11d282 [0x49, 0x01, 0xC8] (fun s => s.RIP = 0x11d282) (addR64R64Effect 0x11d282 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11d282 8 1).toInstrSpec (add_r64_r64_effect_step 0x11d282 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x11d285 [0x4C, 0x21, 0xE0] (fun s => s.RIP = 0x11d285) (andR64R64Effect 0x11d285 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11d285 0 12).toInstrSpec (and_r64_r64_effect_step 0x11d285 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x11d288 [0x48, 0x89, 0x84, 0x24, 0x50, 0x03, 0x00, 0x00] (StorePre 0x11d288 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x350)) s (0x11d288 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d288 0 (.sib 4 none 0 (.d32 0x350)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d288 0 (.sib 4 none 0 (.d32 0x350))).toInstrSpec (mov_m64_r64_effect_step 0x11d288 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x350)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x11d290 [0x4C, 0x21, 0xE2] (fun s => s.RIP = 0x11d290) (andR64R64Effect 0x11d290 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11d290 2 12).toInstrSpec (and_r64_r64_effect_step 0x11d290 0x4c 0xe2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f40 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (9, 126), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d247) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f41 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 128), (9, 126), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d24b) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f42 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 128), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d253) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.exec (n := 132) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 128), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d257) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f44 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 133), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d25b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 133), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d25f) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f46 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 136), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d263) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 136), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d267) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f48 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 139), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d26b) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 139), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d26f) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f50 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 142), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d272) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 142), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d275) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f52 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 100), (1, 145), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (8, 142), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d278) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f53 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 100), (1, 145), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 142), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d27b) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f54 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 100), (1, 145), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 149), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d27e) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f55 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 100), (1, 145), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 151), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d282) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f56 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 100), (1, 145), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d285) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f57 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 155), (1, 145), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d288) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.exec (n := 157) (ρ' := [(0, 155), (1, 145), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d290) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f59 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 155), (1, 145), (2, 158), (3, 3), (4, 4), (5, 5), (6, 118), (7, 147), (8, 153), (9, 126), (10, 130), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d293) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11d157_3 code

theorem rest_l11d157_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x11d157 bytes_l11d157) [(0, 78), (1, 85), (2, 76), (3, 3), (4, 4), (5, 5), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      53 0x11d1d5 bytes_l11d157_1 b_l11d157_1 := by
  have f20 : InstrSpec 0x11d1d5 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11d1d5) (movR64R64Effect 0x11d1d5 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11d1d5 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11d1d5 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x11d1d8 [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x11d1d8) (shrR64Effect 0x11d1d8 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11d1d8 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x11d1d8 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11d1dc [0x48, 0xBE, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d1dc) (movR64Imm64Effect 0x11d1dc 6 0x1000003d1)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x11d1dc 6 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x11d1dc 0x48 0xbe (by decide) (by decide) 0x1000003d1) pre_rip
  have f23 : InstrSpec 0x11d1e6 [0x48, 0x0F, 0xAF, 0xC6] (fun s => s.RIP = 0x11d1e6) (imulR64R64Effect 0x11d1e6 4 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x11d1e6 4 0 6).toInstrSpec (imul_r64_r64_effect_step 0x11d1e6 0x48 (by decide) 0xc6 (by decide)) pre_rip
  have f24 : InstrSpec 0x11d1ea [0x48, 0x2B, 0x84, 0x24, 0xD8, 0x02, 0x00, 0x00] (LoadPre 0x11d1ea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2d8)) s (0x11d1ea + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d1ea 0 (.sib 4 none 0 (.d32 0x2d8)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11d1ea 0 (.sib 4 none 0 (.d32 0x2d8))).toInstrSpec (sub_r64_m64_effect_step 0x11d1ea 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x2d8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x11d1f2 [0x48, 0x89, 0x94, 0x24, 0x28, 0x03, 0x00, 0x00] (StorePre 0x11d1f2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x328)) s (0x11d1f2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d1f2 2 (.sib 4 none 0 (.d32 0x328)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d1f2 2 (.sib 4 none 0 (.d32 0x328))).toInstrSpec (mov_m64_r64_effect_step 0x11d1f2 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x328)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x11d1fa [0x48, 0xBA, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x11d1fa) (movR64Imm64Effect 0x11d1fa 2 0x3ffffbfffff0bc)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x11d1fa 2 0x3ffffbfffff0bc).toInstrSpec (mov_r64_imm64_effect_step 0x11d1fa 0x48 0xba (by decide) (by decide) 0x3ffffbfffff0bc) pre_rip
  have f27 : InstrSpec 0x11d204 [0x48, 0x01, 0xD0] (fun s => s.RIP = 0x11d204) (addR64R64Effect 0x11d204 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11d204 0 2).toInstrSpec (add_r64_r64_effect_step 0x11d204 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x11d207 [0x4C, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x11d207 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11d207 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11d207 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x11d207 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11d207 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x11d20c [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x11d20c) (movR64R64Effect 0x11d20c 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11d20c 2 0).toInstrSpec (mov_r64_r64_effect_step 0x11d20c 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x11d20f [0x48, 0xC1, 0xEA, 0x34] (fun s => s.RIP = 0x11d20f) (shrR64Effect 0x11d20f 4 2 52)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x11d20f 4 2 52).toInstrSpec (shr_r64_imm8_effect_step 0x11d20f 0x48 0xea 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x11d213 [0x48, 0x2B, 0x94, 0x24, 0xE0, 0x02, 0x00, 0x00] (LoadPre 0x11d213 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2e0)) s (0x11d213 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d213 2 (.sib 4 none 0 (.d32 0x2e0)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11d213 2 (.sib 4 none 0 (.d32 0x2e0))).toInstrSpec (sub_r64_m64_effect_step 0x11d213 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x2e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x11d21b [0x48, 0x01, 0xDA] (fun s => s.RIP = 0x11d21b) (addR64R64Effect 0x11d21b 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11d21b 2 3).toInstrSpec (add_r64_r64_effect_step 0x11d21b 0x48 0xda (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x11d21e [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x11d21e) (movR64R64Effect 0x11d21e 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d21e 6 2).toInstrSpec (mov_r64_r64_effect_step 0x11d21e 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x11d221 [0x48, 0xC1, 0xEE, 0x34] (fun s => s.RIP = 0x11d221) (shrR64Effect 0x11d221 4 6 52)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11d221 4 6 52).toInstrSpec (shr_r64_imm8_effect_step 0x11d221 0x48 0xee 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x11d225 [0x48, 0x2B, 0xB4, 0x24, 0xE8, 0x02, 0x00, 0x00] (LoadPre 0x11d225 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2e8)) s (0x11d225 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d225 6 (.sib 4 none 0 (.d32 0x2e8)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11d225 6 (.sib 4 none 0 (.d32 0x2e8))).toInstrSpec (sub_r64_m64_effect_step 0x11d225 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x2e8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x11d22d [0x48, 0x01, 0xDE] (fun s => s.RIP = 0x11d22d) (addR64R64Effect 0x11d22d 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11d22d 6 3).toInstrSpec (add_r64_r64_effect_step 0x11d22d 0x48 0xde (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x11d230 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x11d230) (movR64R64Effect 0x11d230 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d230 7 6).toInstrSpec (mov_r64_r64_effect_step 0x11d230 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x11d233 [0x48, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x11d233) (shrR64Effect 0x11d233 4 7 52)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x11d233 4 7 52).toInstrSpec (shr_r64_imm8_effect_step 0x11d233 0x48 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x11d237 [0x48, 0x2B, 0xBC, 0x24, 0xF0, 0x02, 0x00, 0x00] (LoadPre 0x11d237 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2f0)) s (0x11d237 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d237 7 (.sib 4 none 0 (.d32 0x2f0)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11d237 7 (.sib 4 none 0 (.d32 0x2f0))).toInstrSpec (sub_r64_m64_effect_step 0x11d237 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x2f0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 85), (2, 76), (3, 3), (4, 4), (5, 5), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1d8) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 85), (2, 76), (3, 3), (4, 4), (5, 5), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1dc) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 85), (2, 76), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1e6) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 85), (2, 76), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1ea) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 85), (2, 76), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1f2) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 95), (1, 85), (2, 76), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1fa) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 85), (2, 98), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d204) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 100), (1, 85), (2, 98), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d207) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f28 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 100), (1, 85), (2, 98), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d20c) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 100), (1, 85), (2, 104), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d20f) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 100), (1, 85), (2, 106), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d213) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 100), (1, 85), (2, 108), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d21b) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 91), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d21e) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f33 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 112), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d221) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f34 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 114), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d225) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f35 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 116), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d22d) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d230) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 120), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d233) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 122), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d237) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 100), (1, 85), (2, 110), (3, 3), (4, 4), (5, 5), (6, 118), (7, 124), (11, 83), (12, 12), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d23f) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11d157_2 code

theorem rest_l11d157 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d157 bytes_l11d157) (entryMap (live .l11d157))
      73 0x11d157 bytes_l11d157 b_l11d157 := by
  have f0 : InstrSpec 0x11d157 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d157) (movR32Imm32Effect 0x11d157 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d157 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d157 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d15c [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11d15c) (movR64R64Effect 0x11d15c 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d15c 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11d15c 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d15f [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d15f) (movR64R64Effect 0x11d15f 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d15f 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d15f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d162 [0xF3, 0x48, 0xA5] (RepPre 0x11d162 (RepMovsqPre 0x11d162)) (repMovsqEffect 0x11d162)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d162).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d162 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d165 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d165) (movR32Imm32Effect 0x11d165 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d165 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d165 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d16a [0x48, 0x8D, 0xBC, 0x24, 0x98, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x11d16a) (leaR64Effect 0x11d16a 7 (.sib 4 none 0 (.d32 0xb98)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d16a 7 (.sib 4 none 0 (.d32 0xb98))).toInstrSpec (lea_r64_effect_step 0x11d16a 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb98)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d172 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11d172) (movR64R64Effect 0x11d172 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d172 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11d172 0x4c 0xee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d175 [0xF3, 0x48, 0xA5] (RepPre 0x11d175 (RepMovsqPre 0x11d175)) (repMovsqEffect 0x11d175)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d175).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d175 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x11d178 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x02, 0x00, 0x00] (LoadPre 0x11d178 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2d0)) s (0x11d178 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d178 0 (.sib 4 none 0 (.d32 0x2d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d178 0 (.sib 4 none 0 (.d32 0x2d0))).toInstrSpec (mov_r64_m64_effect_step 0x11d178 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x2d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11d180 [0x48, 0x89, 0x84, 0x24, 0x48, 0x03, 0x00, 0x00] (StorePre 0x11d180 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x348)) s (0x11d180 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d180 0 (.sib 4 none 0 (.d32 0x348)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d180 0 (.sib 4 none 0 (.d32 0x348))).toInstrSpec (mov_m64_r64_effect_step 0x11d180 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x348)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11d188 [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x02, 0x00, 0x00] (LoadPre 0x11d188 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2c8)) s (0x11d188 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d188 0 (.sib 4 none 0 (.d32 0x2c8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d188 0 (.sib 4 none 0 (.d32 0x2c8))).toInstrSpec (mov_r64_m64_effect_step 0x11d188 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x2c8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11d190 [0x48, 0x89, 0x84, 0x24, 0x40, 0x03, 0x00, 0x00] (StorePre 0x11d190 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x340)) s (0x11d190 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d190 0 (.sib 4 none 0 (.d32 0x340)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d190 0 (.sib 4 none 0 (.d32 0x340))).toInstrSpec (mov_m64_r64_effect_step 0x11d190 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x340)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x11d198 [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x02, 0x00, 0x00] (LoadPre 0x11d198 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2c0)) s (0x11d198 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d198 0 (.sib 4 none 0 (.d32 0x2c0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d198 0 (.sib 4 none 0 (.d32 0x2c0))).toInstrSpec (mov_r64_m64_effect_step 0x11d198 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x2c0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x11d1a0 [0x48, 0x89, 0x84, 0x24, 0x38, 0x03, 0x00, 0x00] (StorePre 0x11d1a0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x338)) s (0x11d1a0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d1a0 0 (.sib 4 none 0 (.d32 0x338)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d1a0 0 (.sib 4 none 0 (.d32 0x338))).toInstrSpec (mov_m64_r64_effect_step 0x11d1a0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x338)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x11d1a8 [0x48, 0x8B, 0x94, 0x24, 0xB0, 0x02, 0x00, 0x00] (LoadPre 0x11d1a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2b0)) s (0x11d1a8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d1a8 2 (.sib 4 none 0 (.d32 0x2b0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11d1a8 2 (.sib 4 none 0 (.d32 0x2b0))).toInstrSpec (mov_r64_m64_effect_step 0x11d1a8 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x2b0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x11d1b0 [0x48, 0x8B, 0x84, 0x24, 0xB8, 0x02, 0x00, 0x00] (LoadPre 0x11d1b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2b8)) s (0x11d1b0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d1b0 0 (.sib 4 none 0 (.d32 0x2b8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d1b0 0 (.sib 4 none 0 (.d32 0x2b8))).toInstrSpec (mov_r64_m64_effect_step 0x11d1b0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x2b8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x11d1b8 [0x48, 0x89, 0x84, 0x24, 0x30, 0x03, 0x00, 0x00] (StorePre 0x11d1b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x330)) s (0x11d1b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d1b8 0 (.sib 4 none 0 (.d32 0x330)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d1b8 0 (.sib 4 none 0 (.d32 0x330))).toInstrSpec (mov_m64_r64_effect_step 0x11d1b8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x330)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x11d1c0 [0x48, 0xB9, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00] (fun s => s.RIP = 0x11d1c0) (movR64Imm64Effect 0x11d1c0 1 0x3fffffffffffc)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x11d1c0 1 0x3fffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x11d1c0 0x48 0xb9 (by decide) (by decide) 0x3fffffffffffc) pre_rip
  have f18 : InstrSpec 0x11d1ca [0x4D, 0x89, 0xF3] (fun s => s.RIP = 0x11d1ca) (movR64R64Effect 0x11d1ca 11 14)
      [.gpr 14] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x11d1ca 11 14).toInstrSpec (mov_r64_r64_effect_step 0x11d1ca 0x4d 0xf3 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d1cd [0x48, 0x2B, 0x8C, 0x24, 0xF8, 0x02, 0x00, 0x00] (LoadPre 0x11d1cd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2f8)) s (0x11d1cd + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d1cd 1 (.sib 4 none 0 (.d32 0x2f8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11d1cd 1 (.sib 4 none 0 (.d32 0x2f8))).toInstrSpec (sub_r64_m64_effect_step 0x11d1cd 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x2f8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d15c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d15f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d162) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d165) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d16a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d172) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d175) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d178) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d180) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d188) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d190) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d198) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1a0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1a8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 73), (2, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1b0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (2, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1b8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (2, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1c0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 81), (2, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1ca) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 78), (1, 81), (2, 76), (3, 3), (4, 4), (5, 5), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1cd) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 78), (1, 85), (2, 76), (3, 3), (4, 4), (5, 5), (11, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d1d5) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11d157_1 code

theorem block_l11d157 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d157 :=
  Rest.liftedBlock (rest_l11d157 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d157 x hx)

theorem rest_l11d2e1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d2e1 bytes_l11d2e1) (entryMap (live .l11d2e1))
      16 0x11d2e1 bytes_l11d2e1 b_l11d2e1 := by
  have f0 : InstrSpec 0x11d2e1 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d2e1) (movR32Imm32Effect 0x11d2e1 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d2e1 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d2e1 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d2e6 [0x4C, 0x8D, 0xAC, 0x24, 0x90, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11d2e6) (leaR64Effect 0x11d2e6 13 (.sib 4 none 0 (.d32 0x490)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x11d2e6 13 (.sib 4 none 0 (.d32 0x490))).toInstrSpec (lea_r64_effect_step 0x11d2e6 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x490)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d2ee [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x11d2ee) (movR64R64Effect 0x11d2ee 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d2ee 7 13).toInstrSpec (mov_r64_r64_effect_step 0x11d2ee 0x4c 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d2f1 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d2f1) (movR64R64Effect 0x11d2f1 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d2f1 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d2f1 0x48 0xde (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11d2f4 [0xF3, 0x48, 0xA5] (RepPre 0x11d2f4 (RepMovsqPre 0x11d2f4)) (repMovsqEffect 0x11d2f4)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d2f4).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d2f4 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x11d2f7 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d2f7) (movR32Imm32Effect 0x11d2f7 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d2f7 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d2f7 0xb9 (by decide) 0xf) pre_rip
  have f6 : InstrSpec 0x11d2fc [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d2fc) (movR64R64Effect 0x11d2fc 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d2fc 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d2fc 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d2ff [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d2ff) (movR64R64Effect 0x11d2ff 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d2ff 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d2ff 0x48 0xde (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d302 [0xF3, 0x48, 0xA5] (RepPre 0x11d302 (RepMovsqPre 0x11d302)) (repMovsqEffect 0x11d302)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d302).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d302 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d305 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d305) (movR32Imm32Effect 0x11d305 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d305 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d305 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d30a [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d30a) (movR64R64Effect 0x11d30a 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d30a 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d30a 0x4c 0xff (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d30d [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d30d) (movR64R64Effect 0x11d30d 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d30d 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d30d 0x48 0xde (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d310 [0xF3, 0x48, 0xA5] (RepPre 0x11d310 (RepMovsqPre 0x11d310)) (repMovsqEffect 0x11d310)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d310).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d310 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d313 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d313) (movR64R64Effect 0x11d313 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d313 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d313 0x4c 0xff (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11d316 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d316) (movR64R64Effect 0x11d316 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d316 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d316 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d319 [0xE8, 0xF2, 0xD0, 0xFE, 0xFF] (PushPre 0x11d319 5) (callEffect (fun _ => 0x10a410) 0x11d31e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d319 0x10a410 0x11d31e).toInstrSpec (call_rel32_effect_step 0x11d319 0xfffed0f2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2e6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2ee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2f1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2f4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2f7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2fc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d2ff) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d302) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d305) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d30a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d30d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d310) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d313) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 76), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d316) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 78), (7, 76), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d319) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(3, 3), (4, 80), (5, 5), (6, 78), (7, 76), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 82) (by decide) (by decide) rfl rfl

theorem block_l11d2e1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d2e1 :=
  Rest.liftedBlock (rest_l11d2e1 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d2e1 x hx)

theorem rest_l11d31e_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x11d31e bytes_l11d31e) [(0, 64), (3, 3), (4, 4), (5, 55), (6, 87), (7, 85), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x11d36c bytes_l11d31e_1 b_l11d31e_1 := by
  have f20 : InstrSpec 0x11d36c [0xE8, 0x9F, 0xD0, 0xFE, 0xFF] (PushPre 0x11d36c 5) (callEffect (fun _ => 0x10a410) 0x11d371)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d36c 0x10a410 0x11d371).toInstrSpec (call_rel32_effect_step 0x11d36c 0xfffed09f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 64), (3, 3), (4, 89), (5, 55), (6, 87), (7, 85), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f20 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 91) (by decide) (by decide) rfl rfl

theorem rest_l11d31e [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d31e bytes_l11d31e) (entryMap (live .l11d31e))
      21 0x11d31e bytes_l11d31e b_l11d31e := by
  have f0 : InstrSpec 0x11d31e [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d31e) (movR32Imm32Effect 0x11d31e 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d31e 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d31e 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d323 [0x48, 0x8D, 0xAC, 0x24, 0x18, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11d323) (leaR64Effect 0x11d323 5 (.sib 4 none 0 (.d32 0x418)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x11d323 5 (.sib 4 none 0 (.d32 0x418))).toInstrSpec (lea_r64_effect_step 0x11d323 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x418)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d32b [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11d32b) (movR64R64Effect 0x11d32b 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d32b 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11d32b 0x48 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d32e [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d32e) (movR64R64Effect 0x11d32e 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d32e 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d32e 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11d331 [0xF3, 0x48, 0xA5] (RepPre 0x11d331 (RepMovsqPre 0x11d331)) (repMovsqEffect 0x11d331)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d331).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d331 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x11d334 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d334) (movR32Imm32Effect 0x11d334 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d334 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d334 0xb9 (by decide) 0xf) pre_rip
  have f6 : InstrSpec 0x11d339 [0x48, 0x8D, 0x84, 0x24, 0x08, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x11d339) (leaR64Effect 0x11d339 0 (.sib 4 none 0 (.d32 0x508)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d339 0 (.sib 4 none 0 (.d32 0x508))).toInstrSpec (lea_r64_effect_step 0x11d339 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x508)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d341 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d341) (movR64R64Effect 0x11d341 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d341 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d341 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d344 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d344) (movR64R64Effect 0x11d344 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d344 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d344 0x48 0xee (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11d347 [0xF3, 0x48, 0xA5] (RepPre 0x11d347 (RepMovsqPre 0x11d347)) (repMovsqEffect 0x11d347)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d347).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d347 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f10 : InstrSpec 0x11d34a [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d34a) (movR32Imm32Effect 0x11d34a 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d34a 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d34a 0xb9 (by decide) 0xf) pre_rip
  have f11 : InstrSpec 0x11d34f [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d34f) (movR64R64Effect 0x11d34f 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d34f 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d34f 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d352 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d352) (movR64R64Effect 0x11d352 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d352 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d352 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11d355 [0xF3, 0x48, 0xA5] (RepPre 0x11d355 (RepMovsqPre 0x11d355)) (repMovsqEffect 0x11d355)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d355).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d355 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f14 : InstrSpec 0x11d358 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d358) (movR32Imm32Effect 0x11d358 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d358 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d358 0xb9 (by decide) 0xf) pre_rip
  have f15 : InstrSpec 0x11d35d [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d35d) (movR64R64Effect 0x11d35d 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d35d 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d35d 0x4c 0xff (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d360 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d360) (movR64R64Effect 0x11d360 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d360 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d360 0x48 0xde (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11d363 [0xF3, 0x48, 0xA5] (RepPre 0x11d363 (RepMovsqPre 0x11d363)) (repMovsqEffect 0x11d363)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d363).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d363 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f18 : InstrSpec 0x11d366 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d366) (movR64R64Effect 0x11d366 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d366 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d366 0x4c 0xff (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d369 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d369) (movR64R64Effect 0x11d369 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d369 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d369 0x4c 0xe6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d323) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d32b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 55), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d32e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 55), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d331) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d334) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d339) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 62), (3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d341) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 62), (3, 3), (4, 4), (5, 55), (7, 66), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d344) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 62), (3, 3), (4, 4), (5, 55), (6, 68), (7, 66), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d347) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d34a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 71), (3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d34f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 71), (3, 3), (4, 4), (5, 55), (7, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d352) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 64), (1, 71), (3, 3), (4, 4), (5, 55), (6, 75), (7, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d355) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d358) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 64), (1, 78), (3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d35d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 64), (1, 78), (3, 3), (4, 4), (5, 55), (7, 80), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d360) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 64), (1, 78), (3, 3), (4, 4), (5, 55), (6, 82), (7, 80), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d363) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d366) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 55), (7, 85), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d369) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 55), (6, 87), (7, 85), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d36c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11d31e_1 code

theorem block_l11d31e [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d31e :=
  Rest.liftedBlock (rest_l11d31e hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d31e x hx)

theorem rest_l11d371 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d371 bytes_l11d371) (entryMap (live .l11d371))
      20 0x11d371 bytes_l11d371 b_l11d371 := by
  have f0 : InstrSpec 0x11d371 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d371) (movR32Imm32Effect 0x11d371 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d371 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d371 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d376 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11d376) (movR64R64Effect 0x11d376 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d376 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11d376 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d379 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d379) (movR64R64Effect 0x11d379 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d379 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d379 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d37c [0xF3, 0x48, 0xA5] (RepPre 0x11d37c (RepMovsqPre 0x11d37c)) (repMovsqEffect 0x11d37c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d37c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d37c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d37f [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d37f) (movR32Imm32Effect 0x11d37f 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d37f 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d37f 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d384 [0x48, 0x8D, 0x84, 0x24, 0x80, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x11d384) (leaR64Effect 0x11d384 0 (.sib 4 none 0 (.d32 0x580)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d384 0 (.sib 4 none 0 (.d32 0x580))).toInstrSpec (lea_r64_effect_step 0x11d384 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x580)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d38c [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d38c) (movR64R64Effect 0x11d38c 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d38c 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d38c 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d38f [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d38f) (movR64R64Effect 0x11d38f 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d38f 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d38f 0x48 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d392 [0xF3, 0x48, 0xA5] (RepPre 0x11d392 (RepMovsqPre 0x11d392)) (repMovsqEffect 0x11d392)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d392).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d392 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d395 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d395) (movR32Imm32Effect 0x11d395 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d395 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d395 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d39a [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d39a) (movR64R64Effect 0x11d39a 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d39a 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d39a 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d39d [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d39d) (movR64R64Effect 0x11d39d 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d39d 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d39d 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d3a0 [0xF3, 0x48, 0xA5] (RepPre 0x11d3a0 (RepMovsqPre 0x11d3a0)) (repMovsqEffect 0x11d3a0)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d3a0).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d3a0 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d3a3 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d3a3) (movR32Imm32Effect 0x11d3a3 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d3a3 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d3a3 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d3a8 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d3a8) (movR64R64Effect 0x11d3a8 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d3a8 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d3a8 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d3ab [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d3ab) (movR64R64Effect 0x11d3ab 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d3ab 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d3ab 0x48 0xde (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d3ae [0xF3, 0x48, 0xA5] (RepPre 0x11d3ae (RepMovsqPre 0x11d3ae)) (repMovsqEffect 0x11d3ae)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d3ae).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d3ae 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d3b1 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d3b1) (movR64R64Effect 0x11d3b1 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d3b1 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d3b1 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d3b4 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d3b4) (movR64R64Effect 0x11d3b4 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d3b4 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d3b4 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d3b7 [0xE8, 0x54, 0xD0, 0xFE, 0xFF] (PushPre 0x11d3b7 5) (callEffect (fun _ => 0x10a410) 0x11d3bc)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d3b7 0x10a410 0x11d3bc).toInstrSpec (call_rel32_effect_step 0x11d3b7 0xfffed054 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d376) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d379) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d37c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d37f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d384) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d38c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d38f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d392) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d395) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d39a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d39d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3a0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3a3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3a8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3ab) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3ae) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3b1) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3b4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3b7) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d371 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d371 :=
  Rest.liftedBlock (rest_l11d371 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d371 x hx)

theorem rest_l11d3bc [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d3bc bytes_l11d3bc) (entryMap (live .l11d3bc))
      20 0x11d3bc bytes_l11d3bc b_l11d3bc := by
  have f0 : InstrSpec 0x11d3bc [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d3bc) (movR32Imm32Effect 0x11d3bc 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d3bc 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d3bc 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d3c1 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11d3c1) (movR64R64Effect 0x11d3c1 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d3c1 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11d3c1 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d3c4 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d3c4) (movR64R64Effect 0x11d3c4 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d3c4 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d3c4 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d3c7 [0xF3, 0x48, 0xA5] (RepPre 0x11d3c7 (RepMovsqPre 0x11d3c7)) (repMovsqEffect 0x11d3c7)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d3c7).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d3c7 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d3ca [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d3ca) (movR32Imm32Effect 0x11d3ca 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d3ca 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d3ca 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d3cf [0x48, 0x8D, 0x84, 0x24, 0xF8, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x11d3cf) (leaR64Effect 0x11d3cf 0 (.sib 4 none 0 (.d32 0x5f8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d3cf 0 (.sib 4 none 0 (.d32 0x5f8))).toInstrSpec (lea_r64_effect_step 0x11d3cf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x5f8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d3d7 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d3d7) (movR64R64Effect 0x11d3d7 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d3d7 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d3d7 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d3da [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d3da) (movR64R64Effect 0x11d3da 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d3da 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d3da 0x48 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d3dd [0xF3, 0x48, 0xA5] (RepPre 0x11d3dd (RepMovsqPre 0x11d3dd)) (repMovsqEffect 0x11d3dd)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d3dd).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d3dd 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d3e0 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d3e0) (movR32Imm32Effect 0x11d3e0 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d3e0 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d3e0 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d3e5 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d3e5) (movR64R64Effect 0x11d3e5 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d3e5 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d3e5 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d3e8 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d3e8) (movR64R64Effect 0x11d3e8 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d3e8 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d3e8 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d3eb [0xF3, 0x48, 0xA5] (RepPre 0x11d3eb (RepMovsqPre 0x11d3eb)) (repMovsqEffect 0x11d3eb)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d3eb).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d3eb 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d3ee [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d3ee) (movR32Imm32Effect 0x11d3ee 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d3ee 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d3ee 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d3f3 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d3f3) (movR64R64Effect 0x11d3f3 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d3f3 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d3f3 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d3f6 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d3f6) (movR64R64Effect 0x11d3f6 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d3f6 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d3f6 0x48 0xde (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d3f9 [0xF3, 0x48, 0xA5] (RepPre 0x11d3f9 (RepMovsqPre 0x11d3f9)) (repMovsqEffect 0x11d3f9)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d3f9).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d3f9 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d3fc [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d3fc) (movR64R64Effect 0x11d3fc 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d3fc 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d3fc 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d3ff [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d3ff) (movR64R64Effect 0x11d3ff 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d3ff 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d3ff 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d402 [0xE8, 0x09, 0xD0, 0xFE, 0xFF] (PushPre 0x11d402 5) (callEffect (fun _ => 0x10a410) 0x11d407)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d402 0x10a410 0x11d407).toInstrSpec (call_rel32_effect_step 0x11d402 0xfffed009 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3c7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3ca) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3cf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3d7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3da) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3dd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3e0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3e5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3e8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3eb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3ee) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3f3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3f6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3f9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3fc) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d3ff) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d402) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d3bc [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d3bc :=
  Rest.liftedBlock (rest_l11d3bc hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d3bc x hx)

theorem rest_l11d407 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d407 bytes_l11d407) (entryMap (live .l11d407))
      20 0x11d407 bytes_l11d407 b_l11d407 := by
  have f0 : InstrSpec 0x11d407 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d407) (movR32Imm32Effect 0x11d407 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d407 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d407 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d40c [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11d40c) (movR64R64Effect 0x11d40c 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d40c 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11d40c 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d40f [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d40f) (movR64R64Effect 0x11d40f 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d40f 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d40f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d412 [0xF3, 0x48, 0xA5] (RepPre 0x11d412 (RepMovsqPre 0x11d412)) (repMovsqEffect 0x11d412)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d412).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d412 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d415 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d415) (movR32Imm32Effect 0x11d415 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d415 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d415 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d41a [0x48, 0x8D, 0x84, 0x24, 0x70, 0x06, 0x00, 0x00] (fun s => s.RIP = 0x11d41a) (leaR64Effect 0x11d41a 0 (.sib 4 none 0 (.d32 0x670)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d41a 0 (.sib 4 none 0 (.d32 0x670))).toInstrSpec (lea_r64_effect_step 0x11d41a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x670)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d422 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d422) (movR64R64Effect 0x11d422 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d422 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d422 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d425 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d425) (movR64R64Effect 0x11d425 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d425 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d425 0x48 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d428 [0xF3, 0x48, 0xA5] (RepPre 0x11d428 (RepMovsqPre 0x11d428)) (repMovsqEffect 0x11d428)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d428).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d428 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d42b [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d42b) (movR32Imm32Effect 0x11d42b 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d42b 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d42b 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d430 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d430) (movR64R64Effect 0x11d430 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d430 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d430 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d433 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d433) (movR64R64Effect 0x11d433 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d433 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d433 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d436 [0xF3, 0x48, 0xA5] (RepPre 0x11d436 (RepMovsqPre 0x11d436)) (repMovsqEffect 0x11d436)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d436).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d436 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d439 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d439) (movR32Imm32Effect 0x11d439 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d439 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d439 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d43e [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d43e) (movR64R64Effect 0x11d43e 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d43e 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d43e 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d441 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d441) (movR64R64Effect 0x11d441 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d441 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d441 0x48 0xde (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d444 [0xF3, 0x48, 0xA5] (RepPre 0x11d444 (RepMovsqPre 0x11d444)) (repMovsqEffect 0x11d444)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d444).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d444 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d447 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d447) (movR64R64Effect 0x11d447 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d447 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d447 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d44a [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d44a) (movR64R64Effect 0x11d44a 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d44a 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d44a 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d44d [0xE8, 0xBE, 0xCF, 0xFE, 0xFF] (PushPre 0x11d44d 5) (callEffect (fun _ => 0x10a410) 0x11d452)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d44d 0x10a410 0x11d452).toInstrSpec (call_rel32_effect_step 0x11d44d 0xfffecfbe (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d40c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d40f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d412) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d415) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d41a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d422) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d425) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d428) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d42b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d430) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d433) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d436) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d439) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d43e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d441) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d444) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d447) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d44a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d44d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d407 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d407 :=
  Rest.liftedBlock (rest_l11d407 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d407 x hx)

theorem rest_l11d452 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d452 bytes_l11d452) (entryMap (live .l11d452))
      20 0x11d452 bytes_l11d452 b_l11d452 := by
  have f0 : InstrSpec 0x11d452 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d452) (movR32Imm32Effect 0x11d452 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d452 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d452 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d457 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11d457) (movR64R64Effect 0x11d457 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d457 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11d457 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d45a [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d45a) (movR64R64Effect 0x11d45a 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d45a 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d45a 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d45d [0xF3, 0x48, 0xA5] (RepPre 0x11d45d (RepMovsqPre 0x11d45d)) (repMovsqEffect 0x11d45d)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d45d).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d45d 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d460 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d460) (movR32Imm32Effect 0x11d460 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d460 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d460 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d465 [0x48, 0x8D, 0x84, 0x24, 0xE8, 0x06, 0x00, 0x00] (fun s => s.RIP = 0x11d465) (leaR64Effect 0x11d465 0 (.sib 4 none 0 (.d32 0x6e8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d465 0 (.sib 4 none 0 (.d32 0x6e8))).toInstrSpec (lea_r64_effect_step 0x11d465 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x6e8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d46d [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d46d) (movR64R64Effect 0x11d46d 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d46d 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d46d 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d470 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d470) (movR64R64Effect 0x11d470 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d470 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d470 0x48 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d473 [0xF3, 0x48, 0xA5] (RepPre 0x11d473 (RepMovsqPre 0x11d473)) (repMovsqEffect 0x11d473)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d473).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d473 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d476 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d476) (movR32Imm32Effect 0x11d476 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d476 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d476 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d47b [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d47b) (movR64R64Effect 0x11d47b 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d47b 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d47b 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d47e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d47e) (movR64R64Effect 0x11d47e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d47e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d47e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d481 [0xF3, 0x48, 0xA5] (RepPre 0x11d481 (RepMovsqPre 0x11d481)) (repMovsqEffect 0x11d481)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d481).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d481 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d484 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d484) (movR32Imm32Effect 0x11d484 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d484 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d484 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d489 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d489) (movR64R64Effect 0x11d489 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d489 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d489 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d48c [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d48c) (movR64R64Effect 0x11d48c 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d48c 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d48c 0x48 0xde (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d48f [0xF3, 0x48, 0xA5] (RepPre 0x11d48f (RepMovsqPre 0x11d48f)) (repMovsqEffect 0x11d48f)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d48f).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d48f 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d492 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d492) (movR64R64Effect 0x11d492 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d492 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d492 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d495 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d495) (movR64R64Effect 0x11d495 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d495 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d495 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d498 [0xE8, 0x73, 0xCF, 0xFE, 0xFF] (PushPre 0x11d498 5) (callEffect (fun _ => 0x10a410) 0x11d49d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d498 0x10a410 0x11d49d).toInstrSpec (call_rel32_effect_step 0x11d498 0xfffecf73 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d457) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d45a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d45d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d460) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d465) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d46d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d470) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d473) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d476) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d47b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d47e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d481) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d484) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d489) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d48c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d48f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d492) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d495) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d498) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d452 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d452 :=
  Rest.liftedBlock (rest_l11d452 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d452 x hx)

theorem rest_l11d49d [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d49d bytes_l11d49d) (entryMap (live .l11d49d))
      20 0x11d49d bytes_l11d49d b_l11d49d := by
  have f0 : InstrSpec 0x11d49d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d49d) (movR32Imm32Effect 0x11d49d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d49d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d49d 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d4a2 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11d4a2) (movR64R64Effect 0x11d4a2 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d4a2 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11d4a2 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d4a5 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d4a5) (movR64R64Effect 0x11d4a5 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d4a5 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d4a5 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d4a8 [0xF3, 0x48, 0xA5] (RepPre 0x11d4a8 (RepMovsqPre 0x11d4a8)) (repMovsqEffect 0x11d4a8)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d4a8).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d4a8 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d4ab [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d4ab) (movR32Imm32Effect 0x11d4ab 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d4ab 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d4ab 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d4b0 [0x48, 0x8D, 0x84, 0x24, 0x60, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x11d4b0) (leaR64Effect 0x11d4b0 0 (.sib 4 none 0 (.d32 0x760)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d4b0 0 (.sib 4 none 0 (.d32 0x760))).toInstrSpec (lea_r64_effect_step 0x11d4b0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x760)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d4b8 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11d4b8) (movR64R64Effect 0x11d4b8 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d4b8 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11d4b8 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d4bb [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d4bb) (movR64R64Effect 0x11d4bb 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d4bb 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d4bb 0x48 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d4be [0xF3, 0x48, 0xA5] (RepPre 0x11d4be (RepMovsqPre 0x11d4be)) (repMovsqEffect 0x11d4be)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d4be).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d4be 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x11d4c1 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d4c1) (movR32Imm32Effect 0x11d4c1 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d4c1 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d4c1 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x11d4c6 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d4c6) (movR64R64Effect 0x11d4c6 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d4c6 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d4c6 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d4c9 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11d4c9) (movR64R64Effect 0x11d4c9 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d4c9 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11d4c9 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d4cc [0xF3, 0x48, 0xA5] (RepPre 0x11d4cc (RepMovsqPre 0x11d4cc)) (repMovsqEffect 0x11d4cc)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d4cc).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d4cc 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x11d4cf [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d4cf) (movR32Imm32Effect 0x11d4cf 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d4cf 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d4cf 0xb9 (by decide) 0xf) pre_rip
  have f14 : InstrSpec 0x11d4d4 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d4d4) (movR64R64Effect 0x11d4d4 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d4d4 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d4d4 0x4c 0xff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d4d7 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x11d4d7) (movR64R64Effect 0x11d4d7 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d4d7 6 3).toInstrSpec (mov_r64_r64_effect_step 0x11d4d7 0x48 0xde (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d4da [0xF3, 0x48, 0xA5] (RepPre 0x11d4da (RepMovsqPre 0x11d4da)) (repMovsqEffect 0x11d4da)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d4da).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d4da 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x11d4dd [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d4dd) (movR64R64Effect 0x11d4dd 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d4dd 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d4dd 0x4c 0xff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11d4e0 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d4e0) (movR64R64Effect 0x11d4e0 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d4e0 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d4e0 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d4e3 [0xE8, 0x28, 0xCF, 0xFE, 0xFF] (PushPre 0x11d4e3 5) (callEffect (fun _ => 0x10a410) 0x11d4e8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d4e3 0x10a410 0x11d4e8).toInstrSpec (call_rel32_effect_step 0x11d4e3 0xfffecf28 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4a5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4a8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4ab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4b0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4b8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4bb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 60), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4be) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4c1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4c6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4c9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4cc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4cf) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4d4) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4d7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 76), (3, 3), (4, 4), (5, 5), (6, 80), (7, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4da) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4dd) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4e0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4e3) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem block_l11d49d [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d49d :=
  Rest.liftedBlock (rest_l11d49d hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d49d x hx)

theorem rest_l11d4e8 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d4e8 bytes_l11d4e8) (entryMap (live .l11d4e8))
      10 0x11d4e8 bytes_l11d4e8 b_l11d4e8 := by
  have f0 : InstrSpec 0x11d4e8 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d4e8) (movR32Imm32Effect 0x11d4e8 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d4e8 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d4e8 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11d4ed [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11d4ed) (movR64R64Effect 0x11d4ed 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d4ed 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11d4ed 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d4f0 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d4f0) (movR64R64Effect 0x11d4f0 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d4f0 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d4f0 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d4f3 [0xF3, 0x48, 0xA5] (RepPre 0x11d4f3 (RepMovsqPre 0x11d4f3)) (repMovsqEffect 0x11d4f3)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d4f3).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d4f3 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d4f6 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d4f6) (movR32Imm32Effect 0x11d4f6 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d4f6 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d4f6 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11d4fb [0x48, 0x8D, 0xBC, 0x24, 0xD8, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x11d4fb) (leaR64Effect 0x11d4fb 7 (.sib 4 none 0 (.d32 0x7d8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d4fb 7 (.sib 4 none 0 (.d32 0x7d8))).toInstrSpec (lea_r64_effect_step 0x11d4fb 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x7d8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d503 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x11d503) (movR64R64Effect 0x11d503 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d503 6 5).toInstrSpec (mov_r64_r64_effect_step 0x11d503 0x48 0xee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d506 [0xF3, 0x48, 0xA5] (RepPre 0x11d506 (RepMovsqPre 0x11d506)) (repMovsqEffect 0x11d506)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d506).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d506 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x11d509 [0x4C, 0x39, 0x74, 0x24, 0x68] (LoadPre 0x11d509 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11d509 + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d509 5 64 14 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 14, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x11d509 5 14 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (cmp_m64_r64_effect_step 0x11d509 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4ed) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4f0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4f3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4f6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d4fb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d503) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (4, 4), (5, 5), (6, 64), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d506) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d509) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d50e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel32_effect_step 0x11d50e 4 0x220b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11d4e8 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d4e8 :=
  Rest.liftedBlock (rest_l11d4e8 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d4e8 x hx)

theorem rest_l11d514 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d514 bytes_l11d514) (entryMap (live .l11d514))
      6 0x11d514 bytes_l11d514 b_l11d514 := by
  have f0 : InstrSpec 0x11d514 [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11d514) (movR32Imm32Effect 0x11d514 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x11d514 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x11d514 0xba (by decide) 0x3c0) pre_rip
  have f1 : InstrSpec 0x11d519 [0x48, 0x8B, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x11d519 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11d519 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d519 5 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x11d519 5 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x11d519 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11d521 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x11d521) (movR64R64Effect 0x11d521 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d521 7 5).toInstrSpec (mov_r64_r64_effect_step 0x11d521 0x48 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d524 [0x48, 0x8D, 0xB4, 0x24, 0x50, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x11d524) (leaR64Effect 0x11d524 6 (.sib 4 none 0 (.d32 0x850)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d524 6 (.sib 4 none 0 (.d32 0x850))).toInstrSpec (lea_r64_effect_step 0x11d524 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x850)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11d52c [0x48, 0x8D, 0x1D, 0xED, 0xD2, 0x00, 0x00] (fun s => s.RIP = 0x11d52c) (leaR64Effect 0x11d52c 3 (.rip 0xd2ed))
      [] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x11d52c 3 (.rip 0xd2ed)).toInstrSpec (lea_r64_effect_step 0x11d52c 0x48 (by decide) 3 (.rip 0xd2ed) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11d533 [0xFF, 0xD3] (GoesTo (CallPre 0x11d533 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d535) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d535)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x11d533 3 0x11d535).toInstrSpec (call_r64_effect_step 0x11d533 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d519) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (4, 4), (5, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d521) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (4, 4), (5, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d524) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (4, 4), (5, 55), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d52c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 53), (3, 61), (4, 4), (5, 55), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d533) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 53), (3, 61), (4, 63), (5, 55), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l11d514 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d514 :=
  Rest.liftedBlock (rest_l11d514 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d514 x hx)

theorem rest_l11d535 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d535 bytes_l11d535) (entryMap (live .l11d535))
      4 0x11d535 bytes_l11d535 b_l11d535 := by
  have f0 : InstrSpec 0x11d535 [0x48, 0x8D, 0xBD, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11d535) (leaR64Effect 0x11d535 7 (.base 5 (.d32 0x3c0)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d535 7 (.base 5 (.d32 0x3c0))).toInstrSpec (lea_r64_effect_step 0x11d535 0x48 (by decide) 7 (.base 5 (.d32 0x3c0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d53c [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11d53c) (movR32Imm32Effect 0x11d53c 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x11d53c 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x11d53c 0xba (by decide) 0x3c0) pre_rip
  have f2 : InstrSpec 0x11d541 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11d541) (movR64R64Effect 0x11d541 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d541 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11d541 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d544 [0xFF, 0xD3] (GoesTo (CallPre 0x11d544 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d546) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d546)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x11d544 3 0x11d546).toInstrSpec (call_r64_effect_step 0x11d544 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d53c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d541) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d544) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11d535 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d535 :=
  Rest.liftedBlock (rest_l11d535 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d535 x hx)

theorem rest_l11d546 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d546 bytes_l11d546) (entryMap (live .l11d546))
      3 0x11d546 bytes_l11d546 b_l11d546 := by
  have f0 : InstrSpec 0x11d546 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d546) (movR64R64Effect 0x11d546 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d546 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d546 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d549 [0x48, 0x8D, 0xB4, 0x24, 0x70, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x11d549) (leaR64Effect 0x11d549 6 (.sib 4 none 0 (.d32 0x270)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d549 6 (.sib 4 none 0 (.d32 0x270))).toInstrSpec (lea_r64_effect_step 0x11d549 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x270)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d551 [0xE8, 0xEA, 0xD4, 0xFF, 0xFF] (PushPre 0x11d551 5) (callEffect (fun _ => 0x11aa40) 0x11d556)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d551 0x11aa40 0x11d556).toInstrSpec (call_rel32_effect_step 0x11d551 0xffffd4ea (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d549) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d551) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa40) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l11d546 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d546 :=
  Rest.liftedBlock (rest_l11d546 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d546 x hx)

theorem rest_l11d556 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d556 bytes_l11d556) (entryMap (live .l11d556))
      3 0x11d556 bytes_l11d556 b_l11d556 := by
  have f0 : InstrSpec 0x11d556 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d556) (movR64R64Effect 0x11d556 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d556 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d556 0x4c 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d559 [0x48, 0x8D, 0xB4, 0x24, 0x90, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x11d559) (leaR64Effect 0x11d559 6 (.sib 4 none 0 (.d32 0x290)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d559 6 (.sib 4 none 0 (.d32 0x290))).toInstrSpec (lea_r64_effect_step 0x11d559 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x290)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d561 [0xE8, 0xDA, 0xD4, 0xFF, 0xFF] (PushPre 0x11d561 5) (callEffect (fun _ => 0x11aa40) 0x11d566)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d561 0x11aa40 0x11d566).toInstrSpec (call_rel32_effect_step 0x11d561 0xffffd4da (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d559) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d561) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa40) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l11d556 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d556 :=
  Rest.liftedBlock (rest_l11d556 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d556 x hx)

theorem rest_l11d566 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d566 bytes_l11d566) (entryMap (live .l11d566))
      3 0x11d566 bytes_l11d566 b_l11d566 := by
  have f0 : InstrSpec 0x11d566 [0x48, 0x8B, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x11d566 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11d566 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d566 6 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11d566 6 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x11d566 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11d56e [0x48, 0x39, 0x74, 0x24, 0x60] (LoadPre 0x11d56e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11d56e + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d56e 5 64 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 6, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x11d56e 5 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (cmp_m64_r64_effect_step 0x11d56e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d56e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d573) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x11d573 4 0x21bd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11d566 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d566 :=
  Rest.liftedBlock (rest_l11d566 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d566 x hx)

theorem rest_l11d579_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x11d579 bytes_l11d579) [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x11d5fc bytes_l11d579_1 b_l11d579_1 := by
  have f20 : InstrSpec 0x11d5fc [0x88, 0x44, 0x32, 0x41] (StorePre 0x11d5fc 4 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x41)) s (0x11d5fc + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11d5fc 4 0 (.sib 2 (some 6) 0 (.d8 0x41)))
      [.gpr 0, .gpr 2, .gpr 6] [] [.rip] :=
    (movM8R8Effect_footprint 0x11d5fc 4 0 (.sib 2 (some 6) 0 (.d8 0x41))).toInstrSpec (mov_m8_r8_effect_step 0x11d5fc 0 (by decide) (.sib 2 (some 6) 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x11d600 [0x48, 0x83, 0xC6, 0x42] (fun s => s.RIP = 0x11d600) (addR64Imm8Effect 0x11d600 6 0x42)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11d600 6 0x42).toInstrSpec (add_r64_imm8_effect_step 0x11d600 0x48 0xc6 0x42 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11d604 [0x49, 0x81, 0xC6, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d604) (addR64Imm32Effect 0x11d604 14 0x98)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11d604 14 0x98).toInstrSpec (add_r64_imm32_effect_step 0x11d604 0x49 0xc6 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11d60b [0x48, 0x81, 0xC5, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x11d60b) (addR64Imm32Effect 0x11d60b 5 0x780)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11d60b 5 0x780).toInstrSpec (add_r64_imm32_effect_step 0x11d60b 0x48 0xc5 0x780 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x11d612 [0x4C, 0x39, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x11d612 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11d612 + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x11d612 8 64 14 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 14, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x11d612 8 14 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (cmp_m64_r64_effect_step 0x11d612 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d600) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d604) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f22 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 87), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d60b) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f23 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 89), (6, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 87), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d612) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f24 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 89), (6, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 87), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d61a) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 93) (jcc_rel32_effect_step 0x11d61a 5 0xfffff300) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l11d579 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d579 bytes_l11d579) (entryMap (live .l11d579))
      26 0x11d579 bytes_l11d579 b_l11d579 := by
  have f0 : InstrSpec 0x11d579 [0x0F, 0xB6, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00] (LoadPre 0x11d579 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x11d579 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11d579 8 0 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11d579 8 0 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (movzx_r32_m8_effect_step 0x11d579 0 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11d581 [0x48, 0x8B, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x11d581 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d581 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d581 2 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11d581 2 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x11d581 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11d589 [0x88, 0x44, 0x32, 0x20] (StorePre 0x11d589 4 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x20)) s (0x11d589 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11d589 4 0 (.sib 2 (some 6) 0 (.d8 0x20)))
      [.gpr 0, .gpr 2, .gpr 6] [] [.rip] :=
    (movM8R8Effect_footprint 0x11d589 4 0 (.sib 2 (some 6) 0 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x11d589 0 (by decide) (.sib 2 (some 6) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11d58d [0x48, 0x8B, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x11d58d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x11d58d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d58d 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d58d 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x11d58d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11d595 [0x48, 0x89, 0x44, 0x32, 0x18] (StorePre 0x11d595 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x18)) s (0x11d595 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d595 0 (.sib 2 (some 6) 0 (.d8 0x18)))
      [.gpr 0, .gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d595 0 (.sib 2 (some 6) 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11d595 0x48 (by decide) 0 (.sib 2 (some 6) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x11d59a [0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (LoadPre 0x11d59a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x11d59a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d59a 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d59a 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_r64_m64_effect_step 0x11d59a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11d5a2 [0x48, 0x89, 0x44, 0x32, 0x10] (StorePre 0x11d5a2 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x10)) s (0x11d5a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5a2 0 (.sib 2 (some 6) 0 (.d8 0x10)))
      [.gpr 0, .gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d5a2 0 (.sib 2 (some 6) 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11d5a2 0x48 (by decide) 0 (.sib 2 (some 6) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x11d5a7 [0x48, 0x8B, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x11d5a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11d5a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5a7 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d5a7 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_r64_m64_effect_step 0x11d5a7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11d5af [0x48, 0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x11d5af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x11d5af + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5af 1 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11d5af 1 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_r64_m64_effect_step 0x11d5af 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11d5b7 [0x48, 0x89, 0x4C, 0x32, 0x08] (StorePre 0x11d5b7 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x8)) s (0x11d5b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5b7 1 (.sib 2 (some 6) 0 (.d8 0x8)))
      [.gpr 1, .gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d5b7 1 (.sib 2 (some 6) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11d5b7 0x48 (by decide) 1 (.sib 2 (some 6) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11d5bc [0x48, 0x89, 0x04, 0x32] (StorePre 0x11d5bc 4 (fun s => AddrMode.addr (.sib 2 (some 6) 0 .none) s (0x11d5bc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d5bc 0 (.sib 2 (some 6) 0 .none))
      [.gpr 0, .gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d5bc 0 (.sib 2 (some 6) 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11d5bc 0x48 (by decide) 0 (.sib 2 (some 6) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11d5c0 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (LoadPre 0x11d5c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11d5c0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5c0 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d5c0 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_r64_m64_effect_step 0x11d5c0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x11d5c8 [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x01, 0x00, 0x00] (LoadPre 0x11d5c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x11d5c8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5c8 1 (.sib 4 none 0 (.d32 0x1d8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11d5c8 1 (.sib 4 none 0 (.d32 0x1d8))).toInstrSpec (mov_r64_m64_effect_step 0x11d5c8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x11d5d0 [0x48, 0x89, 0x44, 0x32, 0x21] (StorePre 0x11d5d0 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x21)) s (0x11d5d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5d0 0 (.sib 2 (some 6) 0 (.d8 0x21)))
      [.gpr 0, .gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d5d0 0 (.sib 2 (some 6) 0 (.d8 0x21))).toInstrSpec (mov_m64_r64_effect_step 0x11d5d0 0x48 (by decide) 0 (.sib 2 (some 6) 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x11d5d5 [0x48, 0x89, 0x4C, 0x32, 0x29] (StorePre 0x11d5d5 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x29)) s (0x11d5d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5d5 1 (.sib 2 (some 6) 0 (.d8 0x29)))
      [.gpr 1, .gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d5d5 1 (.sib 2 (some 6) 0 (.d8 0x29))).toInstrSpec (mov_m64_r64_effect_step 0x11d5d5 0x48 (by decide) 1 (.sib 2 (some 6) 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x11d5da [0x48, 0x8B, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00] (LoadPre 0x11d5da (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11d5da + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5da 0 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d5da 0 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_r64_m64_effect_step 0x11d5da 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x11d5e2 [0x48, 0x89, 0x44, 0x32, 0x31] (StorePre 0x11d5e2 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x31)) s (0x11d5e2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5e2 0 (.sib 2 (some 6) 0 (.d8 0x31)))
      [.gpr 0, .gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d5e2 0 (.sib 2 (some 6) 0 (.d8 0x31))).toInstrSpec (mov_m64_r64_effect_step 0x11d5e2 0x48 (by decide) 0 (.sib 2 (some 6) 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x11d5e7 [0x48, 0x8B, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00] (LoadPre 0x11d5e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x11d5e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5e7 0 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d5e7 0 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (mov_r64_m64_effect_step 0x11d5e7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x11d5ef [0x48, 0x89, 0x44, 0x32, 0x39] (StorePre 0x11d5ef 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x39)) s (0x11d5ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5ef 0 (.sib 2 (some 6) 0 (.d8 0x39)))
      [.gpr 0, .gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d5ef 0 (.sib 2 (some 6) 0 (.d8 0x39))).toInstrSpec (mov_m64_r64_effect_step 0x11d5ef 0x48 (by decide) 0 (.sib 2 (some 6) 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11d5f4 [0x0F, 0xB6, 0x84, 0x24, 0xF0, 0x01, 0x00, 0x00] (LoadPre 0x11d5f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x11d5f4 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11d5f4 8 0 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11d5f4 8 0 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (movzx_r32_m8_effect_step 0x11d5f4 0 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d581) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d589) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d58d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d595) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d59a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5a2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5a7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5af) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 66), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5b7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 66), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5bc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 66), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5c0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 66), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5c8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5d0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5d5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 70), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5da) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5e2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5e7) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5ef) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5f4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d5fc) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11d579_1 code

theorem block_l11d579 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d579 :=
  Rest.liftedBlock (rest_l11d579 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d579 x hx)

theorem rest_l11d620 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d620 bytes_l11d620) (entryMap (live .l11d620))
      19 0x11d620 bytes_l11d620 b_l11d620 := by
  have f0 : InstrSpec 0x11d620 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d620) (leaR64Effect 0x11d620 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d620 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d620 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d628 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d628) (movR32Imm32Effect 0x11d628 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d628 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d628 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x11d62d [0x48, 0xC7, 0xC6, 0x58, 0x32, 0x20, 0x00] (fun s => s.RIP = 0x11d62d) (movR64Imm32Effect 0x11d62d 6 0x203258)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x11d62d 6 0x203258).toInstrSpec (mov_r64_imm32_effect_step 0x11d62d 0x48 0xc6 (by decide) (by decide) (by decide) 0x203258) pre_rip
  have f3 : InstrSpec 0x11d634 [0xF3, 0x48, 0xA5] (RepPre 0x11d634 (RepMovsqPre 0x11d634)) (repMovsqEffect 0x11d634)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d634).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d634 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11d637 [0x48, 0x8B, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x11d637 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11d637 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d637 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11d637 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_r64_m64_effect_step 0x11d637 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11d63f [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11d63f) (movR64R64Effect 0x11d63f 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11d63f 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11d63f 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d642 [0x48, 0xC1, 0xE0, 0x06] (fun s => s.RIP = 0x11d642) (shlR64Effect 0x11d642 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x11d642 4 0 6).toInstrSpec (shl_r64_imm8_effect_step 0x11d642 0x48 0xe0 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11d646 [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x11d646) (leaR64Effect 0x11d646 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d646 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x11d646 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11d64a [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x11d64a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11d64a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d64a 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d64a 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11d64a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x11d64f [0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x01, 0x00, 0x00] (LoadPre 0x11d64f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x11d64f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d64f 1 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11d64f 1 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_r64_m64_effect_step 0x11d64f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11d657 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11d657) (movR64R64Effect 0x11d657 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11d657 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11d657 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d65a [0x48, 0xC1, 0xE0, 0x06] (fun s => s.RIP = 0x11d65a) (shlR64Effect 0x11d65a 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x11d65a 4 0 6).toInstrSpec (shl_r64_imm8_effect_step 0x11d65a 0x48 0xe0 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d65e [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x11d65e) (leaR64Effect 0x11d65e 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d65e 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x11d65e 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11d662 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x11d662 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11d662 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d662 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d662 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x11d662 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x11d667 [0x31, 0xED] (fun s => s.RIP = 0x11d667) (xorR32R32Effect 0x11d667 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11d667 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x11d667 0xed (by decide)) pre_rip
  have f15 : InstrSpec 0x11d669 [0x4C, 0x8D, 0xBC, 0x24, 0x90, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11d669) (leaR64Effect 0x11d669 15 (.sib 4 none 0 (.d32 0x490)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x11d669 15 (.sib 4 none 0 (.d32 0x490))).toInstrSpec (lea_r64_effect_step 0x11d669 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x490)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d671 [0x4C, 0x8D, 0xA4, 0x24, 0xD0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d671) (leaR64Effect 0x11d671 12 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x11d671 12 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (lea_r64_effect_step 0x11d671 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11d679 [0x4C, 0x8B, 0xAC, 0x24, 0xC0, 0x01, 0x00, 0x00] (LoadPre 0x11d679 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x11d679 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d679 13 (.sib 4 none 0 (.d32 0x1c0)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x11d679 13 (.sib 4 none 0 (.d32 0x1c0))).toInstrSpec (mov_r64_m64_effect_step 0x11d679 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x1c0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x11d681 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d681) (fun _ => nopEffect 0x11d681 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11d681 15).toInstrSpec (nop_m_effect_step 0x11d681 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d628) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d62d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d634) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d637) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d63f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 60), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d642) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 60), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d646) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 60), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d64a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 60), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d64f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 66), (1, 69), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d657) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 69), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d65a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 69), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d65e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 69), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d662) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 69), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d667) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 75), (1, 69), (4, 4), (5, 78), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d669) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 75), (1, 69), (4, 4), (5, 78), (9, 9), (10, 10), (11, 11), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d671) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 75), (1, 69), (4, 4), (5, 78), (9, 9), (10, 10), (11, 11), (12, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d679) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 75), (1, 69), (4, 4), (5, 78), (9, 9), (10, 10), (11, 11), (12, 82), (13, 84), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d681) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 75), (1, 69), (4, 4), (5, 78), (9, 9), (10, 10), (11, 11), (12, 82), (13, 84), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d690) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 87) (by decide) rfl

theorem block_l11d620 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d620 :=
  Rest.liftedBlock (rest_l11d620 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d620 x hx)

theorem rest_l11d690 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d690 bytes_l11d690) (entryMap (live .l11d690))
      2 0x11d690 bytes_l11d690 b_l11d690 := by
  have f0 : InstrSpec 0x11d690 [0x48, 0x39, 0x6C, 0x24, 0x60] (LoadPre 0x11d690 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11d690 + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d690 5 64 5 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 5, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x11d690 5 5 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (cmp_m64_r64_effect_step 0x11d690 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d695) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x11d695 4 0x20b2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11d690 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d690 :=
  Rest.liftedBlock (rest_l11d690 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d690 x hx)

theorem rest_l11d69b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d69b bytes_l11d69b) (entryMap (live .l11d69b))
      2 0x11d69b bytes_l11d69b b_l11d69b := by
  have f0 : InstrSpec 0x11d69b [0x48, 0x39, 0x6C, 0x24, 0x08] (LoadPre 0x11d69b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11d69b + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d69b 5 64 5 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 5, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x11d69b 5 5 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (cmp_m64_r64_effect_step 0x11d69b 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x11d6a0 4 0x20be) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11d69b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d69b :=
  Rest.liftedBlock (rest_l11d69b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d69b x hx)

theorem rest_l11d6a6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d6a6 bytes_l11d6a6) (entryMap (live .l11d6a6))
      6 0x11d6a6 bytes_l11d6a6 b_l11d6a6 := by
  have f0 : InstrSpec 0x11d6a6 [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11d6a6) (movR32Imm32Effect 0x11d6a6 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x11d6a6 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x11d6a6 0xba (by decide) 0x3c0) pre_rip
  have f1 : InstrSpec 0x11d6ab [0x4C, 0x8D, 0xB4, 0x24, 0x50, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x11d6ab) (leaR64Effect 0x11d6ab 14 (.sib 4 none 0 (.d32 0x850)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x11d6ab 14 (.sib 4 none 0 (.d32 0x850))).toInstrSpec (lea_r64_effect_step 0x11d6ab 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x850)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d6b3 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11d6b3) (movR64R64Effect 0x11d6b3 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d6b3 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11d6b3 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d6b6 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x11d6b6) (movR64R64Effect 0x11d6b6 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d6b6 6 13).toInstrSpec (mov_r64_r64_effect_step 0x11d6b6 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11d6b9 [0x48, 0x8D, 0x1D, 0x60, 0xD1, 0x00, 0x00] (fun s => s.RIP = 0x11d6b9) (leaR64Effect 0x11d6b9 3 (.rip 0xd160))
      [] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x11d6b9 3 (.rip 0xd160)).toInstrSpec (lea_r64_effect_step 0x11d6b9 0x48 (by decide) 3 (.rip 0xd160) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11d6c0 [0xFF, 0xD3] (GoesTo (CallPre 0x11d6c0 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6c2) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6c2)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x11d6c0 3 0x11d6c2).toInstrSpec (call_r64_effect_step 0x11d6c0 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6b6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6b9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 53), (3, 61), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 53), (3, 61), (4, 63), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l11d6a6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d6a6 :=
  Rest.liftedBlock (rest_l11d6a6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d6a6 x hx)

theorem rest_l11d6c2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d6c2 bytes_l11d6c2) (entryMap (live .l11d6c2))
      4 0x11d6c2 bytes_l11d6c2 b_l11d6c2 := by
  have f0 : InstrSpec 0x11d6c2 [0x49, 0x8D, 0xB5, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11d6c2) (leaR64Effect 0x11d6c2 6 (.base 13 (.d32 0x3c0)))
      [.gpr 13] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d6c2 6 (.base 13 (.d32 0x3c0))).toInstrSpec (lea_r64_effect_step 0x11d6c2 0x49 (by decide) 6 (.base 13 (.d32 0x3c0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d6c9 [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11d6c9) (movR32Imm32Effect 0x11d6c9 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x11d6c9 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x11d6c9 0xba (by decide) 0x3c0) pre_rip
  have f2 : InstrSpec 0x11d6ce [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11d6ce) (movR64R64Effect 0x11d6ce 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d6ce 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11d6ce 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d6d1 [0xFF, 0xD3] (GoesTo (CallPre 0x11d6d1 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6d3) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6d3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x11d6d1 3 0x11d6d3).toInstrSpec (call_r64_effect_step 0x11d6d1 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6ce) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6d1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11d6c2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d6c2 :=
  Rest.liftedBlock (rest_l11d6c2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d6c2 x hx)

theorem rest_l11d6d3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d6d3 bytes_l11d6d3) (entryMap (live .l11d6d3))
      5 0x11d6d3 bytes_l11d6d3 b_l11d6d3 := by
  have f0 : InstrSpec 0x11d6d3 [0x48, 0x8B, 0x9C, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x11d6d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d6d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d6d3 3 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11d6d3 3 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x11d6d3 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11d6db [0x0F, 0xB6, 0x54, 0x2B, 0x20] (LoadPre 0x11d6db (fun s => AddrMode.addr (.sib 3 (some 5) 0 (.d8 0x20)) s (0x11d6db + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11d6db 5 2 (.sib 3 (some 5) 0 (.d8 0x20)))
      [.gpr 3, .gpr 5] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x11d6db 5 2 (.sib 3 (some 5) 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x11d6db 2 (.sib 3 (some 5) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11d6e0 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d6e0) (movR64R64Effect 0x11d6e0 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d6e0 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d6e0 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d6e3 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11d6e3) (movR64R64Effect 0x11d6e3 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d6e3 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11d6e3 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11d6e6 [0xE8, 0x25, 0xEE, 0xFF, 0xFF] (PushPre 0x11d6e6 5) (callEffect (fun _ => 0x11c510) 0x11d6eb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d6e6 0x11c510 0x11d6eb).toInstrSpec (call_rel32_effect_step 0x11d6e6 0xffffee25 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6e0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 53), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6e3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 53), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 53), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c510) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11d6d3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d6d3 :=
  Rest.liftedBlock (rest_l11d6d3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d6d3 x hx)

theorem rest_l11d6eb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d6eb bytes_l11d6eb) (entryMap (live .l11d6eb))
      4 0x11d6eb bytes_l11d6eb b_l11d6eb := by
  have f0 : InstrSpec 0x11d6eb [0x4C, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d6eb) (leaR64Effect 0x11d6eb 14 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x11d6eb 14 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d6eb 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d6f3 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11d6f3) (movR64R64Effect 0x11d6f3 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d6f3 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11d6f3 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d6f6 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d6f6) (movR64R64Effect 0x11d6f6 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d6f6 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d6f6 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d6f9 [0xE8, 0x12, 0xCD, 0xFE, 0xFF] (PushPre 0x11d6f9 5) (callEffect (fun _ => 0x10a410) 0x11d6fe)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d6f9 0x10a410 0x11d6fe).toInstrSpec (call_rel32_effect_step 0x11d6f9 0xfffecd12 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d6f9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11d6eb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d6eb :=
  Rest.liftedBlock (rest_l11d6eb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d6eb x hx)

theorem rest_l11d6fe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d6fe bytes_l11d6fe) (entryMap (live .l11d6fe))
      4 0x11d6fe bytes_l11d6fe b_l11d6fe := by
  have f0 : InstrSpec 0x11d6fe [0x0F, 0xB6, 0x54, 0x2B, 0x41] (LoadPre 0x11d6fe (fun s => AddrMode.addr (.sib 3 (some 5) 0 (.d8 0x41)) s (0x11d6fe + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11d6fe 5 2 (.sib 3 (some 5) 0 (.d8 0x41)))
      [.gpr 3, .gpr 5] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x11d6fe 5 2 (.sib 3 (some 5) 0 (.d8 0x41))).toInstrSpec (movzx_r32_m8_effect_step 0x11d6fe 2 (.sib 3 (some 5) 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11d703 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d703) (movR64R64Effect 0x11d703 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d703 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d703 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d706 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11d706) (movR64R64Effect 0x11d706 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d706 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11d706 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d709 [0xE8, 0x02, 0xEE, 0xFF, 0xFF] (PushPre 0x11d709 5) (callEffect (fun _ => 0x11c510) 0x11d70e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d709 0x11c510 0x11d70e).toInstrSpec (call_rel32_effect_step 0x11d709 0xffffee02 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d703) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d706) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d709) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c510) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11d6fe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d6fe :=
  Rest.liftedBlock (rest_l11d6fe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d6fe x hx)

theorem rest_l11d70e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d70e bytes_l11d70e) (entryMap (live .l11d70e))
      3 0x11d70e bytes_l11d70e b_l11d70e := by
  have f0 : InstrSpec 0x11d70e [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11d70e) (movR64R64Effect 0x11d70e 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d70e 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11d70e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d711 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11d711) (movR64R64Effect 0x11d711 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11d711 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11d711 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d714 [0xE8, 0xF7, 0xCC, 0xFE, 0xFF] (PushPre 0x11d714 5) (callEffect (fun _ => 0x10a410) 0x11d719)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d714 0x10a410 0x11d719).toInstrSpec (call_rel32_effect_step 0x11d714 0xfffeccf7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d711) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d714) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l11d70e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d70e :=
  Rest.liftedBlock (rest_l11d70e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d70e x hx)

theorem rest_l11d719 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d719 bytes_l11d719) (entryMap (live .l11d719))
      4 0x11d719 bytes_l11d719 b_l11d719 := by
  have f0 : InstrSpec 0x11d719 [0x48, 0x83, 0xC5, 0x42] (fun s => s.RIP = 0x11d719) (addR64Imm8Effect 0x11d719 5 0x42)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11d719 5 0x42).toInstrSpec (add_r64_imm8_effect_step 0x11d719 0x48 0xc5 0x42 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d71d [0x49, 0x81, 0xC5, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x11d71d) (addR64Imm32Effect 0x11d71d 13 0x780)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11d71d 13 0x780).toInstrSpec (add_r64_imm32_effect_step 0x11d71d 0x49 0xc5 0x780 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d724 [0x48, 0x39, 0x6C, 0x24, 0x38] (LoadPre 0x11d724 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11d724 + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d724 5 64 5 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 5, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x11d724 5 5 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (cmp_m64_r64_effect_step 0x11d724 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d71d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d724) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d729) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x11d729 5 0xffffff61) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11d719 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d719 :=
  Rest.liftedBlock (rest_l11d719 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d719 x hx)

theorem rest_l11d72f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d72f bytes_l11d72f) (entryMap (live .l11d72f))
      1 0x11d72f bytes_l11d72f b_l11d72f := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x11d72f 0x17 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11d72f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d72f :=
  Rest.liftedBlock (rest_l11d72f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d72f x hx)

theorem rest_l11d731 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d731 bytes_l11d731) (entryMap (live .l11d731))
      4 0x11d731 bytes_l11d731 b_l11d731 := by
  have f0 : InstrSpec 0x11d731 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d731) (leaR64Effect 0x11d731 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d731 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (lea_r64_effect_step 0x11d731 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11d739 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d739) (movR32Imm32Effect 0x11d739 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d739 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11d739 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x11d73e [0x48, 0xC7, 0xC6, 0x58, 0x32, 0x20, 0x00] (fun s => s.RIP = 0x11d73e) (movR64Imm32Effect 0x11d73e 6 0x203258)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x11d73e 6 0x203258).toInstrSpec (mov_r64_imm32_effect_step 0x11d73e 0x48 0xc6 (by decide) (by decide) (by decide) 0x203258) pre_rip
  have f3 : InstrSpec 0x11d745 [0xF3, 0x48, 0xA5] (RepPre 0x11d745 (RepMovsqPre 0x11d745)) (repMovsqEffect 0x11d745)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11d745).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11d745 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (7, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d739) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (7, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d73e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (3, 3), (4, 4), (6, 57), (7, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d745) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d748) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l11d731 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d731 :=
  Rest.liftedBlock (rest_l11d731 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d731 x hx)

theorem rest_l11d748_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x11d748 bytes_l11d748) [(0, 88), (1, 84), (2, 55), (3, 3), (4, 4), (12, 86), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x11d7bc bytes_l11d748_1 b_l11d748_1 := by
  have f20 : InstrSpec 0x11d7bc [0x48, 0x83, 0xC0, 0xF9] (fun s => s.RIP = 0x11d7bc) (addR64Imm8Effect 0x11d7bc 0 0xf9)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11d7bc 0 0xf9).toInstrSpec (add_r64_imm8_effect_step 0x11d7bc 0x48 0xc0 0xf9 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x11d7c0 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00] (StorePre 0x11d7c0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x11d7c0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d7c0 0 (.sib 4 none 0 (.d32 0x1c8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d7c0 0 (.sib 4 none 0 (.d32 0x1c8))).toInstrSpec (mov_m64_r64_effect_step 0x11d7c0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1c8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 84), (2, 55), (3, 3), (4, 4), (12, 86), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7c0) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (1, 84), (2, 55), (3, 3), (4, 4), (12, 86), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7c8) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 93) (jmp_rel8_effect_step 0x11d7c8 0x25 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l11d748 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d748 bytes_l11d748) (entryMap (live .l11d748))
      23 0x11d748 bytes_l11d748 b_l11d748 := by
  have f0 : InstrSpec 0x11d748 [0x48, 0x8B, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x11d748 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d748 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d748 2 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11d748 2 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x11d748 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11d750 [0x48, 0x83, 0xC2, 0x40] (fun s => s.RIP = 0x11d750) (addR64Imm8Effect 0x11d750 2 0x40)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11d750 2 0x40).toInstrSpec (add_r64_imm8_effect_step 0x11d750 0x48 0xc2 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d754 [0x48, 0x8B, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x11d754 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11d754 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d754 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11d754 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_r64_m64_effect_step 0x11d754 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11d75c [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11d75c) (movR64R64Effect 0x11d75c 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11d75c 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11d75c 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11d75f [0x48, 0xC1, 0xE0, 0x06] (fun s => s.RIP = 0x11d75f) (shlR64Effect 0x11d75f 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x11d75f 4 0 6).toInstrSpec (shl_r64_imm8_effect_step 0x11d75f 0x48 0xe0 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11d763 [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x11d763) (leaR64Effect 0x11d763 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d763 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x11d763 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11d767 [0x48, 0x89, 0x84, 0x24, 0x60, 0x02, 0x00, 0x00] (StorePre 0x11d767 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x11d767 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d767 0 (.sib 4 none 0 (.d32 0x260)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d767 0 (.sib 4 none 0 (.d32 0x260))).toInstrSpec (mov_m64_r64_effect_step 0x11d767 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x260)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x11d76f [0x48, 0x8B, 0x8C, 0x24, 0xC0, 0x0C, 0x00, 0x00] (LoadPre 0x11d76f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc0)) s (0x11d76f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d76f 1 (.sib 4 none 0 (.d32 0xcc0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11d76f 1 (.sib 4 none 0 (.d32 0xcc0))).toInstrSpec (mov_r64_m64_effect_step 0x11d76f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xcc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11d777 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11d777) (movR64R64Effect 0x11d777 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11d777 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11d777 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11d77a [0x48, 0xC1, 0xE0, 0x06] (fun s => s.RIP = 0x11d77a) (shlR64Effect 0x11d77a 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x11d77a 4 0 6).toInstrSpec (shl_r64_imm8_effect_step 0x11d77a 0x48 0xe0 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11d77e [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x11d77e) (leaR64Effect 0x11d77e 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d77e 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x11d77e 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d782 [0x48, 0x89, 0x84, 0x24, 0x68, 0x02, 0x00, 0x00] (StorePre 0x11d782 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x268)) s (0x11d782 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d782 0 (.sib 4 none 0 (.d32 0x268)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d782 0 (.sib 4 none 0 (.d32 0x268))).toInstrSpec (mov_m64_r64_effect_step 0x11d782 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x268)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x11d78a [0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x01, 0x00, 0x00] (LoadPre 0x11d78a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x11d78a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d78a 1 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11d78a 1 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_r64_m64_effect_step 0x11d78a 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x11d792 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11d792) (movR64R64Effect 0x11d792 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11d792 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11d792 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11d795 [0x48, 0xC1, 0xE0, 0x06] (fun s => s.RIP = 0x11d795) (shlR64Effect 0x11d795 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x11d795 4 0 6).toInstrSpec (shl_r64_imm8_effect_step 0x11d795 0x48 0xe0 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11d799 [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x11d799) (leaR64Effect 0x11d799 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11d799 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x11d799 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11d79d [0x48, 0x89, 0x84, 0x24, 0x58, 0x02, 0x00, 0x00] (StorePre 0x11d79d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x258)) s (0x11d79d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d79d 0 (.sib 4 none 0 (.d32 0x258)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d79d 0 (.sib 4 none 0 (.d32 0x258))).toInstrSpec (mov_m64_r64_effect_step 0x11d79d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x258)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x11d7a5 [0xB9, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d7a5) (movR32Imm32Effect 0x11d7a5 5 1 0x20)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d7a5 5 1 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x11d7a5 0xb9 (by decide) 0x20) pre_rip
  have f18 : InstrSpec 0x11d7aa [0x4C, 0x8D, 0xA4, 0x24, 0x90, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11d7aa) (leaR64Effect 0x11d7aa 12 (.sib 4 none 0 (.d32 0x490)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x11d7aa 12 (.sib 4 none 0 (.d32 0x490))).toInstrSpec (lea_r64_effect_step 0x11d7aa 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x490)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11d7b2 [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x11d7b2) (movR64Imm64Effect 0x11d7b2 0 0xffffffffffff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x11d7b2 0 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x11d7b2 0x48 0xb8 (by decide) (by decide) 0xffffffffffff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d750) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d754) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d75c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d75f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 57), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d763) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 57), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d767) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 57), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d76f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 66), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d777) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 66), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d77a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 66), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d77e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 66), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d782) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 66), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d78a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 72), (1, 75), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d792) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 75), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d795) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 75), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d799) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 75), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d79d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 75), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7a5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 84), (2, 55), (3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7aa) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 81), (1, 84), (2, 55), (3, 3), (4, 4), (12, 86), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7b2) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 84), (2, 55), (3, 3), (4, 4), (12, 86), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7bc) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11d748_1 code

theorem block_l11d748 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d748 :=
  Rest.liftedBlock (rest_l11d748 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d748 x hx)

theorem rest_l11d7d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d7d0 bytes_l11d7d0) (entryMap (live .l11d7d0))
      6 0x11d7d0 bytes_l11d7d0 b_l11d7d0 := by
  have f0 : InstrSpec 0x11d7d0 [0x48, 0x8B, 0x8C, 0x24, 0x50, 0x02, 0x00, 0x00] (LoadPre 0x11d7d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x11d7d0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d7d0 1 (.sib 4 none 0 (.d32 0x250)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11d7d0 1 (.sib 4 none 0 (.d32 0x250))).toInstrSpec (mov_r64_m64_effect_step 0x11d7d0 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x250)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11d7d8 [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x11d7d8) (decR64Effect 0x11d7d8 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x11d7d8 1).toInstrSpec (dec_r64_effect_step 0x11d7d8 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d7db [0x48, 0x8B, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x11d7db (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d7db + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d7db 2 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11d7db 2 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x11d7db 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11d7e3 [0x48, 0xFF, 0xCA] (fun s => s.RIP = 0x11d7e3) (decR64Effect 0x11d7e3 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (decR64Effect_footprint 0x11d7e3 2).toInstrSpec (dec_r64_effect_step 0x11d7e3 0x48 0xca (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11d7e6 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x11d7e6) (testR64R64Effect 0x11d7e6 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11d7e6 1 1).toInstrSpec (test_r64_r64_effect_step 0x11d7e6 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 57), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7e3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 55), (2, 59), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 55), (2, 59), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x11d7e9 4 0x1ed5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11d7d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d7d0 :=
  Rest.liftedBlock (rest_l11d7d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d7d0 x hx)

theorem rest_l11d7ef [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d7ef bytes_l11d7ef) (entryMap (live .l11d7ef))
      5 0x11d7ef bytes_l11d7ef b_l11d7ef := by
  have f0 : InstrSpec 0x11d7ef [0x48, 0x89, 0x8C, 0x24, 0x50, 0x02, 0x00, 0x00] (StorePre 0x11d7ef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x11d7ef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d7ef 1 (.sib 4 none 0 (.d32 0x250)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d7ef 1 (.sib 4 none 0 (.d32 0x250))).toInstrSpec (mov_m64_r64_effect_step 0x11d7ef 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x250)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11d7f7 [0x48, 0x89, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x11d7f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d7f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d7f7 2 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d7f7 2 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x11d7f7 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11d7ff [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d7ff) (movR32Imm32Effect 0x11d7ff 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11d7ff 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x11d7ff 0xb9 (by decide) 0x4) pre_rip
  have f3 : InstrSpec 0x11d804 [0x48, 0xBD, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11d804) (movR64Imm64Effect 0x11d804 5 0x1000003d10)
      [] [] [.reg 5, .rip] :=
    (movR64Imm64Effect_footprint 0x11d804 5 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x11d804 0x48 0xbd (by decide) (by decide) 0x1000003d10) pre_rip
  have f4 : InstrSpec 0x11d80e [0x66, 0x90] (fun s => s.RIP = 0x11d80e) (fun _ => nopEffect 0x11d80e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11d80e 2).toInstrSpec (nop_66_effect_step 0x11d80e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7f7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d7ff) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d804) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (5, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d80e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (5, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d810) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l11d7ef [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d7ef :=
  Rest.liftedBlock (rest_l11d7ef code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d7ef x hx)

theorem rest_l11d810 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d810 bytes_l11d810) (entryMap (live .l11d810))
      4 0x11d810 bytes_l11d810 b_l11d810 := by
  have f0 : InstrSpec 0x11d810 [0x89, 0x8C, 0x24, 0xBC, 0x01, 0x00, 0x00] (StorePre 0x11d810 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1bc)) s (0x11d810 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x11d810 1 (.sib 4 none 0 (.d32 0x1bc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x11d810 1 (.sib 4 none 0 (.d32 0x1bc))).toInstrSpec (mov_m32_r32_low_effect_step 0x11d810 1 (.sib 4 none 0 (.d32 0x1bc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11d817 [0x48, 0x8D, 0xBC, 0x24, 0x50, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x11d817) (leaR64Effect 0x11d817 7 (.sib 4 none 0 (.d32 0x850)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11d817 7 (.sib 4 none 0 (.d32 0x850))).toInstrSpec (lea_r64_effect_step 0x11d817 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x850)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11d81f [0x48, 0x8D, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d81f) (leaR64Effect 0x11d81f 6 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d81f 6 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (lea_r64_effect_step 0x11d81f 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11d827 [0xE8, 0xC4, 0x6D, 0xFF, 0xFF] (PushPre 0x11d827 5) (callEffect (fun _ => 0x1145f0) 0x11d82c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d827 0x1145f0 0x11d82c).toInstrSpec (call_rel32_effect_step 0x11d827 0xffff6dc4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d817) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 54), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d81f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d827) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145f0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 60) (by decide) (by decide) rfl rfl

theorem block_l11d810 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d810 :=
  Rest.liftedBlock (rest_l11d810 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d810 x hx)

theorem rest_l11d82c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11d82c bytes_l11d82c) (entryMap (live .l11d82c))
      13 0x11d82c bytes_l11d82c b_l11d82c := by
  have f0 : InstrSpec 0x11d82c [0x48, 0x8B, 0x84, 0x24, 0x50, 0x08, 0x00, 0x00] (LoadPre 0x11d82c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x850)) s (0x11d82c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d82c 0 (.sib 4 none 0 (.d32 0x850)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d82c 0 (.sib 4 none 0 (.d32 0x850))).toInstrSpec (mov_r64_m64_effect_step 0x11d82c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x850)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11d834 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x11d834 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11d834 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d834 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d834 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x11d834 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11d83c [0x48, 0x8B, 0x84, 0x24, 0x58, 0x08, 0x00, 0x00] (LoadPre 0x11d83c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x858)) s (0x11d83c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d83c 0 (.sib 4 none 0 (.d32 0x858)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d83c 0 (.sib 4 none 0 (.d32 0x858))).toInstrSpec (mov_r64_m64_effect_step 0x11d83c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x858)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11d844 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x11d844 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11d844 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d844 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d844 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x11d844 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11d849 [0x48, 0x8B, 0x84, 0x24, 0x60, 0x08, 0x00, 0x00] (LoadPre 0x11d849 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x860)) s (0x11d849 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d849 0 (.sib 4 none 0 (.d32 0x860)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d849 0 (.sib 4 none 0 (.d32 0x860))).toInstrSpec (mov_r64_m64_effect_step 0x11d849 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x860)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11d851 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x11d851 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11d851 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d851 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d851 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x11d851 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11d856 [0x48, 0x8B, 0x84, 0x24, 0x68, 0x08, 0x00, 0x00] (LoadPre 0x11d856 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x868)) s (0x11d856 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d856 0 (.sib 4 none 0 (.d32 0x868)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d856 0 (.sib 4 none 0 (.d32 0x868))).toInstrSpec (mov_r64_m64_effect_step 0x11d856 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x868)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x11d85e [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x11d85e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11d85e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d85e 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d85e 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x11d85e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11d863 [0x48, 0x8B, 0x84, 0x24, 0x70, 0x08, 0x00, 0x00] (LoadPre 0x11d863 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x870)) s (0x11d863 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d863 0 (.sib 4 none 0 (.d32 0x870)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11d863 0 (.sib 4 none 0 (.d32 0x870))).toInstrSpec (mov_r64_m64_effect_step 0x11d863 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x870)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11d86b [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x11d86b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11d86b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d86b 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11d86b 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x11d86b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11d870 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11d870) (movR64R64Effect 0x11d870 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11d870 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11d870 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11d873 [0x48, 0x8D, 0xB4, 0x24, 0x78, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11d873) (leaR64Effect 0x11d873 6 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11d873 6 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (lea_r64_effect_step 0x11d873 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11d87b [0xE8, 0x70, 0x6D, 0xFF, 0xFF] (PushPre 0x11d87b 5) (callEffect (fun _ => 0x1145f0) 0x11d880)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11d87b 0x1145f0 0x11d880).toInstrSpec (call_rel32_effect_step 0x11d87b 0xffff6d70 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d834) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d83c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d844) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d849) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d851) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d856) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d85e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d863) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d86b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d870) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d873) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11d87b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 65), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145f0) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 74) (by decide) (by decide) rfl rfl

theorem block_l11d82c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11d82c :=
  Rest.liftedBlock (rest_l11d82c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11d82c x hx)

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

theorem_by block_l11c880_eval :
    program.runBlock (dialect code) ⟨.l11c880, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c8d2_eval :
    program.runBlock (dialect code) ⟨.l11c8d2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c920_eval :
    program.runBlock (dialect code) ⟨.l11c920, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c95d_eval :
    program.runBlock (dialect code) ⟨.l11c95d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c977_eval :
    program.runBlock (dialect code) ⟨.l11c977, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c989_eval :
    program.runBlock (dialect code) ⟨.l11c989, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c9a3_eval :
    program.runBlock (dialect code) ⟨.l11c9a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c9c0_eval :
    program.runBlock (dialect code) ⟨.l11c9c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c9d2_eval :
    program.runBlock (dialect code) ⟨.l11c9d2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c9e7_eval :
    program.runBlock (dialect code) ⟨.l11c9e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11ca7f_eval :
    program.runBlock (dialect code) ⟨.l11ca7f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11cb3c_eval :
    program.runBlock (dialect code) ⟨.l11cb3c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11cbf4_eval :
    program.runBlock (dialect code) ⟨.l11cbf4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11cc3e_eval :
    program.runBlock (dialect code) ⟨.l11cc3e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11ccfd_eval :
    program.runBlock (dialect code) ⟨.l11ccfd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11cf0d_eval :
    program.runBlock (dialect code) ⟨.l11cf0d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11cf51_eval :
    program.runBlock (dialect code) ⟨.l11cf51, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11cfae_eval :
    program.runBlock (dialect code) ⟨.l11cfae, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d003_eval :
    program.runBlock (dialect code) ⟨.l11d003, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d058_eval :
    program.runBlock (dialect code) ⟨.l11d058, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d0ad_eval :
    program.runBlock (dialect code) ⟨.l11d0ad, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d102_eval :
    program.runBlock (dialect code) ⟨.l11d102, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d157_eval :
    program.runBlock (dialect code) ⟨.l11d157, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d2e1_eval :
    program.runBlock (dialect code) ⟨.l11d2e1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d31e_eval :
    program.runBlock (dialect code) ⟨.l11d31e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d371_eval :
    program.runBlock (dialect code) ⟨.l11d371, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d3bc_eval :
    program.runBlock (dialect code) ⟨.l11d3bc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d407_eval :
    program.runBlock (dialect code) ⟨.l11d407, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d452_eval :
    program.runBlock (dialect code) ⟨.l11d452, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d49d_eval :
    program.runBlock (dialect code) ⟨.l11d49d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d4e8_eval :
    program.runBlock (dialect code) ⟨.l11d4e8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d514_eval :
    program.runBlock (dialect code) ⟨.l11d514, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d535_eval :
    program.runBlock (dialect code) ⟨.l11d535, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d546_eval :
    program.runBlock (dialect code) ⟨.l11d546, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d556_eval :
    program.runBlock (dialect code) ⟨.l11d556, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d566_eval :
    program.runBlock (dialect code) ⟨.l11d566, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d579_eval :
    program.runBlock (dialect code) ⟨.l11d579, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d620_eval :
    program.runBlock (dialect code) ⟨.l11d620, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d690_eval :
    program.runBlock (dialect code) ⟨.l11d690, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d69b_eval :
    program.runBlock (dialect code) ⟨.l11d69b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d6a6_eval :
    program.runBlock (dialect code) ⟨.l11d6a6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d6c2_eval :
    program.runBlock (dialect code) ⟨.l11d6c2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d6d3_eval :
    program.runBlock (dialect code) ⟨.l11d6d3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d6eb_eval :
    program.runBlock (dialect code) ⟨.l11d6eb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d6fe_eval :
    program.runBlock (dialect code) ⟨.l11d6fe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d70e_eval :
    program.runBlock (dialect code) ⟨.l11d70e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d719_eval :
    program.runBlock (dialect code) ⟨.l11d719, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d72f_eval :
    program.runBlock (dialect code) ⟨.l11d72f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d731_eval :
    program.runBlock (dialect code) ⟨.l11d731, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d748_eval :
    program.runBlock (dialect code) ⟨.l11d748, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d7d0_eval :
    program.runBlock (dialect code) ⟨.l11d7d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d7ef_eval :
    program.runBlock (dialect code) ⟨.l11d7ef, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d810_eval :
    program.runBlock (dialect code) ⟨.l11d810, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11d82c_eval :
    program.runBlock (dialect code) ⟨.l11d82c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
