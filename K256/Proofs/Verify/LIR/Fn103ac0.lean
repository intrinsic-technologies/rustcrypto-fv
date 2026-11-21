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

theorem rest_l103ac0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ac0 bytes_l103ac0) (entryMap (live .l103ac0))
      17 0x103ac0 bytes_l103ac0 b_l103ac0 := by
  have f0 : InstrSpec 0x103ac0 [0x41, 0x56] (PushPre 0x103ac0 2) (pushR64Effect 0x103ac0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103ac0 2 14).toInstrSpec (push_r64_rex_effect_step 0x103ac0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103ac2 [0x53] (PushPre 0x103ac2 1) (pushR64Effect 0x103ac2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103ac2 1 3).toInstrSpec (push_r64_effect_step 0x103ac2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103ac3 [0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103ac3) (subR64Imm32Effect 0x103ac3 4 0xa8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x103ac3 4 0xa8).toInstrSpec (sub_r64_imm32_effect_step 0x103ac3 0x48 0xec 0xa8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103aca [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x103aca) (movR64R64Effect 0x103aca 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103aca 14 6).toInstrSpec (mov_r64_r64_effect_step 0x103aca 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103acd [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x103acd) (movR64R64Effect 0x103acd 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103acd 3 7).toInstrSpec (mov_r64_r64_effect_step 0x103acd 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103ad0 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x103ad0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x103ad0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103ad0 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103ad0 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x103ad0 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103ad4 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x103ad4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103ad4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103ad4 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ad4 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x103ad4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103ad9 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x103ad9 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x103ad9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103ad9 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103ad9 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103ad9 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x103add [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x103add 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103add + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103add 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103add 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x103add 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103ae2 [0x48, 0x8B, 0x06] (LoadPre 0x103ae2 (fun s => AddrMode.addr (.base 6 .none) s (0x103ae2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x103ae2 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103ae2 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103ae2 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x103ae5 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x103ae5 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x103ae5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103ae5 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103ae5 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x103ae5 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x103ae9 [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x103ae9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103ae9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103ae9 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ae9 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x103ae9 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103aee [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x103aee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103aee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103aee 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103aee 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x103aee 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x103af3 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x103af3) (leaR64Effect 0x103af3 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103af3 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103af3 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x103af8 [0x48, 0x8D, 0x74, 0x24, 0x48] (fun s => s.RIP = 0x103af8) (leaR64Effect 0x103af8 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103af8 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x103af8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x103afd [0xBA, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103afd) (movR32Imm32Effect 0x103afd 5 2 0x20)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x103afd 5 2 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x103afd 0xba (by decide) 0x20) pre_rip
  have f16 : InstrSpec 0x103b02 [0xE8, 0x29, 0x3C, 0x00, 0x00] (PushPre 0x103b02 5) (callEffect (fun _ => 0x107730) 0x103b07)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103b02 0x107730 0x103b07).toInstrSpec (call_rel32_effect_step 0x103b02 0x3c29 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ac2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ac3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aca) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103acd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ad0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ad4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ad9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103add) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ae2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ae5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 71), (3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ae9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 69), (1, 71), (3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aee) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 71), (3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103af3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 71), (3, 61), (4, 57), (5, 5), (6, 6), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103af8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 71), (3, 61), (4, 57), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103afd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 69), (1, 71), (2, 79), (3, 61), (4, 57), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b02) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 69), (1, 71), (2, 79), (3, 61), (4, 81), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107730) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l103ac0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ac0 :=
  Rest.liftedBlock (rest_l103ac0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ac0 x hx)

theorem rest_l103b07 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103b07 bytes_l103b07) (entryMap (live .l103b07))
      2 0x103b07 bytes_l103b07 b_l103b07 := by
  have f0 : InstrSpec 0x103b07 [0x83, 0x7C, 0x24, 0x08, 0x01] (LoadPre 0x103b07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103b07 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x103b07 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x103b07 5 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x103b07 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b0c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x103b0c 4 0x13b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103b07 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103b07 :=
  Rest.liftedBlock (rest_l103b07 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103b07 x hx)

theorem rest_l103b12 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103b12 bytes_l103b12) (entryMap (live .l103b12))
      20 0x103b12 bytes_l103b12 b_l103b12 := by
  have f0 : InstrSpec 0x103b12 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x103b12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103b12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b12 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103b12 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103b12 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103b17 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x103b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103b17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b17 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103b17 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x103b17 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103b1c [0x48, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x103b1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103b1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b1c 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103b1c 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103b1c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103b21 [0x48, 0x89, 0x54, 0x24, 0x78] (StorePre 0x103b21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x103b21 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b21 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b21 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x103b21 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103b26 [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x103b26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103b26 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b26 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103b26 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x103b26 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103b2b [0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x103b2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x103b2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103b2b 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b2b 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x103b2b 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103b33 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x103b33 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x103b33 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b33 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b33 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x103b33 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103b38 [0x48, 0x89, 0x4C, 0x24, 0x70] (StorePre 0x103b38 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x103b38 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b38 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b38 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x103b38 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103b3d [0x49, 0x8B, 0x46, 0x38] (LoadPre 0x103b3d (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x103b3d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b3d 0 (.base 14 (.d8 0x38)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103b3d 0 (.base 14 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x103b3d 0x49 (by decide) 0 (.base 14 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103b41 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x103b41 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103b41 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b41 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b41 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x103b41 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x103b46 [0x49, 0x8B, 0x46, 0x30] (LoadPre 0x103b46 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x103b46 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b46 0 (.base 14 (.d8 0x30)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103b46 0 (.base 14 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x103b46 0x49 (by decide) 0 (.base 14 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x103b4a [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x103b4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103b4a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b4a 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b4a 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x103b4a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103b4f [0x49, 0x8B, 0x46, 0x20] (LoadPre 0x103b4f (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x103b4f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b4f 0 (.base 14 (.d8 0x20)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103b4f 0 (.base 14 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103b4f 0x49 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x103b53 [0x49, 0x8B, 0x4E, 0x28] (LoadPre 0x103b53 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x103b53 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b53 1 (.base 14 (.d8 0x28)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103b53 1 (.base 14 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x103b53 0x49 (by decide) 1 (.base 14 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x103b57 [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x103b57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103b57 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b57 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b57 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x103b57 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x103b5c [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x103b5c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103b5c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b5c 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b5c 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x103b5c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x103b61 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x103b61) (leaR64Effect 0x103b61 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103b61 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103b61 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x103b66 [0x48, 0x8D, 0x74, 0x24, 0x48] (fun s => s.RIP = 0x103b66) (leaR64Effect 0x103b66 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103b66 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x103b66 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x103b6b [0xBA, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103b6b) (movR32Imm32Effect 0x103b6b 5 2 0x20)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x103b6b 5 2 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x103b6b 0xba (by decide) 0x20) pre_rip
  have f19 : InstrSpec 0x103b70 [0xE8, 0xBB, 0x3B, 0x00, 0x00] (PushPre 0x103b70 5) (callEffect (fun _ => 0x107730) 0x103b75)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103b70 0x107730 0x103b75).toInstrSpec (call_rel32_effect_step 0x103b70 0x3bbb (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b1c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b21) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b26) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b2b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b33) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b38) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b3d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b41) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b46) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b4a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b4f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b53) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b57) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b5c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b61) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (7, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b66) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (6, 79), (7, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b6b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (2, 81), (3, 3), (4, 4), (5, 5), (6, 79), (7, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b70) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (2, 81), (3, 3), (4, 83), (5, 5), (6, 79), (7, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107730) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l103b12 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103b12 :=
  Rest.liftedBlock (rest_l103b12 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103b12 x hx)

theorem rest_l103b75 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103b75 bytes_l103b75) (entryMap (live .l103b75))
      2 0x103b75 bytes_l103b75 b_l103b75 := by
  have f0 : InstrSpec 0x103b75 [0x83, 0x7C, 0x24, 0x08, 0x01] (LoadPre 0x103b75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103b75 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x103b75 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x103b75 5 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x103b75 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b7a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x103b7a 4 0xcd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103b75 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103b75 :=
  Rest.liftedBlock (rest_l103b75 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103b75 x hx)

theorem rest_l103b80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103b80 bytes_l103b80) (entryMap (live .l103b80))
      17 0x103b80 bytes_l103b80 b_l103b80 := by
  have f0 : InstrSpec 0x103b80 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x103b80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103b80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b80 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103b80 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103b80 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103b85 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x103b85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103b85 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b85 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103b85 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x103b85 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103b8a [0x48, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x103b8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103b8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b8a 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103b8a 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103b8a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103b8f [0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x103b8f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x103b8f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103b8f 2 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b8f 2 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x103b8f 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103b97 [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x103b97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103b97 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b97 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103b97 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x103b97 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103b9c [0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x103b9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x103b9c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103b9c 2 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103b9c 2 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x103b9c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103ba4 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x103ba4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x103ba4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103ba4 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ba4 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x103ba4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103bac [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x103bac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x103bac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103bac 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103bac 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x103bac 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103bb4 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103bb4 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103bb4 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bb4 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103bb4 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103bb4 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103bbd [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103bbd 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103bbd + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bbd (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103bbd (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103bbd 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x103bc6 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103bc6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103bc6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bc6 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103bc6 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103bc6 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x103bcf [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103bcf 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103bcf + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bcf (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103bcf (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103bcf 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103bd8 [0x48, 0x8D, 0x7C, 0x24, 0x68] (fun s => s.RIP = 0x103bd8) (leaR64Effect 0x103bd8 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103bd8 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x103bd8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x103bdd [0x48, 0x8D, 0x54, 0x24, 0x08] (fun s => s.RIP = 0x103bdd) (leaR64Effect 0x103bdd 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x103bdd 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103bdd 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x103be2 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103be2) (movR32Imm32Effect 0x103be2 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x103be2 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x103be2 0xbe (by decide) 0x4) pre_rip
  have f15 : InstrSpec 0x103be7 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103be7) (movR32Imm32Effect 0x103be7 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x103be7 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x103be7 0xb9 (by decide) 0x4) pre_rip
  have f16 : InstrSpec 0x103bec [0xE8, 0x5F, 0x43, 0x02, 0x00] (PushPre 0x103bec 5) (callEffect (fun _ => 0x127f50) 0x103bf1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103bec 0x127f50 0x103bf1).toInstrSpec (call_rel32_effect_step 0x103bec 0x2435f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b85) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b8a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b8f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b97) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b9c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ba4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bac) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bb4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bbd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bc6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bcf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bd8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bdd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 55), (2, 71), (3, 3), (4, 4), (5, 5), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103be2) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 55), (2, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103be7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 75), (2, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bec) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 75), (2, 71), (3, 3), (4, 77), (5, 5), (6, 73), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l103b80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103b80 :=
  Rest.liftedBlock (rest_l103b80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103b80 x hx)

theorem rest_l103bf1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103bf1 bytes_l103bf1) (entryMap (live .l103bf1))
      3 0x103bf1 bytes_l103bf1 b_l103bf1 := by
  have f0 : InstrSpec 0x103bf1 [0x24, 0x01] (fun s => s.RIP = 0x103bf1) (andAlImm8Effect 0x103bf1 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x103bf1 0x1).toInstrSpec (and_al_imm8_effect_step 0x103bf1 0x1) pre_rip
  have f1 : InstrSpec 0x103bf3 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x103bf3) (movzxR32R8Effect 0x103bf3 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x103bf3 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x103bf3 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103bf6 [0xE8, 0x55, 0x41, 0x02, 0x00] (PushPre 0x103bf6 5) (callEffect (fun _ => 0x127d50) 0x103bfb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103bf6 0x127d50 0x103bfb).toInstrSpec (call_rel32_effect_step 0x103bf6 0x24155 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bf3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bf6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l103bf1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103bf1 :=
  Rest.liftedBlock (rest_l103bf1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103bf1 x hx)

theorem rest_l103bfb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103bfb bytes_l103bfb) (entryMap (live .l103bfb))
      2 0x103bfb bytes_l103bfb b_l103bfb := by
  have f0 : InstrSpec 0x103bfb [0x84, 0xC0] (fun s => s.RIP = 0x103bfb) (testR8R8Effect 0x103bfb 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x103bfb 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x103bfb 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bfd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103bfd 5 0x4e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103bfb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103bfb :=
  Rest.liftedBlock (rest_l103bfb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103bfb x hx)

theorem rest_l103bff [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103bff bytes_l103bff) (entryMap (live .l103bff))
      9 0x103bff bytes_l103bff b_l103bff := by
  have f0 : InstrSpec 0x103bff [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103bff 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103bff + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bff (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103bff (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103bff 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103c08 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103c08 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103c08 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103c08 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103c08 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103c08 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103c11 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103c11 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103c11 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103c11 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103c11 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103c11 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x103c1a [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103c1a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103c1a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103c1a (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103c1a (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103c1a 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103c23 [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103c23) (leaR64Effect 0x103c23 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103c23 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x103c23 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103c2b [0x48, 0x8D, 0x54, 0x24, 0x08] (fun s => s.RIP = 0x103c2b) (leaR64Effect 0x103c2b 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x103c2b 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103c2b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103c30 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103c30) (movR32Imm32Effect 0x103c30 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x103c30 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x103c30 0xbe (by decide) 0x4) pre_rip
  have f7 : InstrSpec 0x103c35 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103c35) (movR32Imm32Effect 0x103c35 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x103c35 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x103c35 0xb9 (by decide) 0x4) pre_rip
  have f8 : InstrSpec 0x103c3a [0xE8, 0x11, 0x43, 0x02, 0x00] (PushPre 0x103c3a 5) (callEffect (fun _ => 0x127f50) 0x103c3f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103c3a 0x127f50 0x103c3f).toInstrSpec (call_rel32_effect_step 0x103c3a 0x24311 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c08) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c11) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c1a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c23) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c2b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c30) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c35) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c3a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 59), (3, 3), (4, 65), (5, 5), (6, 61), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l103bff [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103bff :=
  Rest.liftedBlock (rest_l103bff code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103bff x hx)

theorem rest_l103c3f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c3f bytes_l103c3f) (entryMap (live .l103c3f))
      3 0x103c3f bytes_l103c3f b_l103c3f := by
  have f0 : InstrSpec 0x103c3f [0x24, 0x01] (fun s => s.RIP = 0x103c3f) (andAlImm8Effect 0x103c3f 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x103c3f 0x1).toInstrSpec (and_al_imm8_effect_step 0x103c3f 0x1) pre_rip
  have f1 : InstrSpec 0x103c41 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x103c41) (movzxR32R8Effect 0x103c41 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x103c41 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x103c41 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103c44 [0xE8, 0x07, 0x41, 0x02, 0x00] (PushPre 0x103c44 5) (callEffect (fun _ => 0x127d50) 0x103c49)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103c44 0x127d50 0x103c49).toInstrSpec (call_rel32_effect_step 0x103c44 0x24107 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c41) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c44) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l103c3f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c3f :=
  Rest.liftedBlock (rest_l103c3f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c3f x hx)

theorem rest_l103c49 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c49 bytes_l103c49) (entryMap (live .l103c49))
      2 0x103c49 bytes_l103c49 b_l103c49 := by
  have f0 : InstrSpec 0x103c49 [0x84, 0xC0] (fun s => s.RIP = 0x103c49) (testR8R8Effect 0x103c49 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x103c49 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x103c49 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c4b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103c4b 4 0x1d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103c49 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c49 :=
  Rest.liftedBlock (rest_l103c49 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c49 x hx)

theorem rest_l103c4d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c4d bytes_l103c4d) (entryMap (live .l103c4d))
      2 0x103c4d bytes_l103c4d b_l103c4d := by
  have f0 : InstrSpec 0x103c4d [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103c4d 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103c4d + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x103c4d (.base 3 (.d8 0x8)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103c4d (.base 3 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103c4d 0x48 (by decide) (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103c55 [0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x103c55 7 (fun s => AddrMode.addr (.base 3 .none) s (0x103c55 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x103c55 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103c55 (.base 3 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x103c55 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c55) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c5c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l103c4d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c4d :=
  Rest.liftedBlock (rest_l103c4d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c4d x hx)

theorem rest_l103c5c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c5c bytes_l103c5c) (entryMap (live .l103c5c))
      5 0x103c5c bytes_l103c5c b_l103c5c := by
  have f0 : InstrSpec 0x103c5c [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x103c5c) (movR64R64Effect 0x103c5c 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x103c5c 0 3).toInstrSpec (mov_r64_r64_effect_step 0x103c5c 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103c5f [0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103c5f) (addR64Imm32Effect 0x103c5f 4 0xa8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x103c5f 4 0xa8).toInstrSpec (add_r64_imm32_effect_step 0x103c5f 0x48 0xc4 0xa8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103c66 [0x5B] (PopPre 0x103c66) (popR64Effect 0x103c66 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103c66 1 3).toInstrSpec (pop_r64_effect_step 0x103c66 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103c67 [0x41, 0x5E] (PopPre 0x103c67) (popR64Effect 0x103c67 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103c67 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103c67 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103c69 [0xC3] (RetPre 0x103c69) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103c69).toInstrSpec (ret_effect_step 0x103c69) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c5f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c66) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c67) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c69) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l103c5c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c5c :=
  Rest.liftedBlock (rest_l103c5c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c5c x hx)

theorem rest_l103c6a_1 [Bindings] (code : CodeMap) :
    Rest (n := 81) code lifted (codeRange 0x103c6a bytes_l103c6a) [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x103cd9 bytes_l103c6a_1 b_l103c6a_1 := by
  have f20 : InstrSpec 0x103cd9 [0x48, 0x89, 0x43, 0x20] (StorePre 0x103cd9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x103cd9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cd9 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cd9 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x103cd9 0x48 (by decide) 0 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x103cdd [0x48, 0x89, 0x4B, 0x18] (StorePre 0x103cdd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x103cdd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cdd 1 (.base 3 (.d8 0x18)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cdd 1 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x103cdd 0x48 (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x103ce1 [0x48, 0x89, 0x73, 0x10] (StorePre 0x103ce1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103ce1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ce1 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ce1 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103ce1 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x103ce5 [0x48, 0x89, 0x53, 0x08] (StorePre 0x103ce5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103ce5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ce5 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ce5 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103ce5 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x103ce9 [0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103ce9 7 (fun s => AddrMode.addr (.base 3 .none) s (0x103ce9 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x103ce9 (.base 3 .none) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103ce9 (.base 3 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103ce9 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cdd) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ce1) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ce5) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ce9) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cf0) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 86) (jmp_rel32_effect_step 0x103cf0 0xffffff67 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l103c6a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c6a bytes_l103c6a) (entryMap (live .l103c6a))
      26 0x103c6a bytes_l103c6a b_l103c6a := by
  have f0 : InstrSpec 0x103c6a [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x103c6a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x103c6a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103c6a 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103c6a 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x103c6a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103c72 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x103c72 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103c72 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103c72 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c72 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x103c72 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103c77 [0x48, 0x8B, 0x4C, 0x24, 0x78] (LoadPre 0x103c77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x103c77 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c77 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103c77 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x103c77 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103c7c [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x103c7c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103c7c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103c7c 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c7c 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x103c7c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103c81 [0x48, 0x8B, 0x54, 0x24, 0x68] (LoadPre 0x103c81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x103c81 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c81 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103c81 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x103c81 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103c86 [0x48, 0x8B, 0x74, 0x24, 0x70] (LoadPre 0x103c86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x103c86 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c86 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103c86 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x103c86 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103c8b [0x48, 0x89, 0x74, 0x24, 0x10] (StorePre 0x103c8b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103c8b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103c8b 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c8b 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103c8b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103c90 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x103c90 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103c90 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103c90 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103c90 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103c90 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103c95 [0x48, 0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x103c95 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x103c95 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103c95 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103c95 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x103c95 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103c9d [0x4C, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x103c9d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x103c9d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103c9d 8 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x103c9d 8 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x103c9d 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x103ca5 [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x103ca5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103ca5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103ca5 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ca5 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x103ca5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x103caa [0x4C, 0x89, 0x44, 0x24, 0x30] (StorePre 0x103caa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103caa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103caa 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103caa 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x103caa 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103caf [0x4C, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x103caf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x103caf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103caf 9 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x103caf 9 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x103caf 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x103cb7 [0x4C, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x103cb7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103cb7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103cb7 9 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cb7 9 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x103cb7 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x103cbc [0x4C, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x103cbc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x103cbc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103cbc 10 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x103cbc 10 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x103cbc 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x103cc4 [0x4C, 0x89, 0x54, 0x24, 0x40] (StorePre 0x103cc4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103cc4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103cc4 10 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cc4 10 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x103cc4 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x103cc9 [0x4C, 0x89, 0x53, 0x40] (StorePre 0x103cc9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x103cc9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cc9 10 (.base 3 (.d8 0x40)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cc9 10 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x103cc9 0x4c (by decide) 2 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x103ccd [0x4C, 0x89, 0x4B, 0x38] (StorePre 0x103ccd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x103ccd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ccd 9 (.base 3 (.d8 0x38)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103ccd 9 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x103ccd 0x4c (by decide) 1 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x103cd1 [0x4C, 0x89, 0x43, 0x30] (StorePre 0x103cd1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x103cd1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cd1 8 (.base 3 (.d8 0x30)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cd1 8 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x103cd1 0x4c (by decide) 0 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x103cd5 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x103cd5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x103cd5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cd5 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103cd5 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x103cd5 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c72) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c77) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c7c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c81) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c86) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c8b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c90) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c95) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c9d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ca5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103caa) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103caf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cb7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cbc) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cc4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cc9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ccd) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cd1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cd5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103cd9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l103c6a_1 code

theorem block_l103c6a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c6a :=
  Rest.liftedBlock (rest_l103c6a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c6a x hx)

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

theorem_by block_l103ac0_eval :
    program.runBlock (dialect code) ⟨.l103ac0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103b07_eval :
    program.runBlock (dialect code) ⟨.l103b07, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103b12_eval :
    program.runBlock (dialect code) ⟨.l103b12, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103b75_eval :
    program.runBlock (dialect code) ⟨.l103b75, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103b80_eval :
    program.runBlock (dialect code) ⟨.l103b80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103bf1_eval :
    program.runBlock (dialect code) ⟨.l103bf1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103bfb_eval :
    program.runBlock (dialect code) ⟨.l103bfb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103bff_eval :
    program.runBlock (dialect code) ⟨.l103bff, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c3f_eval :
    program.runBlock (dialect code) ⟨.l103c3f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c49_eval :
    program.runBlock (dialect code) ⟨.l103c49, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c4d_eval :
    program.runBlock (dialect code) ⟨.l103c4d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c5c_eval :
    program.runBlock (dialect code) ⟨.l103c5c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c6a_eval :
    program.runBlock (dialect code) ⟨.l103c6a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
