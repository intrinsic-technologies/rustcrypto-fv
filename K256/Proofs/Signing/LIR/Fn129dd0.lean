import K256.Proofs.Signing.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

theorem rest_l129dd0_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x129dd0 bytes_l129dd0) [(0, 83), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x129e1b bytes_l129dd0_1 b_l129dd0_1 := by
  have f20 : InstrSpec 0x129e1b [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x129e1b) (xorR32R32Effect 0x129e1b 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129e1b 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x129e1b 0x45 0xff (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x129e1e [0x31, 0xC0] (fun s => s.RIP = 0x129e1e) (xorR32R32Effect 0x129e1e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129e1e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x129e1e 0xc0 (by decide)) pre_rip
  have f22 : InstrSpec 0x129e20 [0x48, 0x89, 0x55, 0xA0] (StorePre 0x129e20 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x129e20 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129e20 2 (.base 5 (.d8 0xa0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129e20 2 (.base 5 (.d8 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x129e20 0x48 (by decide) 2 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 83), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 86), (15, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e1e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 86), (15, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e20) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 86), (15, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e24) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 93) (jmp_rel8_effect_step 0x129e24 0x4e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l129dd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129dd0 bytes_l129dd0) (entryMap (live .l129dd0))
      24 0x129dd0 bytes_l129dd0 b_l129dd0 := by
  have f0 : InstrSpec 0x129dd0 [0x55] (PushPre 0x129dd0 1) (pushR64Effect 0x129dd0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129dd0 1 5).toInstrSpec (push_r64_effect_step 0x129dd0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129dd1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129dd1) (movR64R64Effect 0x129dd1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129dd1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129dd1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129dd4 [0x41, 0x57] (PushPre 0x129dd4 2) (pushR64Effect 0x129dd4 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129dd4 2 15).toInstrSpec (push_r64_rex_effect_step 0x129dd4 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129dd6 [0x41, 0x56] (PushPre 0x129dd6 2) (pushR64Effect 0x129dd6 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129dd6 2 14).toInstrSpec (push_r64_rex_effect_step 0x129dd6 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129dd8 [0x41, 0x55] (PushPre 0x129dd8 2) (pushR64Effect 0x129dd8 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129dd8 2 13).toInstrSpec (push_r64_rex_effect_step 0x129dd8 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129dda [0x41, 0x54] (PushPre 0x129dda 2) (pushR64Effect 0x129dda 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129dda 2 12).toInstrSpec (push_r64_rex_effect_step 0x129dda 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x129ddc [0x53] (PushPre 0x129ddc 1) (pushR64Effect 0x129ddc 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129ddc 1 3).toInstrSpec (push_r64_effect_step 0x129ddc 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x129ddd [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x129ddd) (subR64Imm8Effect 0x129ddd 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129ddd 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x129ddd 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129de1 [0x48, 0xBB, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80] (fun s => s.RIP = 0x129de1) (movR64Imm64Effect 0x129de1 3 0x8080808080808080)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x129de1 3 0x8080808080808080).toInstrSpec (mov_r64_imm64_effect_step 0x129de1 0x48 0xbb (by decide) (by decide) 0x8080808080808080) pre_rip
  have f9 : InstrSpec 0x129deb [0x49, 0xBC, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A] (fun s => s.RIP = 0x129deb) (movR64Imm64Effect 0x129deb 12 0xa0a0a0a0a0a0a0a)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x129deb 12 0xa0a0a0a0a0a0a0a).toInstrSpec (mov_r64_imm64_effect_step 0x129deb 0x49 0xbc (by decide) (by decide) 0xa0a0a0a0a0a0a0a) pre_rip
  have f10 : InstrSpec 0x129df5 [0x48, 0x8B, 0x47, 0x10] (LoadPre 0x129df5 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x129df5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129df5 0 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129df5 0 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x129df5 0x48 (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x129df9 [0x48, 0x89, 0x45, 0xB0] (StorePre 0x129df9 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x129df9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129df9 0 (.base 5 (.d8 0xb0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129df9 0 (.base 5 (.d8 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x129df9 0x48 (by decide) 0 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x129dfd [0x48, 0x8B, 0x07] (LoadPre 0x129dfd (fun s => AddrMode.addr (.base 7 .none) s (0x129dfd + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x129dfd 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129dfd 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x129dfd 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x129e00 [0x48, 0x89, 0x45, 0xB8] (StorePre 0x129e00 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x129e00 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129e00 0 (.base 5 (.d8 0xb8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129e00 0 (.base 5 (.d8 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x129e00 0x48 (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x129e04 [0x48, 0x8B, 0x47, 0x08] (LoadPre 0x129e04 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x129e04 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129e04 0 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129e04 0 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x129e04 0x48 (by decide) 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x129e08 [0x48, 0x89, 0x45, 0xC0] (StorePre 0x129e08 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x129e08 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129e08 0 (.base 5 (.d8 0xc0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129e08 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x129e08 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x129e0c [0x48, 0x89, 0x75, 0xD0] (StorePre 0x129e0c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129e0c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129e0c 6 (.base 5 (.d8 0xd0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129e0c 6 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x129e0c 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x129e10 [0x48, 0x8D, 0x46, 0x08] (fun s => s.RIP = 0x129e10) (leaR64Effect 0x129e10 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129e10 0 (.base 6 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x129e10 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x129e14 [0x48, 0x89, 0x45, 0xA8] (StorePre 0x129e14 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x129e14 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129e14 0 (.base 5 (.d8 0xa8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129e14 0 (.base 5 (.d8 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x129e14 0x48 (by decide) 0 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x129e18 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x129e18) (xorR32R32Effect 0x129e18 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129e18 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x129e18 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129dd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129dd4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129dd6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129dd8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129dda) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ddc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ddd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129de1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129deb) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129df5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129df9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129dfd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e00) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e04) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e08) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e0c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e10) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e14) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 83), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e18) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e1b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l129dd0_1 code

theorem block_l129dd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129dd0 :=
  Rest.liftedBlock (rest_l129dd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129dd0 x hx)

theorem rest_l129e30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129e30 bytes_l129e30) (entryMap (live .l129e30))
      2 0x129e30 bytes_l129e30 b_l129e30 := by
  have f0 : InstrSpec 0x129e30 [0x80, 0x7C, 0x1F, 0xFF, 0x0A] (LoadPre 0x129e30 (fun s => AddrMode.addr (.sib 7 (some 3) 0 (.d8 0xff)) s (0x129e30 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129e30 5 (.sib 7 (some 3) 0 (.d8 0xff)) 0xa)
      [.gpr 7, .gpr 3] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129e30 5 (.sib 7 (some 3) 0 (.d8 0xff)) 0xa).toInstrSpec (cmp_m8_imm8_effect_step 0x129e30 (.sib 7 (some 3) 0 (.d8 0xff)) (by decide) (by decide) (by decide) 0xa) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129e35 [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x129e35) (atFlags (condHolds 4) (setccR8Effect 0x129e35 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x129e35 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x129e35 4 0xc0 (by decide) (by decide) c)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (5, 5), (7, 7), (15, 15), (19, 53)]) (p' := 0x129e35) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (5, 5), (7, 7), (15, 15), (19, 53)]) (p' := 0x129e38) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l129e30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129e30 :=
  Rest.liftedBlock (rest_l129e30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129e30 x hx)

theorem rest_l129e38 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129e38 bytes_l129e38) (entryMap (live .l129e38))
      8 0x129e38 bytes_l129e38 b_l129e38 := by
  have f0 : InstrSpec 0x129e38 [0x4C, 0x29, 0xFB] (fun s => s.RIP = 0x129e38) (subR64R64Effect 0x129e38 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (subR64R64Effect_footprint 0x129e38 3 15).toInstrSpec (sub_r64_r64_effect_step 0x129e38 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129e3b [0x49, 0x01, 0xFF] (fun s => s.RIP = 0x129e3b) (addR64R64Effect 0x129e3b 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129e3b 15 7).toInstrSpec (add_r64_r64_effect_step 0x129e3b 0x49 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129e3e [0x48, 0x8B, 0x4D, 0xB0] (LoadPre 0x129e3e (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x129e3e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129e3e 1 (.base 5 (.d8 0xb0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x129e3e 1 (.base 5 (.d8 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x129e3e 0x48 (by decide) 1 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x129e42 [0x88, 0x01] (StorePre 0x129e42 2 (fun s => AddrMode.addr (.base 1 .none) s (0x129e42 + BitVec.ofNat 64 2)) 1) (movM8R8Effect 0x129e42 2 0 (.base 1 .none))
      [.gpr 0, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x129e42 2 0 (.base 1 .none)).toInstrSpec (mov_m8_r8_effect_step 0x129e42 0 (by decide) (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x129e44 [0x48, 0x8B, 0x7D, 0xB8] (LoadPre 0x129e44 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x129e44 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129e44 7 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x129e44 7 (.base 5 (.d8 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x129e44 0x48 (by decide) 7 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x129e48 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x129e48) (movR64R64Effect 0x129e48 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x129e48 6 15).toInstrSpec (mov_r64_r64_effect_step 0x129e48 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129e4b [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x129e4b) (movR64R64Effect 0x129e4b 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129e4b 2 3).toInstrSpec (mov_r64_r64_effect_step 0x129e4b 0x48 0xda (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129e4e [0x48, 0x8B, 0x45, 0xC0] (LoadPre 0x129e4e (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x129e4e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129e4e 0 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129e4e 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x129e4e 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 53), (5, 5), (7, 7), (15, 15)]) (p' := 0x129e3b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 53), (5, 5), (7, 7), (15, 55)]) (p' := 0x129e3e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (3, 53), (5, 5), (7, 7), (15, 55)]) (p' := 0x129e42) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 57), (3, 53), (5, 5), (7, 7), (15, 55)]) (p' := 0x129e44) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (3, 53), (5, 5), (15, 55)]) (p' := 0x129e48) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 57), (3, 53), (5, 5), (15, 55)]) (p' := 0x129e4b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 57), (3, 53), (5, 5), (15, 55)]) (p' := 0x129e4e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(1, 57), (3, 53), (5, 5), (15, 55)]) (p' := 0x129e52) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129e38 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129e38 :=
  Rest.liftedBlock (rest_l129e38 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129e38 x hx)

theorem rest_l129e55 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129e55 bytes_l129e55) (entryMap (live .l129e55))
      7 0x129e55 bytes_l129e55 b_l129e55 := by
  have f0 : InstrSpec 0x129e55 [0x4D, 0x89, 0xEF] (fun s => s.RIP = 0x129e55) (movR64R64Effect 0x129e55 15 13)
      [.gpr 13] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x129e55 15 13).toInstrSpec (mov_r64_r64_effect_step 0x129e55 0x4d 0xef (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129e58 [0x84, 0xC0] (fun s => s.RIP = 0x129e58) (testR8R8Effect 0x129e58 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129e58 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x129e58 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129e5a [0x48, 0x8B, 0x55, 0xA0] (LoadPre 0x129e5a (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x129e5a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129e5a 2 (.base 5 (.d8 0xa0)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x129e5a 2 (.base 5 (.d8 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x129e5a 0x48 (by decide) 2 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x129e5e [0x4C, 0x89, 0xE3] (fun s => s.RIP = 0x129e5e) (movR64R64Effect 0x129e5e 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x129e5e 3 12).toInstrSpec (mov_r64_r64_effect_step 0x129e5e 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129e61 [0x49, 0xBC, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A] (fun s => s.RIP = 0x129e61) (movR64Imm64Effect 0x129e61 12 0xa0a0a0a0a0a0a0a)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x129e61 12 0xa0a0a0a0a0a0a0a).toInstrSpec (mov_r64_imm64_effect_step 0x129e61 0x49 0xbc (by decide) (by decide) 0xa0a0a0a0a0a0a0a) pre_rip
  have f5 : InstrSpec 0x129e6b [0x8B, 0x45, 0xCC] (LoadPre 0x129e6b (fun s => AddrMode.addr (.base 5 (.d8 0xcc)) s (0x129e6b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x129e6b 0 (.base 5 (.d8 0xcc)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x129e6b 0 (.base 5 (.d8 0xcc))).toInstrSpec (mov_r32_m32_low_effect_step 0x129e6b 0 (.base 5 (.d8 0xcc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e58) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e5a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e5e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e61) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e6b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 57), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e6e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel32_effect_step 0x129e6e 5 0x1c1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129e55 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129e55 :=
  Rest.liftedBlock (rest_l129e55 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129e55 x hx)

theorem rest_l129e74 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129e74 bytes_l129e74) (entryMap (live .l129e74))
      2 0x129e74 bytes_l129e74 b_l129e74 := by
  have f0 : InstrSpec 0x129e74 [0xA8, 0x01] (fun s => s.RIP = 0x129e74) (testAlImm8Effect 0x129e74 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x129e74 0x1).toInstrSpec (test_al_imm8_effect_step 0x129e74 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e76) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x129e76 5 0x1b5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129e74 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129e74 :=
  Rest.liftedBlock (rest_l129e74 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129e74 x hx)

theorem rest_l129e7c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129e7c bytes_l129e7c) (entryMap (live .l129e7c))
      2 0x129e7c bytes_l129e7c b_l129e7c := by
  have f0 : InstrSpec 0x129e7c [0x4C, 0x39, 0xF2] (fun s => s.RIP = 0x129e7c) (cmpR64R64Effect 0x129e7c 2 14)
      [.gpr 2, .gpr 14] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129e7c 2 14).toInstrSpec (cmp_r64_r64_effect_step 0x129e7c 0x4c 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e7f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129e7f 3 0xf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129e7c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129e7c :=
  Rest.liftedBlock (rest_l129e7c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129e7c x hx)

theorem rest_l129e81 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129e81 bytes_l129e81) (entryMap (live .l129e81))
      3 0x129e81 bytes_l129e81 b_l129e81 := by
  have f0 : InstrSpec 0x129e81 [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x129e81) (movR64R64Effect 0x129e81 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x129e81 13 14).toInstrSpec (mov_r64_r64_effect_step 0x129e81 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129e84 [0x48, 0x8B, 0x7D, 0xD0] (LoadPre 0x129e84 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129e84 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129e84 7 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x129e84 7 (.base 5 (.d8 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x129e84 0x48 (by decide) 7 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e84) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e88) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x129e88 0x156 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129e81 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129e81 :=
  Rest.liftedBlock (rest_l129e81 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129e81 x hx)

theorem rest_l129e90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129e90 bytes_l129e90) (entryMap (live .l129e90))
      2 0x129e90 bytes_l129e90 b_l129e90 := by
  have f0 : InstrSpec 0x129e90 [0x48, 0x8B, 0x7D, 0xD0] (LoadPre 0x129e90 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129e90 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129e90 7 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x129e90 7 (.base 5 (.d8 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x129e90 0x48 (by decide) 7 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129e94) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x129e94 0x16 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129e90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129e90 :=
  Rest.liftedBlock (rest_l129e90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129e90 x hx)

theorem rest_l129ea0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ea0 bytes_l129ea0) (entryMap (live .l129ea0))
      3 0x129ea0 bytes_l129ea0 b_l129ea0 := by
  have f0 : InstrSpec 0x129ea0 [0x4D, 0x89, 0xEE] (fun s => s.RIP = 0x129ea0) (movR64R64Effect 0x129ea0 14 13)
      [.gpr 13] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129ea0 14 13).toInstrSpec (mov_r64_r64_effect_step 0x129ea0 0x4d 0xee (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129ea3 [0x4C, 0x39, 0xEA] (fun s => s.RIP = 0x129ea3) (cmpR64R64Effect 0x129ea3 2 13)
      [.gpr 2, .gpr 13] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129ea3 2 13).toInstrSpec (cmp_r64_r64_effect_step 0x129ea3 0x4c 0xea (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ea3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ea6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x129ea6 2 0x137) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129ea0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ea0 :=
  Rest.liftedBlock (rest_l129ea0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ea0 x hx)

theorem rest_l129eac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129eac bytes_l129eac) (entryMap (live .l129eac))
      5 0x129eac bytes_l129eac b_l129eac := by
  have f0 : InstrSpec 0x129eac [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x129eac) (movR64R64Effect 0x129eac 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x129eac 1 2).toInstrSpec (mov_r64_r64_effect_step 0x129eac 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129eaf [0x4C, 0x29, 0xF1] (fun s => s.RIP = 0x129eaf) (subR64R64Effect 0x129eaf 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x129eaf 1 14).toInstrSpec (sub_r64_r64_effect_step 0x129eaf 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129eb2 [0x4A, 0x8D, 0x04, 0x37] (fun s => s.RIP = 0x129eb2) (leaR64Effect 0x129eb2 0 (.sib 7 (some 14) 0 .none))
      [.gpr 7, .gpr 14] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129eb2 0 (.sib 7 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x129eb2 0x4a (by decide) 0 (.sib 7 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129eb6 [0x48, 0x83, 0xF9, 0x0F] (fun s => s.RIP = 0x129eb6) (cmpR64Imm8Effect 0x129eb6 1 0xf)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x129eb6 1 0xf).toInstrSpec (cmp_r64_imm8_effect_step 0x129eb6 0x48 0xf9 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129eaf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129eb2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129eb6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129eba) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x129eba 7 0x34) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129eac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129eac :=
  Rest.liftedBlock (rest_l129eac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129eac x hx)

theorem rest_l129ebc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ebc bytes_l129ebc) (entryMap (live .l129ebc))
      2 0x129ebc bytes_l129ebc b_l129ebc := by
  have f0 : InstrSpec 0x129ebc [0x4C, 0x39, 0xF2] (fun s => s.RIP = 0x129ebc) (cmpR64R64Effect 0x129ebc 2 14)
      [.gpr 2, .gpr 14] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129ebc 2 14).toInstrSpec (cmp_r64_r64_effect_step 0x129ebc 0x4c 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ebf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x129ebf 4 0x11b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129ebc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ebc :=
  Rest.liftedBlock (rest_l129ebc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ebc x hx)

theorem rest_l129ec5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ec5 bytes_l129ec5) (entryMap (live .l129ec5))
      2 0x129ec5 bytes_l129ec5 b_l129ec5 := by
  have f0 : InstrSpec 0x129ec5 [0x31, 0xF6] (fun s => s.RIP = 0x129ec5) (xorR32R32Effect 0x129ec5 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129ec5 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x129ec5 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x129ec7 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129ec7) (fun _ => nopEffect 0x129ec7 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129ec7 9).toInstrSpec (nop_m_effect_step 0x129ec7 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ec7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ed0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l129ec5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ec5 :=
  Rest.liftedBlock (rest_l129ec5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ec5 x hx)

theorem rest_l129ed0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ed0 bytes_l129ed0) (entryMap (live .l129ed0))
      2 0x129ed0 bytes_l129ed0 b_l129ed0 := by
  have f0 : InstrSpec 0x129ed0 [0x80, 0x3C, 0x30, 0x0A] (LoadPre 0x129ed0 (fun s => AddrMode.addr (.sib 0 (some 6) 0 .none) s (0x129ed0 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129ed0 4 (.sib 0 (some 6) 0 .none) 0xa)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129ed0 4 (.sib 0 (some 6) 0 .none) 0xa).toInstrSpec (cmp_m8_imm8_effect_step 0x129ed0 (.sib 0 (some 6) 0 .none) (by decide) (by decide) (by decide) 0xa) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ed4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x129ed4 4 0xd6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129ed0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ed0 :=
  Rest.liftedBlock (rest_l129ed0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ed0 x hx)

theorem rest_l129eda [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129eda bytes_l129eda) (entryMap (live .l129eda))
      3 0x129eda bytes_l129eda b_l129eda := by
  have f0 : InstrSpec 0x129eda [0x48, 0xFF, 0xC6] (fun s => s.RIP = 0x129eda) (incR64Effect 0x129eda 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (incR64Effect_footprint 0x129eda 6).toInstrSpec (inc_r64_effect_step 0x129eda 0x48 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129edd [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x129edd) (cmpR64R64Effect 0x129edd 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129edd 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x129edd 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129edd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ee0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x129ee0 5 0xee) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129eda [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129eda :=
  Rest.liftedBlock (rest_l129eda code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129eda x hx)

theorem rest_l129ee2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ee2 bytes_l129ee2) (entryMap (live .l129ee2))
      1 0x129ee2 bytes_l129ee2 b_l129ee2 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x129ee2 0xf9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129ee2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ee2 :=
  Rest.liftedBlock (rest_l129ee2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ee2 x hx)

theorem rest_l129ef0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ef0 bytes_l129ef0) (entryMap (live .l129ef0))
      5 0x129ef0 bytes_l129ef0 b_l129ef0 := by
  have f0 : InstrSpec 0x129ef0 [0x4C, 0x8D, 0x58, 0x07] (fun s => s.RIP = 0x129ef0) (leaR64Effect 0x129ef0 11 (.base 0 (.d8 0x7)))
      [.gpr 0] [] [.reg 11, .rip] :=
    (leaR64Effect_footprint 0x129ef0 11 (.base 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x129ef0 0x4c (by decide) 3 (.base 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129ef4 [0x49, 0x83, 0xE3, 0xF8] (fun s => s.RIP = 0x129ef4) (andR64Imm8Effect 0x129ef4 11 0xf8)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x129ef4 11 0xf8).toInstrSpec (and_r64_imm8_effect_step 0x129ef4 0x49 0xe3 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129ef8 [0x49, 0x29, 0xC3] (fun s => s.RIP = 0x129ef8) (subR64R64Effect 0x129ef8 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (subR64R64Effect_footprint 0x129ef8 11 0).toInstrSpec (sub_r64_r64_effect_step 0x129ef8 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129efb [0x49, 0xBD, 0x00, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01] (fun s => s.RIP = 0x129efb) (movR64Imm64Effect 0x129efb 13 0x101010101010100)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x129efb 13 0x101010101010100).toInstrSpec (mov_r64_imm64_effect_step 0x129efb 0x49 0xbd (by decide) (by decide) 0x101010101010100) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ef4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ef8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 12), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129efb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 12), (13, 60), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f05) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x129f05 5 0x59) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129ef0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ef0 :=
  Rest.liftedBlock (rest_l129ef0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ef0 x hx)

theorem rest_l129f07 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f07 bytes_l129f07) (entryMap (live .l129f07))
      2 0x129f07 bytes_l129f07 b_l129f07 := by
  have f0 : InstrSpec 0x129f07 [0x48, 0x8D, 0x71, 0xF0] (fun s => s.RIP = 0x129f07) (leaR64Effect 0x129f07 6 (.base 1 (.d8 0xf0)))
      [.gpr 1] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129f07 6 (.base 1 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129f07 0x48 (by decide) 6 (.base 1 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129f0b [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x129f0b) (xorR32R32Effect 0x129f0b 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129f0b 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x129f0b 0x45 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f0b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f0e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l129f07 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f07 :=
  Rest.liftedBlock (rest_l129f07 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f07 x hx)

theorem rest_l129f0e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f0e bytes_l129f0e) (entryMap (live .l129f0e))
      3 0x129f0e bytes_l129f0e b_l129f0e := by
  have f0 : InstrSpec 0x129f0e [0x48, 0x8B, 0x7D, 0xA8] (LoadPre 0x129f0e (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x129f0e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129f0e 7 (.base 5 (.d8 0xa8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x129f0e 7 (.base 5 (.d8 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x129f0e 0x48 (by decide) 7 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129f12 [0x4C, 0x01, 0xF7] (fun s => s.RIP = 0x129f12) (addR64R64Effect 0x129f12 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129f12 7 14).toInstrSpec (add_r64_r64_effect_step 0x129f12 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129f15 [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129f15) (fun _ => nopEffect 0x129f15 11)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129f15 11).toInstrSpec (nop_m_effect_step 0x129f15 [0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f12) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f15) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f20) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l129f0e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f0e :=
  Rest.liftedBlock (rest_l129f0e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f0e x hx)

theorem rest_l129f20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f20 bytes_l129f20) (entryMap (live .l129f20))
      15 0x129f20 bytes_l129f20 b_l129f20 := by
  have f0 : InstrSpec 0x129f20 [0x4E, 0x8B, 0x44, 0x1F, 0xF8] (LoadPre 0x129f20 (fun s => AddrMode.addr (.sib 7 (some 11) 0 (.d8 0xf8)) s (0x129f20 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129f20 8 (.sib 7 (some 11) 0 (.d8 0xf8)))
      [.gpr 7, .gpr 11] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x129f20 8 (.sib 7 (some 11) 0 (.d8 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x129f20 0x4e (by decide) 0 (.sib 7 (some 11) 0 (.d8 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129f25 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x129f25) (movR64R64Effect 0x129f25 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x129f25 9 8).toInstrSpec (mov_r64_r64_effect_step 0x129f25 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129f28 [0x4D, 0x31, 0xE1] (fun s => s.RIP = 0x129f28) (xorR64R64Effect 0x129f28 9 12)
      [.gpr 9, .gpr 12] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x129f28 9 12).toInstrSpec (xor_r64_r64_effect_step 0x129f28 0x4d 0xe1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129f2b [0x4D, 0x89, 0xEA] (fun s => s.RIP = 0x129f2b) (movR64R64Effect 0x129f2b 10 13)
      [.gpr 13] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x129f2b 10 13).toInstrSpec (mov_r64_r64_effect_step 0x129f2b 0x4d 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129f2e [0x4D, 0x29, 0xCA] (fun s => s.RIP = 0x129f2e) (subR64R64Effect 0x129f2e 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (subR64R64Effect_footprint 0x129f2e 10 9).toInstrSpec (sub_r64_r64_effect_step 0x129f2e 0x4d 0xca (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129f31 [0x4D, 0x09, 0xC2] (fun s => s.RIP = 0x129f31) (orR64R64Effect 0x129f31 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129f31 10 8).toInstrSpec (or_r64_r64_effect_step 0x129f31 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129f34 [0x4E, 0x8B, 0x04, 0x1F] (LoadPre 0x129f34 (fun s => AddrMode.addr (.sib 7 (some 11) 0 .none) s (0x129f34 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129f34 8 (.sib 7 (some 11) 0 .none))
      [.gpr 7, .gpr 11] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x129f34 8 (.sib 7 (some 11) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x129f34 0x4e (by decide) 0 (.sib 7 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x129f38 [0x4D, 0x31, 0xE0] (fun s => s.RIP = 0x129f38) (xorR64R64Effect 0x129f38 8 12)
      [.gpr 8, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x129f38 8 12).toInstrSpec (xor_r64_r64_effect_step 0x129f38 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129f3b [0x4D, 0x89, 0xE9] (fun s => s.RIP = 0x129f3b) (movR64R64Effect 0x129f3b 9 13)
      [.gpr 13] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x129f3b 9 13).toInstrSpec (mov_r64_r64_effect_step 0x129f3b 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129f3e [0x4D, 0x29, 0xC1] (fun s => s.RIP = 0x129f3e) (subR64R64Effect 0x129f3e 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x129f3e 9 8).toInstrSpec (sub_r64_r64_effect_step 0x129f3e 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129f41 [0x4D, 0x09, 0xC1] (fun s => s.RIP = 0x129f41) (orR64R64Effect 0x129f41 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129f41 9 8).toInstrSpec (or_r64_r64_effect_step 0x129f41 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x129f44 [0x49, 0x21, 0xDA] (fun s => s.RIP = 0x129f44) (andR64R64Effect 0x129f44 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129f44 10 3).toInstrSpec (and_r64_r64_effect_step 0x129f44 0x49 0xda (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x129f47 [0x4D, 0x21, 0xCA] (fun s => s.RIP = 0x129f47) (andR64R64Effect 0x129f47 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129f47 10 9).toInstrSpec (and_r64_r64_effect_step 0x129f47 0x4d 0xca (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129f4a [0x49, 0x39, 0xDA] (fun s => s.RIP = 0x129f4a) (cmpR64R64Effect 0x129f4a 10 3)
      [.gpr 10, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129f4a 10 3).toInstrSpec (cmp_r64_r64_effect_step 0x129f4a 0x49 0xda (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f25) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f28) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f2b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 57), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f2e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 57), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f31) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 57), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f34) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 57), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f38) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 57), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f3b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 69), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f3e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f41) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 73), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f44) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 73), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f47) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 73), (10, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f4a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 73), (10, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f4d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 81) (jcc_rel8_effect_step 0x129f4d 5 0x41) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129f20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f20 :=
  Rest.liftedBlock (rest_l129f20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f20 x hx)

theorem rest_l129f4f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f4f bytes_l129f4f) (entryMap (live .l129f4f))
      3 0x129f4f bytes_l129f4f b_l129f4f := by
  have f0 : InstrSpec 0x129f4f [0x49, 0x83, 0xC3, 0x10] (fun s => s.RIP = 0x129f4f) (addR64Imm8Effect 0x129f4f 11 0x10)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129f4f 11 0x10).toInstrSpec (add_r64_imm8_effect_step 0x129f4f 0x49 0xc3 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129f53 [0x49, 0x39, 0xF3] (fun s => s.RIP = 0x129f53) (cmpR64R64Effect 0x129f53 11 6)
      [.gpr 11, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129f53 11 6).toInstrSpec (cmp_r64_r64_effect_step 0x129f53 0x49 0xf3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f56) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x129f56 6 0xc8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129f4f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f4f :=
  Rest.liftedBlock (rest_l129f4f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f4f x hx)

theorem rest_l129f58 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f58 bytes_l129f58) (entryMap (live .l129f58))
      1 0x129f58 bytes_l129f58 b_l129f58 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x129f58 0x36 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129f58 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f58 :=
  Rest.liftedBlock (rest_l129f58 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f58 x hx)

theorem rest_l129f60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f60 bytes_l129f60) (entryMap (live .l129f60))
      2 0x129f60 bytes_l129f60 b_l129f60 := by
  have f0 : InstrSpec 0x129f60 [0x31, 0xF6] (fun s => s.RIP = 0x129f60) (xorR32R32Effect 0x129f60 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129f60 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x129f60 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x129f62 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129f62) (fun _ => nopEffect 0x129f62 14)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129f62 14).toInstrSpec (nop_m_effect_step 0x129f62 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f62) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f70) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l129f60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f60 :=
  Rest.liftedBlock (rest_l129f60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f60 x hx)

theorem rest_l129f70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f70 bytes_l129f70) (entryMap (live .l129f70))
      2 0x129f70 bytes_l129f70 b_l129f70 := by
  have f0 : InstrSpec 0x129f70 [0x80, 0x3C, 0x30, 0x0A] (LoadPre 0x129f70 (fun s => AddrMode.addr (.sib 0 (some 6) 0 .none) s (0x129f70 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129f70 4 (.sib 0 (some 6) 0 .none) 0xa)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129f70 4 (.sib 0 (some 6) 0 .none) 0xa).toInstrSpec (cmp_m8_imm8_effect_step 0x129f70 (.sib 0 (some 6) 0 .none) (by decide) (by decide) (by decide) 0xa) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f74) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129f74 4 0x3a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129f70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f70 :=
  Rest.liftedBlock (rest_l129f70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f70 x hx)

theorem rest_l129f76 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f76 bytes_l129f76) (entryMap (live .l129f76))
      3 0x129f76 bytes_l129f76 b_l129f76 := by
  have f0 : InstrSpec 0x129f76 [0x48, 0xFF, 0xC6] (fun s => s.RIP = 0x129f76) (incR64Effect 0x129f76 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (incR64Effect_footprint 0x129f76 6).toInstrSpec (inc_r64_effect_step 0x129f76 0x48 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129f79 [0x49, 0x39, 0xF3] (fun s => s.RIP = 0x129f79) (cmpR64R64Effect 0x129f79 11 6)
      [.gpr 11, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129f79 11 6).toInstrSpec (cmp_r64_r64_effect_step 0x129f79 0x49 0xf3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f79) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f7c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x129f7c 5 0xf2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129f76 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f76 :=
  Rest.liftedBlock (rest_l129f76 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f76 x hx)

theorem rest_l129f7e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f7e bytes_l129f7e) (entryMap (live .l129f7e))
      3 0x129f7e bytes_l129f7e b_l129f7e := by
  have f0 : InstrSpec 0x129f7e [0x48, 0x8D, 0x71, 0xF0] (fun s => s.RIP = 0x129f7e) (leaR64Effect 0x129f7e 6 (.base 1 (.d8 0xf0)))
      [.gpr 1] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129f7e 6 (.base 1 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129f7e 0x48 (by decide) 6 (.base 1 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129f82 [0x49, 0x39, 0xF3] (fun s => s.RIP = 0x129f82) (cmpR64R64Effect 0x129f82 11 6)
      [.gpr 11, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129f82 11 6).toInstrSpec (cmp_r64_r64_effect_step 0x129f82 0x49 0xf3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f82) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f85) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x129f85 6 0x87) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129f7e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f7e :=
  Rest.liftedBlock (rest_l129f7e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f7e x hx)

theorem rest_l129f87 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f87 bytes_l129f87) (entryMap (live .l129f87))
      1 0x129f87 bytes_l129f87 b_l129f87 := by
  have f0 : InstrSpec 0x129f87 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129f87) (fun _ => nopEffect 0x129f87 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129f87 9).toInstrSpec (nop_m_effect_step 0x129f87 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f90) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l129f87 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f87 :=
  Rest.liftedBlock (rest_l129f87 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f87 x hx)

theorem rest_l129f90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f90 bytes_l129f90) (entryMap (live .l129f90))
      4 0x129f90 bytes_l129f90 b_l129f90 := by
  have f0 : InstrSpec 0x129f90 [0x4C, 0x89, 0xDE] (fun s => s.RIP = 0x129f90) (movR64R64Effect 0x129f90 6 11)
      [.gpr 11] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x129f90 6 11).toInstrSpec (mov_r64_r64_effect_step 0x129f90 0x4c 0xde (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129f93 [0x4C, 0x39, 0xD9] (fun s => s.RIP = 0x129f93) (cmpR64R64Effect 0x129f93 1 11)
      [.gpr 1, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129f93 1 11).toInstrSpec (cmp_r64_r64_effect_step 0x129f93 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129f96 [0x48, 0x8B, 0x7D, 0xD0] (LoadPre 0x129f96 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129f96 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129f96 7 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x129f96 7 (.base 5 (.d8 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x129f96 0x48 (by decide) 7 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f93) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f96) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129f9a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x129f9a 4 0x44) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129f90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f90 :=
  Rest.liftedBlock (rest_l129f90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f90 x hx)

theorem rest_l129f9c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129f9c bytes_l129f9c) (entryMap (live .l129f9c))
      1 0x129f9c bytes_l129f9c b_l129f9c := by
  have f0 : InstrSpec 0x129f9c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x129f9c) (fun _ => nopEffect 0x129f9c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129f9c 4).toInstrSpec (nop_m_effect_step 0x129f9c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fa0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l129f9c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129f9c :=
  Rest.liftedBlock (rest_l129f9c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129f9c x hx)

theorem rest_l129fa0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129fa0 bytes_l129fa0) (entryMap (live .l129fa0))
      2 0x129fa0 bytes_l129fa0 b_l129fa0 := by
  have f0 : InstrSpec 0x129fa0 [0x80, 0x3C, 0x30, 0x0A] (LoadPre 0x129fa0 (fun s => AddrMode.addr (.sib 0 (some 6) 0 .none) s (0x129fa0 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129fa0 4 (.sib 0 (some 6) 0 .none) 0xa)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129fa0 4 (.sib 0 (some 6) 0 .none) 0xa).toInstrSpec (cmp_m8_imm8_effect_step 0x129fa0 (.sib 0 (some 6) 0 .none) (by decide) (by decide) (by decide) 0xa) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fa4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129fa4 4 0xa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129fa0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129fa0 :=
  Rest.liftedBlock (rest_l129fa0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129fa0 x hx)

theorem rest_l129fa6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129fa6 bytes_l129fa6) (entryMap (live .l129fa6))
      3 0x129fa6 bytes_l129fa6 b_l129fa6 := by
  have f0 : InstrSpec 0x129fa6 [0x48, 0xFF, 0xC6] (fun s => s.RIP = 0x129fa6) (incR64Effect 0x129fa6 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (incR64Effect_footprint 0x129fa6 6).toInstrSpec (inc_r64_effect_step 0x129fa6 0x48 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129fa9 [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x129fa9) (cmpR64R64Effect 0x129fa9 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129fa9 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x129fa9 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fa9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x129fac 5 0xf2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129fa6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129fa6 :=
  Rest.liftedBlock (rest_l129fa6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129fa6 x hx)

theorem rest_l129fae [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129fae bytes_l129fae) (entryMap (live .l129fae))
      1 0x129fae bytes_l129fae b_l129fae := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x129fae 0x30 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129fae [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129fae :=
  Rest.liftedBlock (rest_l129fae code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129fae x hx)

theorem rest_l129fb0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129fb0 bytes_l129fb0) (entryMap (live .l129fb0))
      5 0x129fb0 bytes_l129fb0 b_l129fb0 := by
  have f0 : InstrSpec 0x129fb0 [0x4D, 0x8D, 0x2C, 0x36] (fun s => s.RIP = 0x129fb0) (leaR64Effect 0x129fb0 13 (.sib 14 (some 6) 0 .none))
      [.gpr 14, .gpr 6] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x129fb0 13 (.sib 14 (some 6) 0 .none)).toInstrSpec (lea_r64_effect_step 0x129fb0 0x4d (by decide) 5 (.sib 14 (some 6) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129fb4 [0x49, 0xFF, 0xC5] (fun s => s.RIP = 0x129fb4) (incR64Effect 0x129fb4 13)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (incR64Effect_footprint 0x129fb4 13).toInstrSpec (inc_r64_effect_step 0x129fb4 0x49 0xc5 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129fb7 [0x49, 0x01, 0xF6] (fun s => s.RIP = 0x129fb7) (addR64R64Effect 0x129fb7 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129fb7 14 6).toInstrSpec (add_r64_r64_effect_step 0x129fb7 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129fba [0x49, 0x39, 0xD6] (fun s => s.RIP = 0x129fba) (cmpR64R64Effect 0x129fba 14 2)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129fba 14 2).toInstrSpec (cmp_r64_r64_effect_step 0x129fba 0x49 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fb4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fb7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 57), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fbd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x129fbd 3 0xfffffedd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129fb0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129fb0 :=
  Rest.liftedBlock (rest_l129fb0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129fb0 x hx)

theorem rest_l129fc3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129fc3 bytes_l129fc3) (entryMap (live .l129fc3))
      2 0x129fc3 bytes_l129fc3 b_l129fc3 := by
  have f0 : InstrSpec 0x129fc3 [0x80, 0x3C, 0x06, 0x0A] (LoadPre 0x129fc3 (fun s => AddrMode.addr (.sib 6 (some 0) 0 .none) s (0x129fc3 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129fc3 4 (.sib 6 (some 0) 0 .none) 0xa)
      [.gpr 6, .gpr 0] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129fc3 4 (.sib 6 (some 0) 0 .none) 0xa).toInstrSpec (cmp_m8_imm8_effect_step 0x129fc3 (.sib 6 (some 0) 0 .none) (by decide) (by decide) (by decide) 0xa) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fc7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x129fc7 5 0xfffffed3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129fc3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129fc3 :=
  Rest.liftedBlock (rest_l129fc3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129fc3 x hx)

theorem rest_l129fcd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129fcd bytes_l129fcd) (entryMap (live .l129fcd))
      5 0x129fcd bytes_l129fcd b_l129fcd := by
  have f0 : InstrSpec 0x129fcd [0x49, 0x89, 0xDC] (fun s => s.RIP = 0x129fcd) (movR64R64Effect 0x129fcd 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x129fcd 12 3).toInstrSpec (mov_r64_r64_effect_step 0x129fcd 0x49 0xdc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129fd0 [0x31, 0xC0] (fun s => s.RIP = 0x129fd0) (xorR32R32Effect 0x129fd0 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129fd0 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x129fd0 0xc0 (by decide)) pre_rip
  have f2 : InstrSpec 0x129fd2 [0x4D, 0x89, 0xEE] (fun s => s.RIP = 0x129fd2) (movR64R64Effect 0x129fd2 14 13)
      [.gpr 13] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129fd2 14 13).toInstrSpec (mov_r64_r64_effect_step 0x129fd2 0x4d 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129fd5 [0x4C, 0x89, 0xEB] (fun s => s.RIP = 0x129fd5) (movR64R64Effect 0x129fd5 3 13)
      [.gpr 13] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x129fd5 3 13).toInstrSpec (mov_r64_r64_effect_step 0x129fd5 0x4c 0xeb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (5, 5), (7, 7), (13, 13), (15, 15)]) (p' := 0x129fd0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (5, 5), (7, 7), (13, 13), (15, 15)]) (p' := 0x129fd2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (3, 3), (5, 5), (7, 7), (13, 13), (15, 15)]) (p' := 0x129fd5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 54), (3, 57), (5, 5), (7, 7), (13, 13), (15, 15)]) (p' := 0x129fd8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x129fd8 0x1c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129fcd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129fcd :=
  Rest.liftedBlock (rest_l129fcd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129fcd x hx)

theorem rest_l129fe0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129fe0 bytes_l129fe0) (entryMap (live .l129fe0))
      1 0x129fe0 bytes_l129fe0 b_l129fe0 := by
  have f0 : InstrSpec 0x129fe0 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x129fe0) (movR64R64Effect 0x129fe0 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x129fe0 13 2).toInstrSpec (mov_r64_r64_effect_step 0x129fe0 0x49 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fe3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129fe0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129fe0 :=
  Rest.liftedBlock (rest_l129fe0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129fe0 x hx)

theorem rest_l129fe3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129fe3 bytes_l129fe3) (entryMap (live .l129fe3))
      7 0x129fe3 bytes_l129fe3 b_l129fe3 := by
  have f0 : InstrSpec 0x129fe3 [0x49, 0x89, 0xDC] (fun s => s.RIP = 0x129fe3) (movR64R64Effect 0x129fe3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x129fe3 12 3).toInstrSpec (mov_r64_r64_effect_step 0x129fe3 0x49 0xdc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129fe6 [0xB0, 0x01] (fun s => s.RIP = 0x129fe6) (movR8Imm8Effect 0x129fe6 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x129fe6 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x129fe6 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x129fe8 [0x4D, 0x89, 0xEE] (fun s => s.RIP = 0x129fe8) (movR64R64Effect 0x129fe8 14 13)
      [.gpr 13] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129fe8 14 13).toInstrSpec (mov_r64_r64_effect_step 0x129fe8 0x4d 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129feb [0x4D, 0x89, 0xFD] (fun s => s.RIP = 0x129feb) (movR64R64Effect 0x129feb 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x129feb 13 15).toInstrSpec (mov_r64_r64_effect_step 0x129feb 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129fee [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x129fee) (movR64R64Effect 0x129fee 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x129fee 3 2).toInstrSpec (mov_r64_r64_effect_step 0x129fee 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129ff1 [0x4C, 0x39, 0xFA] (fun s => s.RIP = 0x129ff1) (cmpR64R64Effect 0x129ff1 2 15)
      [.gpr 2, .gpr 15] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129ff1 2 15).toInstrSpec (cmp_r64_r64_effect_step 0x129ff1 0x4c 0xfa (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fe6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fe8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129feb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129fee) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ff1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ff4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x129ff4 4 0x3b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129fe3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129fe3 :=
  Rest.liftedBlock (rest_l129fe3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129fe3 x hx)

theorem rest_l129ff6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ff6 bytes_l129ff6) (entryMap (live .l129ff6))
      4 0x129ff6 bytes_l129ff6 b_l129ff6 := by
  have f0 : InstrSpec 0x129ff6 [0x89, 0x45, 0xCC] (StorePre 0x129ff6 3 (fun s => AddrMode.addr (.base 5 (.d8 0xcc)) s (0x129ff6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x129ff6 0 (.base 5 (.d8 0xcc)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x129ff6 0 (.base 5 (.d8 0xcc))).toInstrSpec (mov_m32_r32_low_effect_step 0x129ff6 0 (.base 5 (.d8 0xcc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x129ff9 [0x48, 0x8B, 0x45, 0xB0] (LoadPre 0x129ff9 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x129ff9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129ff9 0 (.base 5 (.d8 0xb0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129ff9 0 (.base 5 (.d8 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x129ff9 0x48 (by decide) 0 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129ffd [0x80, 0x38, 0x00] (LoadPre 0x129ffd (fun s => AddrMode.addr (.base 0 .none) s (0x129ffd + BitVec.ofNat 64 3)) 1) (cmpM8Imm8Effect 0x129ffd 3 (.base 0 .none) 0x0)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129ffd 3 (.base 0 .none) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x129ffd (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (5, 5), (7, 7), (15, 15)]) (p' := 0x129ff9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (5, 5), (7, 7), (15, 15)]) (p' := 0x129ffd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (3, 3), (5, 5), (7, 7), (15, 15), (19, 56)]) (p' := 0x12a000) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x12a000 4 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129ff6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ff6 :=
  Rest.liftedBlock (rest_l129ff6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ff6 x hx)

theorem rest_l12a002 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a002 bytes_l12a002) (entryMap (live .l12a002))
      4 0x12a002 bytes_l12a002 b_l12a002 := by
  have f0 : InstrSpec 0x12a002 [0xBA, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a002) (movR32Imm32Effect 0x12a002 5 2 0x4)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x12a002 5 2 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x12a002 0xba (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x12a007 [0x48, 0x8B, 0x7D, 0xB8] (LoadPre 0x12a007 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x12a007 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a007 7 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12a007 7 (.base 5 (.d8 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x12a007 0x48 (by decide) 7 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a00b [0x48, 0x8D, 0x35, 0xAB, 0x83, 0x0D, 0x00] (fun s => s.RIP = 0x12a00b) (leaR64Effect 0x12a00b 6 (.rip 0xd83ab))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x12a00b 6 (.rip 0xd83ab)).toInstrSpec (lea_r64_effect_step 0x12a00b 0x48 (by decide) 6 (.rip 0xd83ab) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a012 [0x48, 0x8B, 0x45, 0xC0] (LoadPre 0x12a012 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x12a012 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a012 0 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a012 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x12a012 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5)]) (p' := 0x12a007) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5)]) (p' := 0x12a00b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5)]) (p' := 0x12a012) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(5, 5)]) (p' := 0x12a016) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12a002 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a002 :=
  Rest.liftedBlock (rest_l12a002 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a002 x hx)

theorem rest_l12a019 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a019 bytes_l12a019) (entryMap (live .l12a019))
      3 0x12a019 bytes_l12a019 b_l12a019 := by
  have f0 : InstrSpec 0x12a019 [0x48, 0x8B, 0x7D, 0xD0] (LoadPre 0x12a019 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x12a019 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a019 7 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12a019 7 (.base 5 (.d8 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x12a019 0x48 (by decide) 7 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a01d [0x84, 0xC0] (fun s => s.RIP = 0x12a01d) (testR8R8Effect 0x12a01d 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x12a01d 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x12a01d 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a01d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a01f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12a01f 5 0x14) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a019 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a019 :=
  Rest.liftedBlock (rest_l12a019 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a019 x hx)

theorem rest_l12a021 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a021 bytes_l12a021) (entryMap (live .l12a021))
      2 0x12a021 bytes_l12a021 b_l12a021 := by
  have f0 : InstrSpec 0x12a021 [0x4C, 0x39, 0xFB] (fun s => s.RIP = 0x12a021) (cmpR64R64Effect 0x12a021 3 15)
      [.gpr 3, .gpr 15] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a021 3 15).toInstrSpec (cmp_r64_r64_effect_step 0x12a021 0x4c 0xfb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (5, 5), (7, 7), (15, 15), (19, 53)]) (p' := 0x12a024) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x12a024 5 0xfffffe06) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a021 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a021 :=
  Rest.liftedBlock (rest_l12a021 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a021 x hx)

theorem rest_l12a02a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a02a bytes_l12a02a) (entryMap (live .l12a02a))
      2 0x12a02a bytes_l12a02a b_l12a02a := by
  have f0 : InstrSpec 0x12a02a [0x31, 0xC0] (fun s => s.RIP = 0x12a02a) (xorR32R32Effect 0x12a02a 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a02a 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12a02a 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (5, 5), (7, 7), (15, 15)]) (p' := 0x12a02c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x12a02c 0xfffffe07 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12a02a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a02a :=
  Rest.liftedBlock (rest_l12a02a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a02a x hx)

theorem rest_l12a031 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a031 bytes_l12a031) (entryMap (live .l12a031))
      2 0x12a031 bytes_l12a031 b_l12a031 := by
  have f0 : InstrSpec 0x12a031 [0x31, 0xC0] (fun s => s.RIP = 0x12a031) (xorR32R32Effect 0x12a031 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a031 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12a031 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a033) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x12a033 0x2 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12a031 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a031 :=
  Rest.liftedBlock (rest_l12a031 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a031 x hx)

theorem rest_l12a035 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a035 bytes_l12a035) (entryMap (live .l12a035))
      1 0x12a035 bytes_l12a035 b_l12a035 := by
  have f0 : InstrSpec 0x12a035 [0xB0, 0x01] (fun s => s.RIP = 0x12a035) (movR8Imm8Effect 0x12a035 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x12a035 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x12a035 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a037) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12a035 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a035 :=
  Rest.liftedBlock (rest_l12a035 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a035 x hx)

theorem rest_l12a037 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a037 bytes_l12a037) (entryMap (live .l12a037))
      8 0x12a037 bytes_l12a037 b_l12a037 := by
  have f0 : InstrSpec 0x12a037 [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x12a037) (addR64Imm8Effect 0x12a037 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a037 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x12a037 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a03b [0x5B] (PopPre 0x12a03b) (popR64Effect 0x12a03b 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a03b 1 3).toInstrSpec (pop_r64_effect_step 0x12a03b 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x12a03c [0x41, 0x5C] (PopPre 0x12a03c) (popR64Effect 0x12a03c 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a03c 2 12).toInstrSpec (pop_r64_rex_effect_step 0x12a03c 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a03e [0x41, 0x5D] (PopPre 0x12a03e) (popR64Effect 0x12a03e 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a03e 2 13).toInstrSpec (pop_r64_rex_effect_step 0x12a03e 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x12a040 [0x41, 0x5E] (PopPre 0x12a040) (popR64Effect 0x12a040 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a040 2 14).toInstrSpec (pop_r64_rex_effect_step 0x12a040 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12a042 [0x41, 0x5F] (PopPre 0x12a042) (popR64Effect 0x12a042 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a042 2 15).toInstrSpec (pop_r64_rex_effect_step 0x12a042 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12a044 [0x5D] (PopPre 0x12a044) (popR64Effect 0x12a044 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a044 1 5).toInstrSpec (pop_r64_effect_step 0x12a044 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x12a045 [0xC3] (RetPre 0x12a045) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a045).toInstrSpec (ret_effect_step 0x12a045) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a03b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a03c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a03e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a040) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a042) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a044) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a045) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l12a037 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a037 :=
  Rest.liftedBlock (rest_l12a037 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a037 x hx)

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

theorem_by block_l129dd0_eval :
    program.runBlock (dialect code) ⟨.l129dd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129e30_eval :
    program.runBlock (dialect code) ⟨.l129e30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129e38_eval :
    program.runBlock (dialect code) ⟨.l129e38, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129e55_eval :
    program.runBlock (dialect code) ⟨.l129e55, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129e74_eval :
    program.runBlock (dialect code) ⟨.l129e74, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129e7c_eval :
    program.runBlock (dialect code) ⟨.l129e7c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129e81_eval :
    program.runBlock (dialect code) ⟨.l129e81, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129e90_eval :
    program.runBlock (dialect code) ⟨.l129e90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ea0_eval :
    program.runBlock (dialect code) ⟨.l129ea0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129eac_eval :
    program.runBlock (dialect code) ⟨.l129eac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ebc_eval :
    program.runBlock (dialect code) ⟨.l129ebc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ec5_eval :
    program.runBlock (dialect code) ⟨.l129ec5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ed0_eval :
    program.runBlock (dialect code) ⟨.l129ed0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129eda_eval :
    program.runBlock (dialect code) ⟨.l129eda, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ee2_eval :
    program.runBlock (dialect code) ⟨.l129ee2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ef0_eval :
    program.runBlock (dialect code) ⟨.l129ef0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f07_eval :
    program.runBlock (dialect code) ⟨.l129f07, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f0e_eval :
    program.runBlock (dialect code) ⟨.l129f0e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f20_eval :
    program.runBlock (dialect code) ⟨.l129f20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f4f_eval :
    program.runBlock (dialect code) ⟨.l129f4f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f58_eval :
    program.runBlock (dialect code) ⟨.l129f58, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f60_eval :
    program.runBlock (dialect code) ⟨.l129f60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f70_eval :
    program.runBlock (dialect code) ⟨.l129f70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f76_eval :
    program.runBlock (dialect code) ⟨.l129f76, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f7e_eval :
    program.runBlock (dialect code) ⟨.l129f7e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f87_eval :
    program.runBlock (dialect code) ⟨.l129f87, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f90_eval :
    program.runBlock (dialect code) ⟨.l129f90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129f9c_eval :
    program.runBlock (dialect code) ⟨.l129f9c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129fa0_eval :
    program.runBlock (dialect code) ⟨.l129fa0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129fa6_eval :
    program.runBlock (dialect code) ⟨.l129fa6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129fae_eval :
    program.runBlock (dialect code) ⟨.l129fae, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129fb0_eval :
    program.runBlock (dialect code) ⟨.l129fb0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129fc3_eval :
    program.runBlock (dialect code) ⟨.l129fc3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129fcd_eval :
    program.runBlock (dialect code) ⟨.l129fcd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129fe0_eval :
    program.runBlock (dialect code) ⟨.l129fe0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129fe3_eval :
    program.runBlock (dialect code) ⟨.l129fe3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ff6_eval :
    program.runBlock (dialect code) ⟨.l129ff6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a002_eval :
    program.runBlock (dialect code) ⟨.l12a002, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a019_eval :
    program.runBlock (dialect code) ⟨.l12a019, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a021_eval :
    program.runBlock (dialect code) ⟨.l12a021, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a02a_eval :
    program.runBlock (dialect code) ⟨.l12a02a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a031_eval :
    program.runBlock (dialect code) ⟨.l12a031, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a035_eval :
    program.runBlock (dialect code) ⟨.l12a035, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a037_eval :
    program.runBlock (dialect code) ⟨.l12a037, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
