import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l101ab0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101ab0 bytes_l101ab0) (entryMap (live .l101ab0))
      20 0x101ab0 bytes_l101ab0 b_l101ab0 := by
  have f0 : InstrSpec 0x101ab0 [0x55] (PushPre 0x101ab0 1) (pushR64Effect 0x101ab0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ab0 1 5).toInstrSpec (push_r64_effect_step 0x101ab0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101ab1 [0x41, 0x57] (PushPre 0x101ab1 2) (pushR64Effect 0x101ab1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ab1 2 15).toInstrSpec (push_r64_rex_effect_step 0x101ab1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101ab3 [0x41, 0x56] (PushPre 0x101ab3 2) (pushR64Effect 0x101ab3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ab3 2 14).toInstrSpec (push_r64_rex_effect_step 0x101ab3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101ab5 [0x41, 0x55] (PushPre 0x101ab5 2) (pushR64Effect 0x101ab5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ab5 2 13).toInstrSpec (push_r64_rex_effect_step 0x101ab5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101ab7 [0x41, 0x54] (PushPre 0x101ab7 2) (pushR64Effect 0x101ab7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ab7 2 12).toInstrSpec (push_r64_rex_effect_step 0x101ab7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101ab9 [0x53] (PushPre 0x101ab9 1) (pushR64Effect 0x101ab9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ab9 1 3).toInstrSpec (push_r64_effect_step 0x101ab9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101aba [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x101aba) (subR64Imm8Effect 0x101aba 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x101aba 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x101aba 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101abe [0x49, 0x89, 0xFA] (fun s => s.RIP = 0x101abe) (movR64R64Effect 0x101abe 10 7)
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x101abe 10 7).toInstrSpec (mov_r64_r64_effect_step 0x101abe 0x49 0xfa (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101ac1 [0x80, 0xF2, 0x01] (fun s => s.RIP = 0x101ac1) (xorR8Imm8Effect 0x101ac1 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR8Imm8Effect_footprint 0x101ac1 3 2 0x1).toInstrSpec (xor_r8_imm8_effect_step 0x101ac1 0xf2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101ac4 [0x0F, 0xB6, 0xFA] (fun s => s.RIP = 0x101ac4) (movzxR32R8Effect 0x101ac4 3 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x101ac4 3 7 2).toInstrSpec (movzx_r32_r8_effect_step 0x101ac4 0xfa (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101ac7 [0xC1, 0xE7, 0x18] (fun s => s.RIP = 0x101ac7) (shlR32Effect 0x101ac7 3 7 24)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x101ac7 3 7 24).toInstrSpec (shl_r32_imm8_effect_step 0x101ac7 0xe7 0x18 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101aca [0x45, 0x8B, 0x42, 0x10] (LoadPre 0x101aca (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x101aca + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101aca 8 (.base 10 (.d8 0x10)))
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x101aca 8 (.base 10 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x101aca 0x45 (by decide) 0 (.base 10 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101ace [0x41, 0x8B, 0x42, 0x18] (LoadPre 0x101ace (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x101ace + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101ace 0 (.base 10 (.d8 0x18)))
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x101ace 0 (.base 10 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x101ace 0x41 (by decide) 0 (.base 10 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x101ad2 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x101ad2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101ad2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ad2 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101ad2 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101ad2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101ad7 [0x41, 0x8B, 0x4A, 0x1C] (LoadPre 0x101ad7 (fun s => AddrMode.addr (.base 10 (.d8 0x1c)) s (0x101ad7 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101ad7 1 (.base 10 (.d8 0x1c)))
      [.gpr 10] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x101ad7 1 (.base 10 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x101ad7 0x41 (by decide) 1 (.base 10 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101adb [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x101adb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101adb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101adb 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101adb 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101adb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101ae0 [0x41, 0x8B, 0x52, 0x20] (LoadPre 0x101ae0 (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x101ae0 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101ae0 2 (.base 10 (.d8 0x20)))
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x101ae0 2 (.base 10 (.d8 0x20))).toInstrSpec (mov_r32_m32_effect_step 0x101ae0 0x41 (by decide) 2 (.base 10 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x101ae4 [0x48, 0x89, 0x54, 0x24, 0x20] (StorePre 0x101ae4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101ae4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ae4 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101ae4 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101ae4 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101ae9 [0x8D, 0x04, 0x80] (fun s => s.RIP = 0x101ae9) (leaR32Effect 0x101ae9 3 0 (.sib 0 (some 0) 2 .none))
      [.gpr 0, .gpr 0] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x101ae9 3 0 (.sib 0 (some 0) 2 .none)).toInstrSpec (lea_r32_effect_step 0x101ae9 0 (.sib 0 (some 0) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101aec [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x101aec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101aec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101aec 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101aec 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101aec 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101abe) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ac1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ac4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 71), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ac7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aca) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ace) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ad2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ad7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 77), (1, 80), (2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101adb) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 80), (2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 77), (1, 80), (2, 83), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 77), (1, 80), (2, 83), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae9) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 80), (2, 83), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aec) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 86), (1, 80), (2, 83), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af1) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 89) (by decide) rfl

theorem block_l101ab0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101ab0 :=
  Rest.liftedBlock (rest_l101ab0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101ab0 x hx)

theorem rest_l101af1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101af1 bytes_l101af1) (entryMap (live .l101af1))
      20 0x101af1 bytes_l101af1 b_l101af1 := by
  have f0 : InstrSpec 0x101af1 [0x44, 0x8D, 0x0C, 0x89] (fun s => s.RIP = 0x101af1) (leaR32Effect 0x101af1 4 9 (.sib 1 (some 1) 2 .none))
      [.gpr 1, .gpr 1] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x101af1 4 9 (.sib 1 (some 1) 2 .none)).toInstrSpec (lea_r32_rex_effect_step 0x101af1 0x44 (by decide) 1 (.sib 1 (some 1) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101af5 [0x4C, 0x89, 0x0C, 0x24] (StorePre 0x101af5 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101af5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101af5 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101af5 9 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101af5 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101af9 [0x8D, 0x1C, 0x92] (fun s => s.RIP = 0x101af9) (leaR32Effect 0x101af9 3 3 (.sib 2 (some 2) 2 .none))
      [.gpr 2, .gpr 2] [] [.reg 3, .rip] :=
    (leaR32Effect_footprint 0x101af9 3 3 (.sib 2 (some 2) 2 .none)).toInstrSpec (lea_r32_effect_step 0x101af9 3 (.sib 2 (some 2) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101afc [0x41, 0xBF, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101afc) (movR32Imm32Effect 0x101afc 6 15 0x3ffffff)
      [] [] [.reg 15, .rip] :=
    (movR32Imm32Effect_footprint 0x101afc 6 15 0x3ffffff).toInstrSpec (mov_r32_imm32_rex_effect_step 0x101afc 0x41 0xbf (by decide) (by decide) 0x3ffffff) pre_rip
  have f4 : InstrSpec 0x101b02 [0x44, 0x23, 0x3E] (LoadPre 0x101b02 (fun s => AddrMode.addr (.base 6 .none) s (0x101b02 + BitVec.ofNat 64 3)) 4) (andR32M32Effect 0x101b02 3 15 (.base 6 .none))
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (andR32M32Effect_footprint 0x101b02 3 15 (.base 6 .none)).toInstrSpec (and_r32_m32_rex_effect_step 0x101b02 0x44 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101b05 [0x45, 0x03, 0x7A, 0x24] (LoadPre 0x101b05 (fun s => AddrMode.addr (.base 10 (.d8 0x24)) s (0x101b05 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b05 4 15 (.base 10 (.d8 0x24)))
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101b05 4 15 (.base 10 (.d8 0x24))).toInstrSpec (add_r32_m32_rex_effect_step 0x101b05 0x45 (by decide) 7 (.base 10 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101b09 [0x8B, 0x56, 0x03] (LoadPre 0x101b09 (fun s => AddrMode.addr (.base 6 (.d8 0x3)) s (0x101b09 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101b09 2 (.base 6 (.d8 0x3)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x101b09 2 (.base 6 (.d8 0x3))).toInstrSpec (mov_r32_m32_low_effect_step 0x101b09 2 (.base 6 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101b0c [0x44, 0x8B, 0x66, 0x06] (LoadPre 0x101b0c (fun s => AddrMode.addr (.base 6 (.d8 0x6)) s (0x101b0c + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101b0c 12 (.base 6 (.d8 0x6)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x101b0c 12 (.base 6 (.d8 0x6))).toInstrSpec (mov_r32_m32_effect_step 0x101b0c 0x44 (by decide) 4 (.base 6 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101b10 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x101b10) (shrR32Effect 0x101b10 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x101b10 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x101b10 0xea 0x2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101b13 [0x81, 0xE2, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101b13) (andR32Imm32Effect 0x101b13 6 2 0x3ffffff)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101b13 6 2 0x3ffffff).toInstrSpec (and_r32_imm32_effect_step 0x101b13 0xe2 0x3ffffff (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101b19 [0x41, 0x03, 0x52, 0x28] (LoadPre 0x101b19 (fun s => AddrMode.addr (.base 10 (.d8 0x28)) s (0x101b19 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b19 4 2 (.base 10 (.d8 0x28)))
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101b19 4 2 (.base 10 (.d8 0x28))).toInstrSpec (add_r32_m32_rex_effect_step 0x101b19 0x41 (by decide) 2 (.base 10 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101b1d [0x41, 0xC1, 0xEC, 0x04] (fun s => s.RIP = 0x101b1d) (shrR32Effect 0x101b1d 4 12 4)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x101b1d 4 12 4).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101b1d 0x41 0xec 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101b21 [0x41, 0x81, 0xE4, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101b21) (andR32Imm32Effect 0x101b21 7 12 0x3ffffff)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101b21 7 12 0x3ffffff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101b21 0x41 0xe4 0x3ffffff (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101b28 [0x45, 0x03, 0x62, 0x2C] (LoadPre 0x101b28 (fun s => AddrMode.addr (.base 10 (.d8 0x2c)) s (0x101b28 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b28 4 12 (.base 10 (.d8 0x2c)))
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101b28 4 12 (.base 10 (.d8 0x2c))).toInstrSpec (add_r32_m32_rex_effect_step 0x101b28 0x45 (by decide) 4 (.base 10 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101b2c [0x8B, 0x4E, 0x09] (LoadPre 0x101b2c (fun s => AddrMode.addr (.base 6 (.d8 0x9)) s (0x101b2c + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101b2c 1 (.base 6 (.d8 0x9)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x101b2c 1 (.base 6 (.d8 0x9))).toInstrSpec (mov_r32_m32_low_effect_step 0x101b2c 1 (.base 6 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101b2f [0xC1, 0xE9, 0x06] (fun s => s.RIP = 0x101b2f) (shrR32Effect 0x101b2f 3 1 6)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x101b2f 3 1 6).toInstrSpec (shr_r32_imm8_effect_step 0x101b2f 0xe9 0x6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101b32 [0x41, 0x03, 0x4A, 0x30] (LoadPre 0x101b32 (fun s => AddrMode.addr (.base 10 (.d8 0x30)) s (0x101b32 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b32 4 1 (.base 10 (.d8 0x30)))
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101b32 4 1 (.base 10 (.d8 0x30))).toInstrSpec (add_r32_m32_rex_effect_step 0x101b32 0x41 (by decide) 1 (.base 10 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x101b36 [0x8B, 0x76, 0x0C] (LoadPre 0x101b36 (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x101b36 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101b36 6 (.base 6 (.d8 0xc)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x101b36 6 (.base 6 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x101b36 6 (.base 6 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x101b39 [0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x101b39) (shrR32Effect 0x101b39 3 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x101b39 3 6 8).toInstrSpec (shr_r32_imm8_effect_step 0x101b39 0xee 0x8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101b3c [0x41, 0x03, 0x7A, 0x34] (LoadPre 0x101b3c (fun s => AddrMode.addr (.base 10 (.d8 0x34)) s (0x101b3c + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b3c 4 7 (.base 10 (.d8 0x34)))
      [.gpr 7, .gpr 10] [] [.reg 7, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101b3c 4 7 (.base 10 (.d8 0x34))).toInstrSpec (add_r32_m32_rex_effect_step 0x101b3c 0x41 (by decide) 7 (.base 10 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101afc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b02) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b05) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b09) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 64), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b0c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 64), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b10) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b13) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b19) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 72), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b1d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 72), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 74), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b21) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 72), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 76), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b28) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 72), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 78), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b2c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 80), (2, 72), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 78), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b2f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 72), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 78), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b32) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 84), (2, 72), (3, 56), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 78), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b36) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 84), (2, 72), (3, 56), (4, 4), (6, 86), (7, 7), (8, 8), (9, 53), (10, 10), (12, 78), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b39) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 84), (2, 72), (3, 56), (4, 4), (6, 88), (7, 7), (8, 8), (9, 53), (10, 10), (12, 78), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b3c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 84), (2, 72), (3, 56), (4, 4), (6, 88), (7, 90), (8, 8), (9, 53), (10, 10), (12, 78), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b40) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 92) (by decide) rfl

theorem block_l101af1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101af1 :=
  Rest.liftedBlock (rest_l101af1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101af1 x hx)

theorem rest_l101b40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101b40 bytes_l101b40) (entryMap (live .l101b40))
      20 0x101b40 bytes_l101b40 b_l101b40 := by
  have f0 : InstrSpec 0x101b40 [0x01, 0xF7] (fun s => s.RIP = 0x101b40) (addR32R32Effect 0x101b40 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101b40 2 7 6).toInstrSpec (add_r32_r32_effect_step 0x101b40 0xf7 (by decide)) pre_rip
  have f1 : InstrSpec 0x101b42 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x101b42) (movR64R64Effect 0x101b42 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101b42 6 15).toInstrSpec (mov_r64_r64_effect_step 0x101b42 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101b45 [0x49, 0x0F, 0xAF, 0xF0] (fun s => s.RIP = 0x101b45) (imulR64R64Effect 0x101b45 4 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b45 4 6 8).toInstrSpec (imul_r64_r64_effect_step 0x101b45 0x49 (by decide) 0xf0 (by decide)) pre_rip
  have f3 : InstrSpec 0x101b49 [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x101b49) (movR64R64Effect 0x101b49 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x101b49 5 2).toInstrSpec (mov_r64_r64_effect_step 0x101b49 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101b4c [0x48, 0x0F, 0xAF, 0xEB] (fun s => s.RIP = 0x101b4c) (imulR64R64Effect 0x101b4c 4 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b4c 4 5 3).toInstrSpec (imul_r64_r64_effect_step 0x101b4c 0x48 (by decide) 0xeb (by decide)) pre_rip
  have f5 : InstrSpec 0x101b50 [0x48, 0x01, 0xF5] (fun s => s.RIP = 0x101b50) (addR64R64Effect 0x101b50 5 6)
      [.gpr 5, .gpr 6] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101b50 5 6).toInstrSpec (add_r64_r64_effect_step 0x101b50 0x48 0xf5 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101b53 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x101b53) (movR64R64Effect 0x101b53 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101b53 6 12).toInstrSpec (mov_r64_r64_effect_step 0x101b53 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101b56 [0x49, 0x0F, 0xAF, 0xF1] (fun s => s.RIP = 0x101b56) (imulR64R64Effect 0x101b56 4 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b56 4 6 9).toInstrSpec (imul_r64_r64_effect_step 0x101b56 0x49 (by decide) 0xf1 (by decide)) pre_rip
  have f8 : InstrSpec 0x101b5a [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x101b5a) (movR64R64Effect 0x101b5a 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101b5a 13 1).toInstrSpec (mov_r64_r64_effect_step 0x101b5a 0x49 0xcd (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101b5d [0x4C, 0x0F, 0xAF, 0xE8] (fun s => s.RIP = 0x101b5d) (imulR64R64Effect 0x101b5d 4 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b5d 4 13 0).toInstrSpec (imul_r64_r64_effect_step 0x101b5d 0x4c (by decide) 0xe8 (by decide)) pre_rip
  have f10 : InstrSpec 0x101b61 [0x49, 0x01, 0xF5] (fun s => s.RIP = 0x101b61) (addR64R64Effect 0x101b61 13 6)
      [.gpr 13, .gpr 6] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101b61 13 6).toInstrSpec (add_r64_r64_effect_step 0x101b61 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101b64 [0x49, 0x01, 0xED] (fun s => s.RIP = 0x101b64) (addR64R64Effect 0x101b64 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101b64 13 5).toInstrSpec (add_r64_r64_effect_step 0x101b64 0x49 0xed (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101b67 [0x41, 0x8B, 0x6A, 0x14] (LoadPre 0x101b67 (fun s => AddrMode.addr (.base 10 (.d8 0x14)) s (0x101b67 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101b67 5 (.base 10 (.d8 0x14)))
      [.gpr 10] [] [.reg 5, .rip] :=
    (movR32M32Effect_footprint 0x101b67 5 (.base 10 (.d8 0x14))).toInstrSpec (mov_r32_m32_effect_step 0x101b67 0x41 (by decide) 5 (.base 10 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x101b6b [0x44, 0x8D, 0x5C, 0xAD, 0x00] (fun s => s.RIP = 0x101b6b) (leaR32Effect 0x101b6b 5 11 (.sib 5 (some 5) 2 (.d8 0x0)))
      [.gpr 5, .gpr 5] [] [.reg 11, .rip] :=
    (leaR32Effect_footprint 0x101b6b 5 11 (.sib 5 (some 5) 2 (.d8 0x0))).toInstrSpec (lea_r32_rex_effect_step 0x101b6b 0x44 (by decide) 3 (.sib 5 (some 5) 2 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101b70 [0x4C, 0x0F, 0xAF, 0xDF] (fun s => s.RIP = 0x101b70) (imulR64R64Effect 0x101b70 4 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b70 4 11 7).toInstrSpec (imul_r64_r64_effect_step 0x101b70 0x4c (by decide) 0xdf (by decide)) pre_rip
  have f15 : InstrSpec 0x101b74 [0x4D, 0x01, 0xEB] (fun s => s.RIP = 0x101b74) (addR64R64Effect 0x101b74 11 13)
      [.gpr 11, .gpr 13] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101b74 11 13).toInstrSpec (add_r64_r64_effect_step 0x101b74 0x4d 0xeb (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101b77 [0x4D, 0x89, 0xFD] (fun s => s.RIP = 0x101b77) (movR64R64Effect 0x101b77 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101b77 13 15).toInstrSpec (mov_r64_r64_effect_step 0x101b77 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101b7a [0x4C, 0x0F, 0xAF, 0xED] (fun s => s.RIP = 0x101b7a) (imulR64R64Effect 0x101b7a 4 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b7a 4 13 5).toInstrSpec (imul_r64_r64_effect_step 0x101b7a 0x4c (by decide) 0xed (by decide)) pre_rip
  have f18 : InstrSpec 0x101b7e [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x101b7e) (movR64R64Effect 0x101b7e 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101b7e 14 2).toInstrSpec (mov_r64_r64_effect_step 0x101b7e 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101b81 [0x4D, 0x0F, 0xAF, 0xF0] (fun s => s.RIP = 0x101b81) (imulR64R64Effect 0x101b81 4 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b81 4 14 8).toInstrSpec (imul_r64_r64_effect_step 0x101b81 0x4d (by decide) 0xf0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b42) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b45) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b49) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 59), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b4c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b50) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b53) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 65), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b56) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b5a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (13, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b5d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (13, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b61) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (13, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b64) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (13, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b67) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (12, 12), (13, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b6b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (11, 79), (12, 12), (13, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b70) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (11, 81), (12, 12), (13, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b74) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (11, 83), (12, 12), (13, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b77) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (11, 83), (12, 12), (13, 85), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b7a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (11, 83), (12, 12), (13, 87), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b7e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (11, 83), (12, 12), (13, 87), (14, 89), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b81) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (11, 83), (12, 12), (13, 87), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b85) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 93) (by decide) rfl

theorem block_l101b40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101b40 :=
  Rest.liftedBlock (rest_l101b40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101b40 x hx)

theorem rest_l101b85 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101b85 bytes_l101b85) (entryMap (live .l101b85))
      20 0x101b85 bytes_l101b85 b_l101b85 := by
  have f0 : InstrSpec 0x101b85 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x101b85) (movR64R64Effect 0x101b85 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x101b85 9 8).toInstrSpec (mov_r64_r64_effect_step 0x101b85 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101b88 [0x4D, 0x01, 0xEE] (fun s => s.RIP = 0x101b88) (addR64R64Effect 0x101b88 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101b88 14 13).toInstrSpec (add_r64_r64_effect_step 0x101b88 0x4d 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101b8b [0x4D, 0x89, 0xE5] (fun s => s.RIP = 0x101b8b) (movR64R64Effect 0x101b8b 13 12)
      [.gpr 12] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101b8b 13 12).toInstrSpec (mov_r64_r64_effect_step 0x101b8b 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101b8e [0x4C, 0x0F, 0xAF, 0xEB] (fun s => s.RIP = 0x101b8e) (imulR64R64Effect 0x101b8e 4 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b8e 4 13 3).toInstrSpec (imul_r64_r64_effect_step 0x101b8e 0x4c (by decide) 0xeb (by decide)) pre_rip
  have f4 : InstrSpec 0x101b92 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x101b92) (movR64R64Effect 0x101b92 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101b92 0 1).toInstrSpec (mov_r64_r64_effect_step 0x101b92 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101b95 [0x4C, 0x8B, 0x04, 0x24] (LoadPre 0x101b95 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101b95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101b95 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x101b95 8 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101b95 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101b99 [0x49, 0x0F, 0xAF, 0xC0] (fun s => s.RIP = 0x101b99) (imulR64R64Effect 0x101b99 4 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101b99 4 0 8).toInstrSpec (imul_r64_r64_effect_step 0x101b99 0x49 (by decide) 0xc0 (by decide)) pre_rip
  have f7 : InstrSpec 0x101b9d [0x4C, 0x01, 0xE8] (fun s => s.RIP = 0x101b9d) (addR64R64Effect 0x101b9d 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101b9d 0 13).toInstrSpec (add_r64_r64_effect_step 0x101b9d 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101ba0 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x101ba0) (addR64R64Effect 0x101ba0 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101ba0 0 14).toInstrSpec (add_r64_r64_effect_step 0x101ba0 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101ba3 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x101ba3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101ba3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ba3 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x101ba3 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101ba3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101ba8 [0x48, 0x0F, 0xAF, 0xF7] (fun s => s.RIP = 0x101ba8) (imulR64R64Effect 0x101ba8 4 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101ba8 4 6 7).toInstrSpec (imul_r64_r64_effect_step 0x101ba8 0x48 (by decide) 0xf7 (by decide)) pre_rip
  have f11 : InstrSpec 0x101bac [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x101bac) (addR64R64Effect 0x101bac 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101bac 6 0).toInstrSpec (add_r64_r64_effect_step 0x101bac 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101baf [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x101baf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101baf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101baf 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101baf 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101baf 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101bb4 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x101bb4) (movR64R64Effect 0x101bb4 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101bb4 0 15).toInstrSpec (mov_r64_r64_effect_step 0x101bb4 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101bb7 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x101bb7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101bb7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101bb7 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x101bb7 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101bb7 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101bbc [0x48, 0x0F, 0xAF, 0xC6] (fun s => s.RIP = 0x101bbc) (imulR64R64Effect 0x101bbc 4 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101bbc 4 0 6).toInstrSpec (imul_r64_r64_effect_step 0x101bbc 0x48 (by decide) 0xc6 (by decide)) pre_rip
  have f16 : InstrSpec 0x101bc0 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x101bc0) (movR64R64Effect 0x101bc0 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101bc0 14 2).toInstrSpec (mov_r64_r64_effect_step 0x101bc0 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101bc3 [0x4C, 0x0F, 0xAF, 0xF5] (fun s => s.RIP = 0x101bc3) (imulR64R64Effect 0x101bc3 4 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101bc3 4 14 5).toInstrSpec (imul_r64_r64_effect_step 0x101bc3 0x4c (by decide) 0xf5 (by decide)) pre_rip
  have f18 : InstrSpec 0x101bc7 [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x101bc7) (addR64R64Effect 0x101bc7 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101bc7 14 0).toInstrSpec (add_r64_r64_effect_step 0x101bc7 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101bca [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x101bca) (movR64R64Effect 0x101bca 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101bca 0 12).toInstrSpec (mov_r64_r64_effect_step 0x101bca 0x4c 0xe0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b88) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b8b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 57), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b8e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b92) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b95) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b99) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b9d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ba0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ba3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ba8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bac) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 75), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101baf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 75), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bb4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 75), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bb7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 80), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bbc) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 80), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bc0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 82), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 80), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 84), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bc3) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 82), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 80), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 86), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bc7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 82), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 80), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 88), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bca) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 80), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 88), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bcd) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 92) (by decide) rfl

theorem block_l101b85 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101b85 :=
  Rest.liftedBlock (rest_l101b85 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101b85 x hx)

theorem rest_l101bcd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101bcd bytes_l101bcd) (entryMap (live .l101bcd))
      20 0x101bcd bytes_l101bcd b_l101bcd := by
  have f0 : InstrSpec 0x101bcd [0x49, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x101bcd) (imulR64R64Effect 0x101bcd 4 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101bcd 4 0 9).toInstrSpec (imul_r64_r64_effect_step 0x101bcd 0x49 (by decide) 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x101bd1 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x101bd1) (movR64R64Effect 0x101bd1 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101bd1 13 1).toInstrSpec (mov_r64_r64_effect_step 0x101bd1 0x49 0xcd (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101bd4 [0x4C, 0x0F, 0xAF, 0xEB] (fun s => s.RIP = 0x101bd4) (imulR64R64Effect 0x101bd4 4 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101bd4 4 13 3).toInstrSpec (imul_r64_r64_effect_step 0x101bd4 0x4c (by decide) 0xeb (by decide)) pre_rip
  have f3 : InstrSpec 0x101bd8 [0x49, 0x01, 0xC5] (fun s => s.RIP = 0x101bd8) (addR64R64Effect 0x101bd8 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101bd8 13 0).toInstrSpec (add_r64_r64_effect_step 0x101bd8 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101bdb [0x4D, 0x01, 0xF5] (fun s => s.RIP = 0x101bdb) (addR64R64Effect 0x101bdb 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101bdb 13 14).toInstrSpec (add_r64_r64_effect_step 0x101bdb 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101bde [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x101bde) (movR64R64Effect 0x101bde 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101bde 0 8).toInstrSpec (mov_r64_r64_effect_step 0x101bde 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101be1 [0x48, 0x0F, 0xAF, 0xC7] (fun s => s.RIP = 0x101be1) (imulR64R64Effect 0x101be1 4 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101be1 4 0 7).toInstrSpec (imul_r64_r64_effect_step 0x101be1 0x48 (by decide) 0xc7 (by decide)) pre_rip
  have f7 : InstrSpec 0x101be5 [0x4C, 0x01, 0xE8] (fun s => s.RIP = 0x101be5) (addR64R64Effect 0x101be5 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101be5 0 13).toInstrSpec (add_r64_r64_effect_step 0x101be5 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101be8 [0x48, 0x89, 0x04, 0x24] (StorePre 0x101be8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101be8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101be8 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101be8 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101be8 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101bec [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x101bec) (movR64R64Effect 0x101bec 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101bec 0 15).toInstrSpec (mov_r64_r64_effect_step 0x101bec 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101bef [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x101bef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101bef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101bef 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x101bef 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101bef 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101bf4 [0x49, 0x0F, 0xAF, 0xC0] (fun s => s.RIP = 0x101bf4) (imulR64R64Effect 0x101bf4 4 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101bf4 4 0 8).toInstrSpec (imul_r64_r64_effect_step 0x101bf4 0x49 (by decide) 0xc0 (by decide)) pre_rip
  have f12 : InstrSpec 0x101bf8 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x101bf8) (movR64R64Effect 0x101bf8 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101bf8 14 2).toInstrSpec (mov_r64_r64_effect_step 0x101bf8 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101bfb [0x4C, 0x0F, 0xAF, 0xF6] (fun s => s.RIP = 0x101bfb) (imulR64R64Effect 0x101bfb 4 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101bfb 4 14 6).toInstrSpec (imul_r64_r64_effect_step 0x101bfb 0x4c (by decide) 0xf6 (by decide)) pre_rip
  have f14 : InstrSpec 0x101bff [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x101bff) (addR64R64Effect 0x101bff 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101bff 14 0).toInstrSpec (add_r64_r64_effect_step 0x101bff 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101c02 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x101c02) (movR64R64Effect 0x101c02 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101c02 0 12).toInstrSpec (mov_r64_r64_effect_step 0x101c02 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101c05 [0x48, 0x0F, 0xAF, 0xC5] (fun s => s.RIP = 0x101c05) (imulR64R64Effect 0x101c05 4 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101c05 4 0 5).toInstrSpec (imul_r64_r64_effect_step 0x101c05 0x48 (by decide) 0xc5 (by decide)) pre_rip
  have f17 : InstrSpec 0x101c09 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x101c09) (movR64R64Effect 0x101c09 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101c09 13 1).toInstrSpec (mov_r64_r64_effect_step 0x101c09 0x49 0xcd (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101c0c [0x4D, 0x0F, 0xAF, 0xE9] (fun s => s.RIP = 0x101c0c) (imulR64R64Effect 0x101c0c 4 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101c0c 4 13 9).toInstrSpec (imul_r64_r64_effect_step 0x101c0c 0x4d (by decide) 0xe9 (by decide)) pre_rip
  have f19 : InstrSpec 0x101c10 [0x49, 0x01, 0xC5] (fun s => s.RIP = 0x101c10) (addR64R64Effect 0x101c10 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c10 13 0).toInstrSpec (add_r64_r64_effect_step 0x101c10 0x49 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bd4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bd8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bdb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bde) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101be1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101be5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101be8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bec) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bef) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bf4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bf8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 74), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bfb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 78), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bff) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 74), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 80), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c02) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 80), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c05) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 80), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c09) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 86), (14, 80), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c0c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 88), (14, 80), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c10) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 90), (14, 80), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c13) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 92) (by decide) rfl

theorem block_l101bcd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101bcd :=
  Rest.liftedBlock (rest_l101bcd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101bcd x hx)

theorem rest_l101c13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c13 bytes_l101c13) (entryMap (live .l101c13))
      20 0x101c13 bytes_l101c13 b_l101c13 := by
  have f0 : InstrSpec 0x101c13 [0x4D, 0x01, 0xF5] (fun s => s.RIP = 0x101c13) (addR64R64Effect 0x101c13 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c13 13 14).toInstrSpec (add_r64_r64_effect_step 0x101c13 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101c16 [0x48, 0x0F, 0xAF, 0xDF] (fun s => s.RIP = 0x101c16) (imulR64R64Effect 0x101c16 4 3 7)
      [.gpr 3, .gpr 7] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101c16 4 3 7).toInstrSpec (imul_r64_r64_effect_step 0x101c16 0x48 (by decide) 0xdf (by decide)) pre_rip
  have f2 : InstrSpec 0x101c1a [0x4C, 0x01, 0xEB] (fun s => s.RIP = 0x101c1a) (addR64R64Effect 0x101c1a 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c1a 3 13).toInstrSpec (add_r64_r64_effect_step 0x101c1a 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101c1d [0x4C, 0x0F, 0xAF, 0x7C, 0x24, 0x20] (LoadPre 0x101c1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101c1d + BitVec.ofNat 64 6)) 8) (imulR64M64Effect 0x101c1d 6 15 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (imulR64M64Effect_footprint 0x101c1d 6 15 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (imul_r64_m64_effect_step 0x101c1d 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x101c23 [0x49, 0x0F, 0xAF, 0xD0] (fun s => s.RIP = 0x101c23) (imulR64R64Effect 0x101c23 4 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101c23 4 2 8).toInstrSpec (imul_r64_r64_effect_step 0x101c23 0x49 (by decide) 0xd0 (by decide)) pre_rip
  have f5 : InstrSpec 0x101c27 [0x4C, 0x01, 0xFA] (fun s => s.RIP = 0x101c27) (addR64R64Effect 0x101c27 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c27 2 15).toInstrSpec (add_r64_r64_effect_step 0x101c27 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101c2a [0x4C, 0x0F, 0xAF, 0xE6] (fun s => s.RIP = 0x101c2a) (imulR64R64Effect 0x101c2a 4 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101c2a 4 12 6).toInstrSpec (imul_r64_r64_effect_step 0x101c2a 0x4c (by decide) 0xe6 (by decide)) pre_rip
  have f7 : InstrSpec 0x101c2e [0x48, 0x0F, 0xAF, 0xCD] (fun s => s.RIP = 0x101c2e) (imulR64R64Effect 0x101c2e 4 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101c2e 4 1 5).toInstrSpec (imul_r64_r64_effect_step 0x101c2e 0x48 (by decide) 0xcd (by decide)) pre_rip
  have f8 : InstrSpec 0x101c32 [0x4C, 0x01, 0xE1] (fun s => s.RIP = 0x101c32) (addR64R64Effect 0x101c32 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c32 1 12).toInstrSpec (add_r64_r64_effect_step 0x101c32 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101c35 [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x101c35) (addR64R64Effect 0x101c35 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c35 1 2).toInstrSpec (add_r64_r64_effect_step 0x101c35 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101c38 [0x49, 0x0F, 0xAF, 0xF9] (fun s => s.RIP = 0x101c38) (imulR64R64Effect 0x101c38 4 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x101c38 4 7 9).toInstrSpec (imul_r64_r64_effect_step 0x101c38 0x49 (by decide) 0xf9 (by decide)) pre_rip
  have f11 : InstrSpec 0x101c3c [0x48, 0x01, 0xCF] (fun s => s.RIP = 0x101c3c) (addR64R64Effect 0x101c3c 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c3c 7 1).toInstrSpec (add_r64_r64_effect_step 0x101c3c 0x48 0xcf (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101c3f [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x101c3f) (movR64R64Effect 0x101c3f 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101c3f 0 11).toInstrSpec (mov_r64_r64_effect_step 0x101c3f 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101c42 [0x48, 0xC1, 0xE8, 0x1A] (fun s => s.RIP = 0x101c42) (shrR64Effect 0x101c42 4 0 26)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101c42 4 0 26).toInstrSpec (shr_r64_imm8_effect_step 0x101c42 0x48 0xe8 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101c46 [0x41, 0x81, 0xE3, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101c46) (andR32Imm32Effect 0x101c46 7 11 0x3ffffff)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101c46 7 11 0x3ffffff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101c46 0x41 0xe3 0x3ffffff (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101c4d [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x101c4d) (movR32R32Effect 0x101c4d 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x101c4d 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x101c4d 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101c50 [0x4C, 0x03, 0x44, 0x24, 0x08] (LoadPre 0x101c50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101c50 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x101c50 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (addR64M64Effect_footprint 0x101c50 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (add_r64_m64_effect_step 0x101c50 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x101c55 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x101c55) (movR64R64Effect 0x101c55 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101c55 0 8).toInstrSpec (mov_r64_r64_effect_step 0x101c55 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101c58 [0x48, 0xC1, 0xE8, 0x1A] (fun s => s.RIP = 0x101c58) (shrR64Effect 0x101c58 4 0 26)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101c58 4 0 26).toInstrSpec (shr_r64_imm8_effect_step 0x101c58 0x48 0xe8 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101c5c [0x41, 0x81, 0xE0, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101c5c) (andR32Imm32Effect 0x101c5c 7 8 0x3ffffff)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101c5c 7 8 0x3ffffff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101c5c 0x41 0xe0 0x3ffffff (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c16) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c1a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c1d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c23) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 61), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c27) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c2a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c2e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c32) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 69), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c35) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c38) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c3c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c3f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c42) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c46) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 8), (9, 9), (10, 10), (11, 81), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c4d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 79), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 83), (9, 9), (10, 10), (11, 81), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c50) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 79), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 85), (9, 9), (10, 10), (11, 81), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c55) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 85), (9, 9), (10, 10), (11, 81), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c58) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 85), (9, 9), (10, 10), (11, 81), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c5c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 91), (9, 9), (10, 10), (11, 81), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c63) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 93) (by decide) rfl

theorem block_l101c13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c13 :=
  Rest.liftedBlock (rest_l101c13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c13 x hx)

theorem rest_l101c63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c63 bytes_l101c63) (entryMap (live .l101c63))
      20 0x101c63 bytes_l101c63 b_l101c63 := by
  have f0 : InstrSpec 0x101c63 [0x41, 0x89, 0xC1] (fun s => s.RIP = 0x101c63) (movR32R32Effect 0x101c63 3 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x101c63 3 9 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x101c63 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101c66 [0x4C, 0x03, 0x0C, 0x24] (LoadPre 0x101c66 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101c66 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x101c66 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (addR64M64Effect_footprint 0x101c66 9 (.sib 4 none 0 .none)).toInstrSpec (add_r64_m64_effect_step 0x101c66 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101c6a [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x101c6a) (movR64R64Effect 0x101c6a 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101c6a 0 9).toInstrSpec (mov_r64_r64_effect_step 0x101c6a 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101c6d [0x48, 0xC1, 0xE8, 0x1A] (fun s => s.RIP = 0x101c6d) (shrR64Effect 0x101c6d 4 0 26)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101c6d 4 0 26).toInstrSpec (shr_r64_imm8_effect_step 0x101c6d 0x48 0xe8 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101c71 [0x89, 0xC2] (fun s => s.RIP = 0x101c71) (movR32R32Effect 0x101c71 2 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x101c71 2 2 0).toInstrSpec (mov_r32_r32_effect_step 0x101c71 0xc2 (by decide)) pre_rip
  have f5 : InstrSpec 0x101c73 [0x48, 0x01, 0xDA] (fun s => s.RIP = 0x101c73) (addR64R64Effect 0x101c73 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c73 2 3).toInstrSpec (add_r64_r64_effect_step 0x101c73 0x48 0xda (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101c76 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x101c76) (movR64R64Effect 0x101c76 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101c76 0 2).toInstrSpec (mov_r64_r64_effect_step 0x101c76 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101c79 [0x48, 0xC1, 0xE8, 0x1A] (fun s => s.RIP = 0x101c79) (shrR64Effect 0x101c79 4 0 26)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101c79 4 0 26).toInstrSpec (shr_r64_imm8_effect_step 0x101c79 0x48 0xe8 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101c7d [0x89, 0xC0] (fun s => s.RIP = 0x101c7d) (movR32R32Effect 0x101c7d 2 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101c7d 2 0 0).toInstrSpec (mov_r32_r32_effect_step 0x101c7d 0xc0 (by decide)) pre_rip
  have f9 : InstrSpec 0x101c7f [0x48, 0x01, 0xF8] (fun s => s.RIP = 0x101c7f) (addR64R64Effect 0x101c7f 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101c7f 0 7).toInstrSpec (add_r64_r64_effect_step 0x101c7f 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101c82 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x101c82) (movR64R64Effect 0x101c82 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x101c82 1 0).toInstrSpec (mov_r64_r64_effect_step 0x101c82 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101c85 [0x48, 0xC1, 0xE9, 0x1A] (fun s => s.RIP = 0x101c85) (shrR64Effect 0x101c85 4 1 26)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101c85 4 1 26).toInstrSpec (shr_r64_imm8_effect_step 0x101c85 0x48 0xe9 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101c89 [0x8D, 0x0C, 0x89] (fun s => s.RIP = 0x101c89) (leaR32Effect 0x101c89 3 1 (.sib 1 (some 1) 2 .none))
      [.gpr 1, .gpr 1] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x101c89 3 1 (.sib 1 (some 1) 2 .none)).toInstrSpec (lea_r32_effect_step 0x101c89 1 (.sib 1 (some 1) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101c8c [0x44, 0x01, 0xD9] (fun s => s.RIP = 0x101c8c) (addR32R32Effect 0x101c8c 3 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101c8c 3 1 11).toInstrSpec (add_r32_r32_rex_effect_step 0x101c8c 0x44 0xd9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101c8f [0x89, 0xCE] (fun s => s.RIP = 0x101c8f) (movR32R32Effect 0x101c8f 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x101c8f 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x101c8f 0xce (by decide)) pre_rip
  have f15 : InstrSpec 0x101c91 [0xC1, 0xEE, 0x1A] (fun s => s.RIP = 0x101c91) (shrR32Effect 0x101c91 3 6 26)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x101c91 3 6 26).toInstrSpec (shr_r32_imm8_effect_step 0x101c91 0xee 0x1a (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101c94 [0x44, 0x01, 0xC6] (fun s => s.RIP = 0x101c94) (addR32R32Effect 0x101c94 3 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101c94 3 6 8).toInstrSpec (add_r32_r32_rex_effect_step 0x101c94 0x44 0xc6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101c97 [0x81, 0xE1, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101c97) (andR32Imm32Effect 0x101c97 6 1 0x3ffffff)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101c97 6 1 0x3ffffff).toInstrSpec (and_r32_imm32_effect_step 0x101c97 0xe1 0x3ffffff (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101c9d [0x41, 0x89, 0x4A, 0x24] (StorePre 0x101c9d 4 (fun s => AddrMode.addr (.base 10 (.d8 0x24)) s (0x101c9d + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101c9d 1 (.base 10 (.d8 0x24)))
      [.gpr 1, .gpr 10] [] [.rip] :=
    (movM32R32Effect_footprint 0x101c9d 1 (.base 10 (.d8 0x24))).toInstrSpec (mov_m32_r32_effect_step 0x101c9d 0x41 (by decide) 1 (.base 10 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x101ca1 [0x41, 0x89, 0x72, 0x28] (StorePre 0x101ca1 4 (fun s => AddrMode.addr (.base 10 (.d8 0x28)) s (0x101ca1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101ca1 6 (.base 10 (.d8 0x28)))
      [.gpr 6, .gpr 10] [] [.rip] :=
    (movM32R32Effect_footprint 0x101ca1 6 (.base 10 (.d8 0x28))).toInstrSpec (mov_m32_r32_effect_step 0x101ca1 0x41 (by decide) 6 (.base 10 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c66) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c6a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c6d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c71) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (2, 61), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c73) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c76) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c79) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c7d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c7f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c82) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c85) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 75), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c89) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 77), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c8c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 79), (2, 63), (3, 3), (4, 4), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c8f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 79), (2, 63), (3, 3), (4, 4), (6, 81), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c91) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 79), (2, 63), (3, 3), (4, 4), (6, 83), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c94) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 71), (1, 79), (2, 63), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c97) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 71), (1, 87), (2, 63), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c9d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 71), (1, 87), (2, 63), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 71), (1, 87), (2, 63), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca5) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 91) (by decide) rfl

theorem block_l101c63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c63 :=
  Rest.liftedBlock (rest_l101c63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c63 x hx)

theorem rest_l101ca5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101ca5 bytes_l101ca5) (entryMap (live .l101ca5))
      14 0x101ca5 bytes_l101ca5 b_l101ca5 := by
  have f0 : InstrSpec 0x101ca5 [0x41, 0x81, 0xE1, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101ca5) (andR32Imm32Effect 0x101ca5 7 9 0x3ffffff)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101ca5 7 9 0x3ffffff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101ca5 0x41 0xe1 0x3ffffff (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101cac [0x45, 0x89, 0x4A, 0x2C] (StorePre 0x101cac 4 (fun s => AddrMode.addr (.base 10 (.d8 0x2c)) s (0x101cac + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101cac 9 (.base 10 (.d8 0x2c)))
      [.gpr 9, .gpr 10] [] [.rip] :=
    (movM32R32Effect_footprint 0x101cac 9 (.base 10 (.d8 0x2c))).toInstrSpec (mov_m32_r32_effect_step 0x101cac 0x45 (by decide) 1 (.base 10 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101cb0 [0x81, 0xE2, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101cb0) (andR32Imm32Effect 0x101cb0 6 2 0x3ffffff)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101cb0 6 2 0x3ffffff).toInstrSpec (and_r32_imm32_effect_step 0x101cb0 0xe2 0x3ffffff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101cb6 [0x41, 0x89, 0x52, 0x30] (StorePre 0x101cb6 4 (fun s => AddrMode.addr (.base 10 (.d8 0x30)) s (0x101cb6 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101cb6 2 (.base 10 (.d8 0x30)))
      [.gpr 2, .gpr 10] [] [.rip] :=
    (movM32R32Effect_footprint 0x101cb6 2 (.base 10 (.d8 0x30))).toInstrSpec (mov_m32_r32_effect_step 0x101cb6 0x41 (by decide) 2 (.base 10 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101cba [0x25, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101cba) (andEaxImm32Effect 0x101cba 0x3ffffff)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x101cba 0x3ffffff).toInstrSpec (and_eax_imm32_effect_step 0x101cba 0x3ffffff) pre_rip
  have f5 : InstrSpec 0x101cbf [0x41, 0x89, 0x42, 0x34] (StorePre 0x101cbf 4 (fun s => AddrMode.addr (.base 10 (.d8 0x34)) s (0x101cbf + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101cbf 0 (.base 10 (.d8 0x34)))
      [.gpr 0, .gpr 10] [] [.rip] :=
    (movM32R32Effect_footprint 0x101cbf 0 (.base 10 (.d8 0x34))).toInstrSpec (mov_m32_r32_effect_step 0x101cbf 0x41 (by decide) 0 (.base 10 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101cc3 [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x101cc3) (addR64Imm8Effect 0x101cc3 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x101cc3 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x101cc3 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101cc7 [0x5B] (PopPre 0x101cc7) (popR64Effect 0x101cc7 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101cc7 1 3).toInstrSpec (pop_r64_effect_step 0x101cc7 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x101cc8 [0x41, 0x5C] (PopPre 0x101cc8) (popR64Effect 0x101cc8 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101cc8 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101cc8 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x101cca [0x41, 0x5D] (PopPre 0x101cca) (popR64Effect 0x101cca 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101cca 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101cca 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x101ccc [0x41, 0x5E] (PopPre 0x101ccc) (popR64Effect 0x101ccc 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101ccc 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101ccc 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x101cce [0x41, 0x5F] (PopPre 0x101cce) (popR64Effect 0x101cce 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101cce 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101cce 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x101cd0 [0x5D] (PopPre 0x101cd0) (popR64Effect 0x101cd0 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101cd0 1 5).toInstrSpec (pop_r64_effect_step 0x101cd0 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x101cd1 [0xC3] (RetPre 0x101cd1) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101cd1).toInstrSpec (ret_effect_step 0x101cd1) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cb0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (4, 4), (6, 6), (7, 7), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cb6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (4, 4), (6, 6), (7, 7), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cba) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 56), (4, 4), (6, 6), (7, 7), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cbf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 1), (2, 56), (4, 4), (6, 6), (7, 7), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cc3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 56), (4, 62), (6, 6), (7, 7), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cc7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 56), (3, 64), (4, 65), (6, 6), (7, 7), (9, 53), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cc8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 1), (2, 56), (3, 64), (4, 68), (6, 6), (7, 7), (9, 53), (10, 10), (12, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cca) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 1), (2, 56), (3, 64), (4, 71), (6, 6), (7, 7), (9, 53), (10, 10), (12, 67), (13, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ccc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 1), (2, 56), (3, 64), (4, 74), (6, 6), (7, 7), (9, 53), (10, 10), (12, 67), (13, 70), (14, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cce) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 59), (1, 1), (2, 56), (3, 64), (4, 77), (6, 6), (7, 7), (9, 53), (10, 10), (12, 67), (13, 70), (14, 73), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cd0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 59), (1, 1), (2, 56), (3, 64), (4, 80), (5, 79), (6, 6), (7, 7), (9, 53), (10, 10), (12, 67), (13, 70), (14, 73), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cd1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 84) (ρ' := [(0, 59), (1, 1), (2, 56), (3, 64), (4, 83), (5, 79), (6, 6), (7, 7), (9, 53), (10, 10), (12, 67), (13, 70), (14, 73), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) f13 (by decide) rfl rfl rfl (by decide)

theorem block_l101ca5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101ca5 :=
  Rest.liftedBlock (rest_l101ca5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101ca5 x hx)

theorem rest_l101e30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e30 bytes_l101e30) (entryMap (live .l101e30))
      2 0x101e30 bytes_l101e30 b_l101e30 := by
  have f0 : InstrSpec 0x101e30 [0x31, 0xD2] (fun s => s.RIP = 0x101e30) (xorR32R32Effect 0x101e30 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101e30 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x101e30 0xd2 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e32) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x101e32 0xfffffc79 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l101e30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e30 :=
  Rest.liftedBlock (rest_l101e30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e30 x hx)

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

theorem_by block_l101ab0_eval :
    program.runBlock (dialect code) ⟨.l101ab0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101af1_eval :
    program.runBlock (dialect code) ⟨.l101af1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101b40_eval :
    program.runBlock (dialect code) ⟨.l101b40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101b85_eval :
    program.runBlock (dialect code) ⟨.l101b85, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101bcd_eval :
    program.runBlock (dialect code) ⟨.l101bcd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101c13_eval :
    program.runBlock (dialect code) ⟨.l101c13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101c63_eval :
    program.runBlock (dialect code) ⟨.l101c63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101ca5_eval :
    program.runBlock (dialect code) ⟨.l101ca5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e30_eval :
    program.runBlock (dialect code) ⟨.l101e30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
