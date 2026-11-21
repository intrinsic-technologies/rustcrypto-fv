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

theorem rest_l104c90_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x104c90 bytes_l104c90) [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 83), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x104cee bytes_l104c90_1 b_l104c90_1 := by
  have f20 : InstrSpec 0x104cee [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x104cee) (leaR64Effect 0x104cee 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104cee 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x104cee 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x104cf3 [0xE8, 0x88, 0x55, 0x00, 0x00] (PushPre 0x104cf3 5) (callEffect (fun _ => 0x10a280) 0x104cf8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104cf3 0x10a280 0x104cf8).toInstrSpec (call_rel32_effect_step 0x104cf3 0x5588 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 85), (7, 83), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cf3) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 87), (5, 5), (6, 85), (7, 83), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f21 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem rest_l104c90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104c90 bytes_l104c90) (entryMap (live .l104c90))
      22 0x104c90 bytes_l104c90 b_l104c90 := by
  have f0 : InstrSpec 0x104c90 [0x41, 0x57] (PushPre 0x104c90 2) (pushR64Effect 0x104c90 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104c90 2 15).toInstrSpec (push_r64_rex_effect_step 0x104c90 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x104c92 [0x41, 0x56] (PushPre 0x104c92 2) (pushR64Effect 0x104c92 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104c92 2 14).toInstrSpec (push_r64_rex_effect_step 0x104c92 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x104c94 [0x41, 0x54] (PushPre 0x104c94 2) (pushR64Effect 0x104c94 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104c94 2 12).toInstrSpec (push_r64_rex_effect_step 0x104c94 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x104c96 [0x53] (PushPre 0x104c96 1) (pushR64Effect 0x104c96 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104c96 1 3).toInstrSpec (push_r64_effect_step 0x104c96 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x104c97 [0x48, 0x83, 0xEC, 0x68] (fun s => s.RIP = 0x104c97) (subR64Imm8Effect 0x104c97 4 0x68)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x104c97 4 0x68).toInstrSpec (sub_r64_imm8_effect_step 0x104c97 0x48 0xec 0x68 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104c9b [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x104c9b) (movR64R64Effect 0x104c9b 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x104c9b 14 6).toInstrSpec (mov_r64_r64_effect_step 0x104c9b 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104c9e [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x104c9e) (movR64R64Effect 0x104c9e 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x104c9e 3 7).toInstrSpec (mov_r64_r64_effect_step 0x104c9e 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104ca1 [0x48, 0x8B, 0x46, 0x38] (LoadPre 0x104ca1 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x104ca1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104ca1 0 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104ca1 0 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x104ca1 0x48 (by decide) 0 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x104ca5 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x104ca5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x104ca5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104ca5 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104ca5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x104ca5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x104caa [0x48, 0x8B, 0x46, 0x30] (LoadPre 0x104caa (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x104caa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104caa 0 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104caa 0 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x104caa 0x48 (by decide) 0 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x104cae [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x104cae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x104cae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104cae 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104cae 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x104cae 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x104cb3 [0x48, 0x8B, 0x46, 0x20] (LoadPre 0x104cb3 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x104cb3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104cb3 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104cb3 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x104cb3 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x104cb7 [0x48, 0x8B, 0x4E, 0x28] (LoadPre 0x104cb7 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x104cb7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104cb7 1 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104cb7 1 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x104cb7 0x48 (by decide) 1 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x104cbb [0x48, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x104cbb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x104cbb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104cbb 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104cbb 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x104cbb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x104cc0 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x104cc0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104cc0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104cc0 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104cc0 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x104cc0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x104cc5 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104cc5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104cc5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104cc5 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104cc5 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104cc5 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x104cce [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104cce 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104cce + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104cce (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104cce (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104cce 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x104cd7 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104cd7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104cd7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104cd7 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104cd7 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104cd7 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x104ce0 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104ce0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104ce0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104ce0 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104ce0 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104ce0 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x104ce9 [0x48, 0x8D, 0x7C, 0x24, 0x28] (fun s => s.RIP = 0x104ce9) (leaR64Effect 0x104ce9 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104ce9 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x104ce9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c92) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c94) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c96) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c97) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c9b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c9e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ca1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ca5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104caa) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cae) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 70), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cb3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cb7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cbb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cc0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cc5) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cce) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cd7) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ce0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ce9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 73), (1, 75), (3, 65), (4, 61), (5, 5), (6, 6), (7, 83), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cee) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l104c90_1 code

theorem block_l104c90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104c90 :=
  Rest.liftedBlock (rest_l104c90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104c90 x hx)

theorem rest_l104cf8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104cf8 bytes_l104cf8) (entryMap (live .l104cf8))
      4 0x104cf8 bytes_l104cf8 b_l104cf8 := by
  have f0 : InstrSpec 0x104cf8 [0xF6, 0xD0] (fun s => s.RIP = 0x104cf8) (notR8Effect 0x104cf8 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x104cf8 2 0).toInstrSpec (not_r8_effect_step 0x104cf8 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104cfa [0x24, 0x01] (fun s => s.RIP = 0x104cfa) (andAlImm8Effect 0x104cfa 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x104cfa 0x1).toInstrSpec (and_al_imm8_effect_step 0x104cfa 0x1) pre_rip
  have f2 : InstrSpec 0x104cfc [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x104cfc) (movzxR32R8Effect 0x104cfc 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x104cfc 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x104cfc 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104cff [0xE8, 0x4C, 0x30, 0x02, 0x00] (PushPre 0x104cff 5) (callEffect (fun _ => 0x127d50) 0x104d04)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104cff 0x127d50 0x104d04).toInstrSpec (call_rel32_effect_step 0x104cff 0x2304c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cfa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cfc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l104cf8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104cf8 :=
  Rest.liftedBlock (rest_l104cf8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104cf8 x hx)

theorem rest_l104d04 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104d04 bytes_l104d04) (entryMap (live .l104d04))
      3 0x104d04 bytes_l104d04 b_l104d04 := by
  have f0 : InstrSpec 0x104d04 [0x88, 0x44, 0x24, 0x08] (StorePre 0x104d04 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104d04 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x104d04 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x104d04 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x104d04 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104d08 [0x3C, 0x01] (fun s => s.RIP = 0x104d08) (cmpAlImm8Effect 0x104d08 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x104d08 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x104d08 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d08) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d0a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x104d0a 5 0xd5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104d04 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104d04 :=
  Rest.liftedBlock (rest_l104d04 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104d04 x hx)

theorem rest_l104d10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104d10 bytes_l104d10) (entryMap (live .l104d10))
      13 0x104d10 bytes_l104d10 b_l104d10 := by
  have f0 : InstrSpec 0x104d10 [0x4D, 0x8D, 0x7E, 0x20] (fun s => s.RIP = 0x104d10) (leaR64Effect 0x104d10 15 (.base 14 (.d8 0x20)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x104d10 15 (.base 14 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x104d10 0x4d (by decide) 7 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104d14 [0x49, 0x8B, 0x47, 0x18] (LoadPre 0x104d14 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x104d14 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d14 0 (.base 15 (.d8 0x18)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104d14 0 (.base 15 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104d14 0x49 (by decide) 0 (.base 15 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104d18 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x104d18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104d18 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104d18 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104d18 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x104d18 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104d1d [0x49, 0x8B, 0x47, 0x10] (LoadPre 0x104d1d (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x104d1d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d1d 0 (.base 15 (.d8 0x10)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104d1d 0 (.base 15 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104d1d 0x49 (by decide) 0 (.base 15 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x104d21 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x104d21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104d21 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104d21 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104d21 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x104d21 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x104d26 [0x49, 0x8B, 0x07] (LoadPre 0x104d26 (fun s => AddrMode.addr (.base 15 .none) s (0x104d26 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104d26 0 (.base 15 .none))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104d26 0 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x104d26 0x49 (by decide) 0 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x104d29 [0x49, 0x8B, 0x4F, 0x08] (LoadPre 0x104d29 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x104d29 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d29 1 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104d29 1 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104d29 0x49 (by decide) 1 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x104d2d [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x104d2d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104d2d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104d2d 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104d2d 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x104d2d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104d32 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x104d32 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104d32 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104d32 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104d32 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x104d32 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x104d37 [0x4C, 0x8D, 0x64, 0x24, 0x48] (fun s => s.RIP = 0x104d37) (leaR64Effect 0x104d37 12 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x104d37 12 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x104d37 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x104d3c [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x104d3c) (leaR64Effect 0x104d3c 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104d3c 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x104d3c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x104d41 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x104d41) (movR64R64Effect 0x104d41 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104d41 7 12).toInstrSpec (mov_r64_r64_effect_step 0x104d41 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104d44 [0xE8, 0x87, 0x55, 0x00, 0x00] (PushPre 0x104d44 5) (callEffect (fun _ => 0x10a2d0) 0x104d49)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104d44 0x10a2d0 0x104d49).toInstrSpec (call_rel32_effect_step 0x104d44 0x5587 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d14) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d18) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d1d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d21) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d26) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d29) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d2d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d32) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d37) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (12, 67), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d3c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (6, 69), (12, 67), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d41) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (6, 69), (7, 71), (12, 67), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d44) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 73), (5, 5), (6, 69), (7, 71), (12, 67), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2d0) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l104d10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104d10 :=
  Rest.liftedBlock (rest_l104d10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104d10 x hx)

theorem rest_l104d49 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104d49 bytes_l104d49) (entryMap (live .l104d49))
      3 0x104d49 bytes_l104d49 b_l104d49 := by
  have f0 : InstrSpec 0x104d49 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x104d49) (leaR64Effect 0x104d49 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104d49 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x104d49 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104d4e [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x104d4e) (movR64R64Effect 0x104d4e 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104d4e 6 12).toInstrSpec (mov_r64_r64_effect_step 0x104d4e 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104d51 [0xE8, 0x9A, 0x76, 0x01, 0x00] (PushPre 0x104d51 5) (callEffect (fun _ => 0x11c3f0) 0x104d56)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104d51 0x11c3f0 0x104d56).toInstrSpec (call_rel32_effect_step 0x104d51 0x1769a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d4e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d51) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3f0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l104d49 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104d49 :=
  Rest.liftedBlock (rest_l104d49 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104d49 x hx)

theorem rest_l104d56 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104d56 bytes_l104d56) (entryMap (live .l104d56))
      2 0x104d56 bytes_l104d56 b_l104d56 := by
  have f0 : InstrSpec 0x104d56 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x104d56) (movR64R64Effect 0x104d56 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104d56 7 15).toInstrSpec (mov_r64_r64_effect_step 0x104d56 0x4c 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104d59 [0xE8, 0x22, 0x36, 0x00, 0x00] (PushPre 0x104d59 5) (callEffect (fun _ => 0x108380) 0x104d5e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104d59 0x108380 0x104d5e).toInstrSpec (call_rel32_effect_step 0x104d59 0x3622 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d59) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108380) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l104d56 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104d56 :=
  Rest.liftedBlock (rest_l104d56 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104d56 x hx)

theorem rest_l104d5e_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x104d5e bytes_l104d5e) [(0, 89), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x104dac bytes_l104d5e_1 b_l104d5e_1 := by
  have f20 : InstrSpec 0x104dac [0x48, 0x89, 0x43, 0x18] (StorePre 0x104dac 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x104dac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dac 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104dac 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x104dac 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x104db0 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x104db0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x104db0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104db0 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104db0 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104db0 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x104db4 [0x48, 0x89, 0x43, 0x10] (StorePre 0x104db4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x104db4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104db4 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104db4 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x104db4 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x104db8 [0x49, 0x8B, 0x06] (LoadPre 0x104db8 (fun s => AddrMode.addr (.base 14 .none) s (0x104db8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104db8 0 (.base 14 .none))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104db8 0 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x104db8 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x104dbb [0x4D, 0x8B, 0x46, 0x08] (LoadPre 0x104dbb (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x104dbb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104dbb 8 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x104dbb 8 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104dbb 0x4d (by decide) 0 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x104dbf [0x4C, 0x89, 0x43, 0x08] (StorePre 0x104dbf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x104dbf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dbf 8 (.base 3 (.d8 0x8)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104dbf 8 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x104dbf 0x4c (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x104dc3 [0x48, 0x89, 0x03] (StorePre 0x104dc3 3 (fun s => AddrMode.addr (.base 3 .none) s (0x104dc3 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x104dc3 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104dc3 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x104dc3 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x104dc6 [0x48, 0x89, 0x4B, 0x20] (StorePre 0x104dc6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x104dc6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dc6 1 (.base 3 (.d8 0x20)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104dc6 1 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x104dc6 0x48 (by decide) 1 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x104dca [0x48, 0x89, 0x53, 0x28] (StorePre 0x104dca 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x104dca + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dca 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104dca 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x104dca 0x48 (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x104dce [0x48, 0x89, 0x73, 0x30] (StorePre 0x104dce 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x104dce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dce 6 (.base 3 (.d8 0x30)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104dce 6 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x104dce 0x48 (by decide) 6 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x104dd2 [0x48, 0x89, 0x7B, 0x38] (StorePre 0x104dd2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x104dd2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dd2 7 (.base 3 (.d8 0x38)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104dd2 7 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x104dd2 0x48 (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x104dd6 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x104dd6) (movR64R64Effect 0x104dd6 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x104dd6 0 3).toInstrSpec (mov_r64_r64_effect_step 0x104dd6 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x104dd9 [0x48, 0x83, 0xC4, 0x68] (fun s => s.RIP = 0x104dd9) (addR64Imm8Effect 0x104dd9 4 0x68)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104dd9 4 0x68).toInstrSpec (add_r64_imm8_effect_step 0x104dd9 0x48 0xc4 0x68 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x104ddd [0x5B] (PopPre 0x104ddd) (popR64Effect 0x104ddd 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104ddd 1 3).toInstrSpec (pop_r64_effect_step 0x104ddd 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f34 : InstrSpec 0x104dde [0x41, 0x5C] (PopPre 0x104dde) (popR64Effect 0x104dde 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104dde 2 12).toInstrSpec (pop_r64_rex_effect_step 0x104dde 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f35 : InstrSpec 0x104de0 [0x41, 0x5E] (PopPre 0x104de0) (popR64Effect 0x104de0 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104de0 2 14).toInstrSpec (pop_r64_rex_effect_step 0x104de0 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f36 : InstrSpec 0x104de2 [0x41, 0x5F] (PopPre 0x104de2) (popR64Effect 0x104de2 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104de2 2 15).toInstrSpec (pop_r64_rex_effect_step 0x104de2 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f37 : InstrSpec 0x104de4 [0xC3] (RetPre 0x104de4) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x104de4).toInstrSpec (ret_effect_step 0x104de4) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 89), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104db0) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104db4) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 92), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104db8) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dbb) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dbf) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dc3) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dc6) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dca) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 95), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dce) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 95), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dd2) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 95), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dd6) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 105), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dd9) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f32 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 105), (1, 71), (2, 75), (3, 3), (4, 107), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ddd) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 110) f33 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 111) (ρ' := [(0, 105), (1, 71), (2, 75), (3, 109), (4, 110), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dde) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f34 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 113) f34 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 114) (ρ' := [(0, 105), (1, 71), (2, 75), (3, 109), (4, 113), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (12, 112), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104de0) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f35 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 116) f35 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 117) (ρ' := [(0, 105), (1, 71), (2, 75), (3, 109), (4, 116), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (12, 112), (13, 13), (14, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104de2) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f36 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 119) f36 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 120) (ρ' := [(0, 105), (1, 71), (2, 75), (3, 109), (4, 119), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (12, 112), (13, 13), (14, 115), (15, 118), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104de4) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f37 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f37 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 123) (ρ' := [(0, 105), (1, 71), (2, 75), (3, 109), (4, 122), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (12, 112), (13, 13), (14, 115), (15, 118), (22, 22), (39, 39), (50, 50), (51, 51)]) f37 (by decide) rfl rfl rfl (by decide)

theorem rest_l104d5e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104d5e bytes_l104d5e) (entryMap (live .l104d5e))
      38 0x104d5e bytes_l104d5e b_l104d5e := by
  have f0 : InstrSpec 0x104d5e [0x49, 0x8B, 0x4E, 0x20] (LoadPre 0x104d5e (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x104d5e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d5e 1 (.base 14 (.d8 0x20)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104d5e 1 (.base 14 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x104d5e 0x49 (by decide) 1 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104d62 [0x49, 0x8B, 0x56, 0x28] (LoadPre 0x104d62 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x104d62 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d62 2 (.base 14 (.d8 0x28)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x104d62 2 (.base 14 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x104d62 0x49 (by decide) 2 (.base 14 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104d66 [0x49, 0x8B, 0x76, 0x30] (LoadPre 0x104d66 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x104d66 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d66 6 (.base 14 (.d8 0x30)))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x104d66 6 (.base 14 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x104d66 0x49 (by decide) 6 (.base 14 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x104d6a [0x49, 0x8B, 0x7E, 0x38] (LoadPre 0x104d6a (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x104d6a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d6a 7 (.base 14 (.d8 0x38)))
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x104d6a 7 (.base 14 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x104d6a 0x49 (by decide) 7 (.base 14 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x104d6e [0x88, 0x44, 0x24, 0x28] (StorePre 0x104d6e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104d6e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x104d6e 4 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x104d6e 4 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m8_r8_effect_step 0x104d6e 0 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x104d72 [0x48, 0x8D, 0x44, 0x24, 0x28] (fun s => s.RIP = 0x104d72) (leaR64Effect 0x104d72 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x104d72 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x104d72 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104d77 [0x0F, 0xB6, 0x44, 0x24, 0x28] (LoadPre 0x104d77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104d77 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x104d77 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x104d77 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x104d77 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x104d7c [0x4C, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x104d7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104d7c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104d7c 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x104d7c 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104d7c 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x104d81 [0x4C, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x104d81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104d81 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104d81 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x104d81 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104d81 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x104d86 [0x84, 0xC0] (fun s => s.RIP = 0x104d86) (testR8R8Effect 0x104d86 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x104d86 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x104d86 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x104d88 [0x49, 0x0F, 0x45, 0xC8] (fun s => s.RIP = 0x104d88) (atFlags (condHolds 5) (cmovR64R64Effect 0x104d88 4 1 8))
      [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x104d88 4 1 8 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x104d88 5 0x49 (by decide) 0xc8 (by decide) c)) pre_rip
  have f11 : InstrSpec 0x104d8c [0x84, 0xC0] (fun s => s.RIP = 0x104d8c) (testR8R8Effect 0x104d8c 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x104d8c 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x104d8c 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104d8e [0x49, 0x0F, 0x45, 0xD1] (fun s => s.RIP = 0x104d8e) (atFlags (condHolds 5) (cmovR64R64Effect 0x104d8e 4 2 9))
      [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x104d8e 4 2 9 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x104d8e 5 0x49 (by decide) 0xd1 (by decide) c)) pre_rip
  have f13 : InstrSpec 0x104d92 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x104d92 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104d92 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104d92 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x104d92 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104d92 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x104d97 [0x84, 0xC0] (fun s => s.RIP = 0x104d97) (testR8R8Effect 0x104d97 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x104d97 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x104d97 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x104d99 [0x49, 0x0F, 0x45, 0xF0] (fun s => s.RIP = 0x104d99) (atFlags (condHolds 5) (cmovR64R64Effect 0x104d99 4 6 8))
      [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x104d99 4 6 8 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x104d99 5 0x49 (by decide) 0xf0 (by decide) c)) pre_rip
  have f16 : InstrSpec 0x104d9d [0x4C, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x104d9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104d9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104d9d 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x104d9d 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x104d9d 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x104da2 [0x84, 0xC0] (fun s => s.RIP = 0x104da2) (testR8R8Effect 0x104da2 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x104da2 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x104da2 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x104da4 [0x49, 0x0F, 0x45, 0xF8] (fun s => s.RIP = 0x104da4) (atFlags (condHolds 5) (cmovR64R64Effect 0x104da4 4 7 8))
      [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (cmovR64R64Effect_footprint 0x104da4 4 7 8 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x104da4 5 0x49 (by decide) 0xf8 (by decide) c)) pre_rip
  have f19 : InstrSpec 0x104da8 [0x49, 0x8B, 0x46, 0x18] (LoadPre 0x104da8 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x104da8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104da8 0 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104da8 0 (.base 14 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104da8 0x49 (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d62) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d66) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d6a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d6e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d72) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d77) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d7c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 65), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d81) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 65), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d86) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 65), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d88) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 63), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 65), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d8c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 63), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 65), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d8e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 63), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 65), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d92) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 63), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 77), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d97) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 63), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 77), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d99) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 63), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 59), (8, 77), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d9d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 63), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 59), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104da2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 63), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 59), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104da4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 63), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104da8) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 71), (2, 75), (3, 3), (4, 4), (5, 5), (6, 81), (7, 87), (8, 83), (9, 67), (10, 10), (11, 11), (13, 13), (14, 14), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dac) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l104d5e_1 code

theorem block_l104d5e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104d5e :=
  Rest.liftedBlock (rest_l104d5e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104d5e x hx)

theorem rest_l104de5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104de5 bytes_l104de5) (entryMap (live .l104de5))
      6 0x104de5 bytes_l104de5 b_l104de5 := by
  have f0 : InstrSpec 0x104de5 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x104de5) (leaR64Effect 0x104de5 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104de5 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x104de5 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104dea [0x31, 0xFF] (fun s => s.RIP = 0x104dea) (xorR32R32Effect 0x104dea 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104dea 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x104dea 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x104dec [0x48, 0xC7, 0xC2, 0xE8, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x104dec) (movR64Imm32Effect 0x104dec 2 0x2022e8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x104dec 2 0x2022e8).toInstrSpec (mov_r64_imm32_effect_step 0x104dec 0x48 0xc2 (by decide) (by decide) (by decide) 0x2022e8) pre_rip
  have f3 : InstrSpec 0x104df3 [0x31, 0xC9] (fun s => s.RIP = 0x104df3) (xorR32R32Effect 0x104df3 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104df3 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x104df3 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x104df5 [0x49, 0xC7, 0xC1, 0xF0, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x104df5) (movR64Imm32Effect 0x104df5 9 0x2022f0)
      [] [] [.reg 9, .rip] :=
    (movR64Imm32Effect_footprint 0x104df5 9 0x2022f0).toInstrSpec (mov_r64_imm32_effect_step 0x104df5 0x49 0xc1 (by decide) (by decide) (by decide) 0x2022f0) pre_rip
  have f5 : InstrSpec 0x104dfc [0xE8, 0x07, 0x06, 0x01, 0x00] (PushPre 0x104dfc 5) (callEffect (fun _ => 0x115408) 0x104e01)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104dfc 0x115408 0x104e01).toInstrSpec (call_rel32_effect_step 0x104dfc 0x10607 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)]) (p' := 0x104dea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x104dec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x104df3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x104df5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)]) (p' := 0x104dfc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 59), (2, 57), (4, 63), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)]) (p' := 0x115408) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l104de5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104de5 :=
  Rest.liftedBlock (rest_l104de5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104de5 x hx)

theorem rest_l104e01 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104e01 bytes_l104e01) (entryMap (live .l104e01))
      5 0x104e01 bytes_l104e01 b_l104e01 := by
  have f0 : InstrSpec 0x104e01 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104e01) (fun _ => nopEffect 0x104e01 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x104e01 10).toInstrSpec (nop_m_effect_step 0x104e01 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104e0b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x104e0b) (fun _ => nopEffect 0x104e0b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x104e0b 5).toInstrSpec (nop_m_effect_step 0x104e0b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104e10 [0x48, 0x8B, 0x07] (LoadPre 0x104e10 (fun s => AddrMode.addr (.base 7 .none) s (0x104e10 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104e10 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104e10 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x104e10 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x104e13 [0x83, 0x38, 0x01] (LoadPre 0x104e13 (fun s => AddrMode.addr (.base 0 .none) s (0x104e13 + BitVec.ofNat 64 3)) 4) (cmpMImm8Effect 0x104e13 3 32 (.base 0 .none) 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x104e13 3 (.base 0 .none) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x104e13 (.base 0 .none) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e0b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e10) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e13) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57)]) (p' := 0x104e16) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x104e16 5 0x29) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104e01 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104e01 :=
  Rest.liftedBlock (rest_l104e01 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104e01 x hx)

theorem rest_l104e18 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104e18 bytes_l104e18) (entryMap (live .l104e18))
      9 0x104e18 bytes_l104e18 b_l104e18 := by
  have f0 : InstrSpec 0x104e18 [0x50] (PushPre 0x104e18 1) (pushR64Effect 0x104e18 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104e18 1 0).toInstrSpec (push_r64_effect_step 0x104e18 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x104e19 [0x48, 0x83, 0xC0, 0x04] (fun s => s.RIP = 0x104e19) (addR64Imm8Effect 0x104e19 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104e19 0 0x4).toInstrSpec (add_r64_imm8_effect_step 0x104e19 0x48 0xc0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104e1d [0x48, 0x89, 0x04, 0x24] (StorePre 0x104e1d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x104e1d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104e1d 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104e1d 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x104e1d 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104e21 [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x104e21) (movR64R64Effect 0x104e21 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x104e21 1 4).toInstrSpec (mov_r64_r64_effect_step 0x104e21 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104e24 [0xBA, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104e24) (movR32Imm32Effect 0x104e24 5 2 0x4)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104e24 5 2 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x104e24 0xba (by decide) 0x4) pre_rip
  have f5 : InstrSpec 0x104e29 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x104e29) (movR64R64Effect 0x104e29 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104e29 7 6).toInstrSpec (mov_r64_r64_effect_step 0x104e29 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104e2c [0x48, 0xC7, 0xC6, 0x99, 0x23, 0x20, 0x00] (fun s => s.RIP = 0x104e2c) (movR64Imm32Effect 0x104e2c 6 0x202399)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x104e2c 6 0x202399).toInstrSpec (mov_r64_imm32_effect_step 0x104e2c 0x48 0xc6 (by decide) (by decide) (by decide) 0x202399) pre_rip
  have f7 : InstrSpec 0x104e33 [0x49, 0xC7, 0xC0, 0xE0, 0x23, 0x20, 0x00] (fun s => s.RIP = 0x104e33) (movR64Imm32Effect 0x104e33 8 0x2023e0)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x104e33 8 0x2023e0).toInstrSpec (mov_r64_imm32_effect_step 0x104e33 0x49 0xc0 (by decide) (by decide) (by decide) 0x2023e0) pre_rip
  have f8 : InstrSpec 0x104e3a [0xE8, 0x01, 0x40, 0x02, 0x00] (PushPre 0x104e3a 5) (callEffect (fun _ => 0x128e40) 0x104e3f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104e3a 0x128e40 0x104e3f).toInstrSpec (call_rel32_effect_step 0x104e3a 0x24001 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 53), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e19) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e1d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e21) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 58), (3, 3), (4, 53), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e24) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 58), (2, 60), (3, 3), (4, 53), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e29) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 58), (2, 60), (3, 3), (4, 53), (5, 5), (6, 6), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e2c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 58), (2, 60), (3, 3), (4, 53), (5, 5), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e33) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 58), (2, 60), (3, 3), (4, 53), (5, 5), (7, 62), (8, 65), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x104e3a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 58), (2, 60), (3, 3), (4, 67), (5, 5), (7, 62), (8, 65), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x128e40) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l104e18 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104e18 :=
  Rest.liftedBlock (rest_l104e18 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104e18 x hx)

theorem rest_l104e3f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104e3f bytes_l104e3f) (entryMap (live .l104e3f))
      2 0x104e3f bytes_l104e3f b_l104e3f := by
  have f0 : InstrSpec 0x104e3f [0x59] (PopPre 0x104e3f) (popR64Effect 0x104e3f 1 1)
      [.gpr 4] [] [.reg 1, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104e3f 1 1).toInstrSpec (pop_r64_effect_step 0x104e3f 0x59 (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x104e40 [0xC3] (RetPre 0x104e40) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x104e40).toInstrSpec (ret_effect_step 0x104e40) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e40) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l104e3f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104e3f :=
  Rest.liftedBlock (rest_l104e3f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104e3f x hx)

theorem rest_l104e41 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104e41 bytes_l104e41) (entryMap (live .l104e41))
      4 0x104e41 bytes_l104e41 b_l104e41 := by
  have f0 : InstrSpec 0x104e41 [0xBA, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104e41) (movR32Imm32Effect 0x104e41 5 2 0x4)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104e41 5 2 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x104e41 0xba (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x104e46 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x104e46) (movR64R64Effect 0x104e46 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104e46 7 6).toInstrSpec (mov_r64_r64_effect_step 0x104e46 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104e49 [0x48, 0xC7, 0xC6, 0x95, 0x23, 0x20, 0x00] (fun s => s.RIP = 0x104e49) (movR64Imm32Effect 0x104e49 6 0x202395)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x104e49 6 0x202395).toInstrSpec (mov_r64_imm32_effect_step 0x104e49 0x48 0xc6 (by decide) (by decide) (by decide) 0x202395) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(6, 6)]) (p' := 0x104e46) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(6, 6), (7, 54)]) (p' := 0x104e49) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(7, 54)]) (p' := 0x104e50) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x104e50 0x2453b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l104e41 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104e41 :=
  Rest.liftedBlock (rest_l104e41 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104e41 x hx)

theorem rest_l129390 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129390 bytes_l129390) (entryMap (live .l129390))
      4 0x129390 bytes_l129390 b_l129390 := by
  have f0 : InstrSpec 0x129390 [0x48, 0x8B, 0x07] (LoadPre 0x129390 (fun s => AddrMode.addr (.base 7 .none) s (0x129390 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x129390 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129390 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x129390 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129393 [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x129393 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x129393 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129393 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x129393 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x129393 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129397 [0x48, 0x8B, 0x49, 0x18] (LoadPre 0x129397 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x129397 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129397 1 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x129397 1 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x129397 0x48 (by decide) 1 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12939b [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12939b) (movR64R64Effect 0x12939b 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12939b 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12939b 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (7, 7)]) (p' := 0x129393) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (7, 7)]) (p' := 0x129397) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (7, 7)]) (p' := 0x12939b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53)]) (p' := 0x12939e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129390 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129390 :=
  Rest.liftedBlock (rest_l129390 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129390 x hx)

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

theorem_by block_l104c90_eval :
    program.runBlock (dialect code) ⟨.l104c90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104cf8_eval :
    program.runBlock (dialect code) ⟨.l104cf8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104d04_eval :
    program.runBlock (dialect code) ⟨.l104d04, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104d10_eval :
    program.runBlock (dialect code) ⟨.l104d10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104d49_eval :
    program.runBlock (dialect code) ⟨.l104d49, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104d56_eval :
    program.runBlock (dialect code) ⟨.l104d56, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104d5e_eval :
    program.runBlock (dialect code) ⟨.l104d5e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104de5_eval :
    program.runBlock (dialect code) ⟨.l104de5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104e01_eval :
    program.runBlock (dialect code) ⟨.l104e01, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104e18_eval :
    program.runBlock (dialect code) ⟨.l104e18, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104e3f_eval :
    program.runBlock (dialect code) ⟨.l104e3f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104e41_eval :
    program.runBlock (dialect code) ⟨.l104e41, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129390_eval :
    program.runBlock (dialect code) ⟨.l129390, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
