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

theorem rest_l1211b0_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x1211b0 bytes_l1211b0) [(0, 78), (1, 80), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 84), (13, 13), (14, 86), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x1211f9 bytes_l1211b0_1 b_l1211b0_1 := by
  have f20 : InstrSpec 0x1211f9 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x1211f9) (movR64R64Effect 0x1211f9 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1211f9 7 12).toInstrSpec (mov_r64_r64_effect_step 0x1211f9 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1211fc [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1211fc) (movR64R64Effect 0x1211fc 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1211fc 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1211fc 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1211ff [0xE8, 0x2C, 0x37, 0xFF, 0xFF] (PushPre 0x1211ff 5) (callEffect (fun _ => 0x114930) 0x121204)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1211ff 0x114930 0x121204).toInstrSpec (call_rel32_effect_step 0x1211ff 0xffff372c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 78), (1, 80), (3, 67), (4, 63), (5, 5), (6, 6), (7, 88), (10, 10), (11, 11), (12, 84), (13, 13), (14, 86), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211fc) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 78), (1, 80), (3, 67), (4, 63), (5, 5), (6, 90), (7, 88), (10, 10), (11, 11), (12, 84), (13, 13), (14, 86), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211ff) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 78), (1, 80), (3, 67), (4, 92), (5, 5), (6, 90), (7, 88), (10, 10), (11, 11), (12, 84), (13, 13), (14, 86), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f22 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 94) (by decide) (by decide) rfl rfl

theorem rest_l1211b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1211b0 bytes_l1211b0) (entryMap (live .l1211b0))
      23 0x1211b0 bytes_l1211b0 b_l1211b0 := by
  have f0 : InstrSpec 0x1211b0 [0x41, 0x57] (PushPre 0x1211b0 2) (pushR64Effect 0x1211b0 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1211b0 2 15).toInstrSpec (push_r64_rex_effect_step 0x1211b0 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1211b2 [0x41, 0x56] (PushPre 0x1211b2 2) (pushR64Effect 0x1211b2 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1211b2 2 14).toInstrSpec (push_r64_rex_effect_step 0x1211b2 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1211b4 [0x41, 0x55] (PushPre 0x1211b4 2) (pushR64Effect 0x1211b4 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1211b4 2 13).toInstrSpec (push_r64_rex_effect_step 0x1211b4 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1211b6 [0x41, 0x54] (PushPre 0x1211b6 2) (pushR64Effect 0x1211b6 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1211b6 2 12).toInstrSpec (push_r64_rex_effect_step 0x1211b6 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1211b8 [0x53] (PushPre 0x1211b8 1) (pushR64Effect 0x1211b8 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1211b8 1 3).toInstrSpec (push_r64_effect_step 0x1211b8 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1211b9 [0x48, 0x81, 0xEC, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1211b9) (subR64Imm32Effect 0x1211b9 4 0x120)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1211b9 4 0x120).toInstrSpec (sub_r64_imm32_effect_step 0x1211b9 0x48 0xec 0x120 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1211c0 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x1211c0) (movR64R64Effect 0x1211c0 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1211c0 15 6).toInstrSpec (mov_r64_r64_effect_step 0x1211c0 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1211c3 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1211c3) (movR64R64Effect 0x1211c3 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1211c3 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1211c3 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1211c6 [0x48, 0x8B, 0x46, 0x20] (LoadPre 0x1211c6 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1211c6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1211c6 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1211c6 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1211c6 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1211ca [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1211ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1211ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1211ca 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1211ca 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1211ca 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1211cf [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x1211cf (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1211cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1211cf 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1211cf 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1211cf 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1211d3 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x1211d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1211d3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1211d3 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1211d3 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1211d3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1211d8 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x1211d8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1211d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1211d8 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1211d8 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1211d8 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1211dc [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x1211dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1211dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1211dc 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1211dc 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1211dc 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1211e1 [0x48, 0x8B, 0x06] (LoadPre 0x1211e1 (fun s => AddrMode.addr (.base 6 .none) s (0x1211e1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1211e1 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1211e1 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1211e1 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1211e4 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x1211e4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1211e4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1211e4 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1211e4 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1211e4 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1211e8 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x1211e8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1211e8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1211e8 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1211e8 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1211e8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1211ed [0x48, 0x89, 0x04, 0x24] (StorePre 0x1211ed 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1211ed + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1211ed 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1211ed 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1211ed 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1211f1 [0x4C, 0x8D, 0x64, 0x24, 0x70] (fun s => s.RIP = 0x1211f1) (leaR64Effect 0x1211f1 12 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x1211f1 12 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x1211f1 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1211f6 [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x1211f6) (movR64R64Effect 0x1211f6 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1211f6 14 4).toInstrSpec (mov_r64_r64_effect_step 0x1211f6 0x49 0xe6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211b2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211b4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211b6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211b8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211b9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211c0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211c3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211c6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211ca) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211cf) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211d3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211d8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211dc) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211e1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211e4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 80), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211e8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 80), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211ed) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 78), (1, 80), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211f1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 78), (1, 80), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 84), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211f6) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (1, 80), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 84), (13, 13), (14, 86), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211f9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1211b0_1 code

theorem block_l1211b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1211b0 :=
  Rest.liftedBlock (rest_l1211b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1211b0 x hx)

theorem rest_l121204 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121204 bytes_l121204) (entryMap (live .l121204))
      3 0x121204 bytes_l121204 b_l121204 := by
  have f0 : InstrSpec 0x121204 [0x48, 0x8D, 0x7C, 0x24, 0x29] (fun s => s.RIP = 0x121204) (leaR64Effect 0x121204 7 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x121204 7 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (lea_r64_effect_step 0x121204 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x121209 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x121209) (movR64R64Effect 0x121209 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x121209 6 12).toInstrSpec (mov_r64_r64_effect_step 0x121209 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12120c [0xE8, 0xBF, 0x36, 0xFF, 0xFF] (PushPre 0x12120c 5) (callEffect (fun _ => 0x1148d0) 0x121211)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12120c 0x1148d0 0x121211).toInstrSpec (call_rel32_effect_step 0x12120c 0xffff36bf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121209) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12120c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l121204 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121204 :=
  Rest.liftedBlock (rest_l121204 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121204 x hx)

theorem rest_l121211 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121211 bytes_l121211) (entryMap (live .l121211))
      14 0x121211 bytes_l121211 b_l121211 := by
  have f0 : InstrSpec 0x121211 [0x49, 0x8B, 0x47, 0x48] (LoadPre 0x121211 (fun s => AddrMode.addr (.base 15 (.d8 0x48)) s (0x121211 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121211 0 (.base 15 (.d8 0x48)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121211 0 (.base 15 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x121211 0x49 (by decide) 0 (.base 15 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x121215 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x121215 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121215 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121215 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121215 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x121215 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12121a [0x49, 0x8B, 0x47, 0x40] (LoadPre 0x12121a (fun s => AddrMode.addr (.base 15 (.d8 0x40)) s (0x12121a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12121a 0 (.base 15 (.d8 0x40)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12121a 0 (.base 15 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x12121a 0x49 (by decide) 0 (.base 15 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12121e [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x12121e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12121e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12121e 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12121e 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12121e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x121223 [0x49, 0x8B, 0x47, 0x38] (LoadPre 0x121223 (fun s => AddrMode.addr (.base 15 (.d8 0x38)) s (0x121223 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121223 0 (.base 15 (.d8 0x38)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121223 0 (.base 15 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x121223 0x49 (by decide) 0 (.base 15 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x121227 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x121227 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121227 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121227 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121227 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x121227 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12122c [0x49, 0x8B, 0x47, 0x28] (LoadPre 0x12122c (fun s => AddrMode.addr (.base 15 (.d8 0x28)) s (0x12122c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12122c 0 (.base 15 (.d8 0x28)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12122c 0 (.base 15 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x12122c 0x49 (by decide) 0 (.base 15 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x121230 [0x49, 0x8B, 0x4F, 0x30] (LoadPre 0x121230 (fun s => AddrMode.addr (.base 15 (.d8 0x30)) s (0x121230 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121230 1 (.base 15 (.d8 0x30)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x121230 1 (.base 15 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x121230 0x49 (by decide) 1 (.base 15 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x121234 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x121234 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x121234 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121234 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121234 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x121234 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x121239 [0x48, 0x89, 0x04, 0x24] (StorePre 0x121239 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x121239 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121239 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121239 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x121239 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x12123d [0x4C, 0x8D, 0x64, 0x24, 0x70] (fun s => s.RIP = 0x12123d) (leaR64Effect 0x12123d 12 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x12123d 12 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x12123d 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x121242 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x121242) (movR64R64Effect 0x121242 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x121242 6 4).toInstrSpec (mov_r64_r64_effect_step 0x121242 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x121245 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x121245) (movR64R64Effect 0x121245 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x121245 7 12).toInstrSpec (mov_r64_r64_effect_step 0x121245 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x121248 [0xE8, 0xE3, 0x36, 0xFF, 0xFF] (PushPre 0x121248 5) (callEffect (fun _ => 0x114930) 0x12124d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x121248 0x114930 0x12124d).toInstrSpec (call_rel32_effect_step 0x121248 0xffff36e3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121215) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12121a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12121e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121223) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121227) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12122c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121230) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121234) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121239) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12123d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 68), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121242) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 70), (10, 10), (11, 11), (12, 68), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121245) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 72), (10, 10), (11, 11), (12, 68), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121248) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 74), (5, 5), (6, 70), (7, 72), (10, 10), (11, 11), (12, 68), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 76) (by decide) (by decide) rfl rfl

theorem block_l121211 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121211 :=
  Rest.liftedBlock (rest_l121211 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121211 x hx)

theorem rest_l12124d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12124d bytes_l12124d) (entryMap (live .l12124d))
      4 0x12124d bytes_l12124d b_l12124d := by
  have f0 : InstrSpec 0x12124d [0x4C, 0x8D, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x12124d) (leaR64Effect 0x12124d 13 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x12124d 13 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x12124d 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x121255 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x121255) (movR64R64Effect 0x121255 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x121255 7 13).toInstrSpec (mov_r64_r64_effect_step 0x121255 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x121258 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x121258) (movR64R64Effect 0x121258 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x121258 6 12).toInstrSpec (mov_r64_r64_effect_step 0x121258 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12125b [0xE8, 0x70, 0x36, 0xFF, 0xFF] (PushPre 0x12125b 5) (callEffect (fun _ => 0x1148d0) 0x121260)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12125b 0x1148d0 0x121260).toInstrSpec (call_rel32_effect_step 0x12125b 0xffff3670 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121255) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121258) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12125b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l12124d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12124d :=
  Rest.liftedBlock (rest_l12124d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12124d x hx)

theorem rest_l121260 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121260 bytes_l121260) (entryMap (live .l121260))
      3 0x121260 bytes_l121260 b_l121260 := by
  have f0 : InstrSpec 0x121260 [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x121260) (movR32Imm32Effect 0x121260 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x121260 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x121260 0xbe (by decide) 0x20) pre_rip
  have f1 : InstrSpec 0x121265 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x121265) (movR64R64Effect 0x121265 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x121265 7 13).toInstrSpec (mov_r64_r64_effect_step 0x121265 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x121268 [0xE8, 0xF3, 0x44, 0x00, 0x00] (PushPre 0x121268 5) (callEffect (fun _ => 0x125760) 0x12126d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x121268 0x125760 0x12126d).toInstrSpec (call_rel32_effect_step 0x121268 0x44f3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121265) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121268) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125760) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l121260 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121260 :=
  Rest.liftedBlock (rest_l121260 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121260 x hx)

theorem rest_l12126d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12126d bytes_l12126d) (entryMap (live .l12126d))
      16 0x12126d bytes_l12126d b_l12126d := by
  have f0 : InstrSpec 0x12126d [0x48, 0xC7, 0x44, 0x24, 0x49, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12126d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x12126d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12126d (.sib 4 none 0 (.d8 0x49)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12126d (.sib 4 none 0 (.d8 0x49)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12126d 0x48 (by decide) (.sib 4 none 0 (.d8 0x49)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x121276 [0x48, 0xC7, 0x44, 0x24, 0x51, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121276 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x121276 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121276 (.sib 4 none 0 (.d8 0x51)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121276 (.sib 4 none 0 (.d8 0x51)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121276 0x48 (by decide) (.sib 4 none 0 (.d8 0x51)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12127f [0x48, 0xC7, 0x44, 0x24, 0x59, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12127f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x12127f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12127f (.sib 4 none 0 (.d8 0x59)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12127f (.sib 4 none 0 (.d8 0x59)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12127f 0x48 (by decide) (.sib 4 none 0 (.d8 0x59)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x121288 [0x48, 0xC7, 0x44, 0x24, 0x61, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121288 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x121288 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121288 (.sib 4 none 0 (.d8 0x61)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121288 (.sib 4 none 0 (.d8 0x61)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121288 0x48 (by decide) (.sib 4 none 0 (.d8 0x61)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x121291 [0x88, 0x44, 0x24, 0x28] (StorePre 0x121291 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x121291 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x121291 4 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x121291 4 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m8_r8_effect_step 0x121291 0 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x121295 [0xC6, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121295 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x121295 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x121295 (.sib 4 none 0 (.d32 0xb0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x121295 (.sib 4 none 0 (.d32 0xb0)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x121295 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12129d [0x48, 0xC7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12129d 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x12129d + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x12129d (.sib 4 none 0 (.d32 0xa8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12129d (.sib 4 none 0 (.d32 0xa8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12129d 0x48 (by decide) (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1212a9 [0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1212a9 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1212a9 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1212a9 (.sib 4 none 0 (.d32 0xa0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1212a9 (.sib 4 none 0 (.d32 0xa0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1212a9 0x48 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1212b5 [0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1212b5 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1212b5 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1212b5 (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1212b5 (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1212b5 0x48 (by decide) (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1212c1 [0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1212c1 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1212c1 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1212c1 (.sib 4 none 0 (.d32 0x90)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1212c1 (.sib 4 none 0 (.d32 0x90)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1212c1 0x48 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1212cd [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1212cd 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1212cd + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1212cd (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1212cd (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1212cd 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1212d9 [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1212d9 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1212d9 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1212d9 (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1212d9 (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1212d9 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1212e5 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1212e5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1212e5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1212e5 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1212e5 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1212e5 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1212ee [0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1212ee 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1212ee + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1212ee (.sib 4 none 0 (.d8 0x70)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1212ee (.sib 4 none 0 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1212ee 0x48 (by decide) (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1212f7 [0x41, 0x8B, 0x7F, 0x50] (LoadPre 0x1212f7 (fun s => AddrMode.addr (.base 15 (.d8 0x50)) s (0x1212f7 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1212f7 7 (.base 15 (.d8 0x50)))
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR32M32Effect_footprint 0x1212f7 7 (.base 15 (.d8 0x50))).toInstrSpec (mov_r32_m32_effect_step 0x1212f7 0x41 (by decide) 7 (.base 15 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1212fb [0xE8, 0x50, 0x6A, 0x00, 0x00] (PushPre 0x1212fb 5) (callEffect (fun _ => 0x127d50) 0x121300)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1212fb 0x127d50 0x121300).toInstrSpec (call_rel32_effect_step 0x1212fb 0x6a50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121276) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12127f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121288) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121291) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121295) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12129d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212a9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212b5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212c1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212cd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212d9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212e5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212ee) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212f7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1212fb) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 69), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l12126d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12126d :=
  Rest.liftedBlock (rest_l12126d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12126d x hx)

theorem rest_l121300 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121300 bytes_l121300) (entryMap (live .l121300))
      11 0x121300 bytes_l121300 b_l121300 := by
  have f0 : InstrSpec 0x121300 [0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121300 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x121300 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121300 (.sib 4 none 0 (.d32 0xb8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121300 (.sib 4 none 0 (.d32 0xb8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121300 0x48 (by decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12130c [0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12130c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x12130c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x12130c (.sib 4 none 0 (.d32 0xc0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12130c (.sib 4 none 0 (.d32 0xc0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12130c 0x48 (by decide) (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x121318 [0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121318 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x121318 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121318 (.sib 4 none 0 (.d32 0xc8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121318 (.sib 4 none 0 (.d32 0xc8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121318 0x48 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x121324 [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121324 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x121324 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121324 (.sib 4 none 0 (.d32 0xd0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121324 (.sib 4 none 0 (.d32 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121324 0x48 (by decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x121330 [0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121330 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x121330 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121330 (.sib 4 none 0 (.d32 0xd8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121330 (.sib 4 none 0 (.d32 0xd8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121330 0x48 (by decide) (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12133c [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12133c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x12133c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x12133c (.sib 4 none 0 (.d32 0xe0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12133c (.sib 4 none 0 (.d32 0xe0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12133c 0x48 (by decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x121348 [0x48, 0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121348 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x121348 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121348 (.sib 4 none 0 (.d32 0xe8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121348 (.sib 4 none 0 (.d32 0xe8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121348 0x48 (by decide) (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x121354 [0x48, 0xC7, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121354 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x121354 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121354 (.sib 4 none 0 (.d32 0xf0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x121354 (.sib 4 none 0 (.d32 0xf0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x121354 0x48 (by decide) (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x121360 [0xC6, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x00] (StorePre 0x121360 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x121360 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x121360 (.sib 4 none 0 (.d32 0xf8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x121360 (.sib 4 none 0 (.d32 0xf8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x121360 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x121368 [0x31, 0xC9] (fun s => s.RIP = 0x121368) (xorR32R32Effect 0x121368 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x121368 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x121368 0xc9 (by decide)) pre_rip
  have f10 : InstrSpec 0x12136a [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x12136a) (fun _ => nopEffect 0x12136a 6)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12136a 6).toInstrSpec (nop_m_effect_step 0x12136a [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x12130c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x121318) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x121324) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x121330) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x12133c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x121348) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x121354) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x121360) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5)]) (p' := 0x121368) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (4, 4), (5, 5)]) (p' := 0x12136a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 62), (4, 4), (5, 5)]) (p' := 0x121370) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 65) (by decide) rfl

theorem block_l121300 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121300 :=
  Rest.liftedBlock (rest_l121300 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121300 x hx)

theorem rest_l121370 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121370 bytes_l121370) (entryMap (live .l121370))
      10 0x121370 bytes_l121370 b_l121370 := by
  have f0 : InstrSpec 0x121370 [0x0F, 0xB6, 0x54, 0x0C, 0x28] (LoadPre 0x121370 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d8 0x28)) s (0x121370 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x121370 5 2 (.sib 4 (some 1) 0 (.d8 0x28)))
      [.gpr 4, .gpr 1] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x121370 5 2 (.sib 4 (some 1) 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x121370 2 (.sib 4 (some 1) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x121375 [0x88, 0x04, 0x24] (StorePre 0x121375 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x121375 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x121375 3 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x121375 3 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x121375 0 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x121378 [0x0F, 0xB6, 0x74, 0x0C, 0x70] (LoadPre 0x121378 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d8 0x70)) s (0x121378 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x121378 5 6 (.sib 4 (some 1) 0 (.d8 0x70)))
      [.gpr 4, .gpr 1] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x121378 5 6 (.sib 4 (some 1) 0 (.d8 0x70))).toInstrSpec (movzx_r32_m8_effect_step 0x121378 6 (.sib 4 (some 1) 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12137d [0x0F, 0xB6, 0x3C, 0x24] (LoadPre 0x12137d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12137d + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12137d 4 7 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x12137d 4 7 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x12137d 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x121381 [0x40, 0x84, 0xFF] (fun s => s.RIP = 0x121381) (testR8R8Effect 0x121381 3 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x121381 3 7 7).toInstrSpec (test_r8_r8_rex_effect_step 0x121381 0x40 0xff (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x121384 [0x0F, 0x45, 0xD6] (fun s => s.RIP = 0x121384) (atFlags (condHolds 5) (cmovR32R32Effect 0x121384 3 2 6))
      [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR32R32Effect_footprint 0x121384 3 2 6 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x121384 5 0xd6 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x121387 [0x88, 0x94, 0x0C, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x121387 7 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xb8)) s (0x121387 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x121387 7 2 (.sib 4 (some 1) 0 (.d32 0xb8)))
      [.gpr 2, .gpr 4, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x121387 7 2 (.sib 4 (some 1) 0 (.d32 0xb8))).toInstrSpec (mov_m8_r8_effect_step 0x121387 2 (by decide) (.sib 4 (some 1) 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12138e [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x12138e) (incR64Effect 0x12138e 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x12138e 1).toInstrSpec (inc_r64_effect_step 0x12138e 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x121391 [0x48, 0x83, 0xF9, 0x41] (fun s => s.RIP = 0x121391) (cmpR64Imm8Effect 0x121391 1 0x41)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x121391 1 0x41).toInstrSpec (cmp_r64_imm8_effect_step 0x121391 0x48 0xf9 0x41 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5)]) (p' := 0x121375) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5)]) (p' := 0x121378) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 56)]) (p' := 0x12137d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x121381) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 56), (7, 58), (19, 60)]) (p' := 0x121384) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 56), (7, 58), (19, 60)]) (p' := 0x121387) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 56), (7, 58), (19, 60)]) (p' := 0x12138e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 62), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x121391) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 62), (4, 4), (5, 5), (6, 56), (7, 58), (19, 67)]) (p' := 0x121395) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel8_effect_step 0x121395 5 0xd9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l121370 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121370 :=
  Rest.liftedBlock (rest_l121370 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121370 x hx)

theorem rest_l121397 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121397 bytes_l121397) (entryMap (live .l121397))
      8 0x121397 bytes_l121397 b_l121397 := by
  have f0 : InstrSpec 0x121397 [0xC6, 0x44, 0x24, 0x48, 0x00] (StorePre 0x121397 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x121397 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x121397 (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x121397 (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x121397 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12139c [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12139c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12139c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12139c (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12139c (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12139c 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1213a5 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1213a5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1213a5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1213a5 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1213a5 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1213a5 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1213ae [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1213ae 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1213ae + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1213ae (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1213ae (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1213ae 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1213b7 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1213b7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1213b7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1213b7 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1213b7 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1213b7 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1213c0 [0x0F, 0xB6, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x1213c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1213c0 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1213c0 8 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1213c0 8 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (movzx_r32_m8_effect_step 0x1213c0 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1213c8 [0x48, 0x83, 0xF8, 0x05] (fun s => s.RIP = 0x1213c8) (cmpR64Imm8Effect 0x1213c8 0 0x5)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1213c8 0 0x5).toInstrSpec (cmp_r64_imm8_effect_step 0x1213c8 0x48 0xf8 0x5 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x12139c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1213a5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1213ae) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1213b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1213c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (4, 4), (5, 5)]) (p' := 0x1213c8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (4, 4), (5, 5), (16, 60), (19, 61)]) (p' := 0x1213cc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x1213cc 7 0x7d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l121397 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121397 :=
  Rest.liftedBlock (rest_l121397 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121397 x hx)

theorem rest_l1213ce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1213ce bytes_l1213ce) (entryMap (live .l1213ce))
      0 0x1213ce bytes_l1213ce b_l1213ce := by
  exact Rest.cut

theorem block_l1213ce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1213ce :=
  Rest.liftedBlock (rest_l1213ce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1213ce x hx)

theorem rest_l1213d5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1213d5 bytes_l1213d5) (entryMap (live .l1213d5))
      2 0x1213d5 bytes_l1213d5 b_l1213d5 := by
  have f0 : InstrSpec 0x1213d5 [0xBA, 0x21, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1213d5) (movR32Imm32Effect 0x1213d5 5 2 0x21)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1213d5 5 2 0x21).toInstrSpec (mov_r32_imm32_effect_step 0x1213d5 0xba (by decide) 0x21) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1213da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1213da 0x1d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1213d5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1213d5 :=
  Rest.liftedBlock (rest_l1213d5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1213d5 x hx)

theorem rest_l1213dc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1213dc bytes_l1213dc) (entryMap (live .l1213dc))
      5 0x1213dc bytes_l1213dc b_l1213dc := by
  have f0 : InstrSpec 0x1213dc [0xBE, 0x41, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1213dc) (movR32Imm32Effect 0x1213dc 5 6 0x41)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1213dc 5 6 0x41).toInstrSpec (mov_r32_imm32_effect_step 0x1213dc 0xbe (by decide) 0x41) pre_rip
  have f1 : InstrSpec 0x1213e1 [0xBA, 0x21, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1213e1) (movR32Imm32Effect 0x1213e1 5 2 0x21)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1213e1 5 2 0x21).toInstrSpec (mov_r32_imm32_effect_step 0x1213e1 0xba (by decide) 0x21) pre_rip
  have f2 : InstrSpec 0x1213e6 [0x31, 0xFF] (fun s => s.RIP = 0x1213e6) (xorR32R32Effect 0x1213e6 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1213e6 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x1213e6 0xff (by decide)) pre_rip
  have f3 : InstrSpec 0x1213e8 [0x48, 0xC7, 0xC1, 0x90, 0x33, 0x20, 0x00] (fun s => s.RIP = 0x1213e8) (movR64Imm32Effect 0x1213e8 1 0x203390)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x1213e8 1 0x203390).toInstrSpec (mov_r64_imm32_effect_step 0x1213e8 0x48 0xc1 (by decide) (by decide) (by decide) 0x203390) pre_rip
  have f4 : InstrSpec 0x1213ef [0xE8, 0x6C, 0x87, 0x00, 0x00] (PushPre 0x1213ef 5) (callEffect (fun _ => 0x129b60) 0x1213f4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1213ef 0x129b60 0x1213f4).toInstrSpec (call_rel32_effect_step 0x1213ef 0x876c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 7)]) (p' := 0x1213e1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 53), (7, 7)]) (p' := 0x1213e6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 53), (7, 57)]) (p' := 0x1213e8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 55), (4, 4), (5, 5), (6, 53), (7, 57)]) (p' := 0x1213ef) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 55), (4, 61), (5, 5), (6, 53), (7, 57)]) (p' := 0x129b60) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1213dc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1213dc :=
  Rest.liftedBlock (rest_l1213dc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1213dc x hx)

theorem rest_l1213f4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1213f4 bytes_l1213f4) (entryMap (live .l1213f4))
      1 0x1213f4 bytes_l1213f4 b_l1213f4 := by
  have f0 : InstrSpec 0x1213f4 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1213f4) (movR32Imm32Effect 0x1213f4 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1213f4 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1213f4 0xba (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1213f9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1213f4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1213f4 :=
  Rest.liftedBlock (rest_l1213f4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1213f4 x hx)

theorem rest_l1213f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1213f9 bytes_l1213f9) (entryMap (live .l1213f9))
      3 0x1213f9 bytes_l1213f9 b_l1213f9 := by
  have f0 : InstrSpec 0x1213f9 [0x48, 0x8D, 0x7C, 0x24, 0x28] (fun s => s.RIP = 0x1213f9) (leaR64Effect 0x1213f9 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1213f9 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x1213f9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1213fe [0x48, 0x8D, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1213fe) (leaR64Effect 0x1213fe 6 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1213fe 6 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x1213fe 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x121406 [0xFF, 0x15, 0xC4, 0x29, 0x0E, 0x00] (GoesTo (CallMemPre 0x121406 (.rip 0xe29c4)) (callEffect (callMemPtr 0x121406 (.rip 0xe29c4)) (0x121406 + BitVec.ofNat 64 (callMemLen (.rip 0xe29c4)))) 0x12a820) (callEffect (callMemPtr 0x121406 (.rip 0xe29c4)) (0x121406 + BitVec.ofNat 64 (callMemLen (.rip 0xe29c4))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x121406 (.rip 0xe29c4)).toInstrSpec (call_m64_effect_step 0x121406 (.rip 0xe29c4) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1213fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121406) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f2 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1213f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1213f9 :=
  Rest.liftedBlock (rest_l1213f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1213f9 x hx)

theorem rest_l12140c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12140c bytes_l12140c) (entryMap (live .l12140c))
      18 0x12140c bytes_l12140c b_l12140c := by
  have f0 : InstrSpec 0x12140c [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x12140c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12140c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12140c 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12140c 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x12140c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x121411 [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x121411 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x121411 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121411 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x121411 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x121411 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x121416 [0x48, 0x89, 0x03] (StorePre 0x121416 3 (fun s => AddrMode.addr (.base 3 .none) s (0x121416 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x121416 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x121416 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x121416 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x121419 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x121419 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x121419 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121419 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x121419 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x121419 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12141d [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x12141d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12141d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12141d 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12141d 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x12141d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x121422 [0x48, 0x89, 0x43, 0x10] (StorePre 0x121422 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x121422 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121422 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x121422 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x121422 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x121426 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x121426 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x121426 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121426 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121426 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x121426 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x12142b [0x48, 0x89, 0x43, 0x18] (StorePre 0x12142b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x12142b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12142b 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12142b 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12142b 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12142f [0x0F, 0xB6, 0x44, 0x24, 0x48] (LoadPre 0x12142f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12142f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12142f 5 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x12142f 5 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m8_effect_step 0x12142f 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x121434 [0x88, 0x43, 0x20] (StorePre 0x121434 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x121434 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x121434 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x121434 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x121434 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x121437 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x121437) (movR64R64Effect 0x121437 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x121437 0 3).toInstrSpec (mov_r64_r64_effect_step 0x121437 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12143a [0x48, 0x81, 0xC4, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x12143a) (addR64Imm32Effect 0x12143a 4 0x120)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x12143a 4 0x120).toInstrSpec (add_r64_imm32_effect_step 0x12143a 0x48 0xc4 0x120 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x121441 [0x5B] (PopPre 0x121441) (popR64Effect 0x121441 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x121441 1 3).toInstrSpec (pop_r64_effect_step 0x121441 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x121442 [0x41, 0x5C] (PopPre 0x121442) (popR64Effect 0x121442 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x121442 2 12).toInstrSpec (pop_r64_rex_effect_step 0x121442 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x121444 [0x41, 0x5D] (PopPre 0x121444) (popR64Effect 0x121444 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x121444 2 13).toInstrSpec (pop_r64_rex_effect_step 0x121444 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x121446 [0x41, 0x5E] (PopPre 0x121446) (popR64Effect 0x121446 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x121446 2 14).toInstrSpec (pop_r64_rex_effect_step 0x121446 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f16 : InstrSpec 0x121448 [0x41, 0x5F] (PopPre 0x121448) (popR64Effect 0x121448 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x121448 2 15).toInstrSpec (pop_r64_rex_effect_step 0x121448 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f17 : InstrSpec 0x12144a [0xC3] (RetPre 0x12144a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12144a).toInstrSpec (ret_effect_step 0x12144a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121411) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121416) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121419) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12141d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121422) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121426) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12142b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12142f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121434) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121437) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12143a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 55), (2, 2), (3, 3), (4, 70), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121441) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 68), (1, 55), (2, 2), (3, 72), (4, 73), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121442) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 68), (1, 55), (2, 2), (3, 72), (4, 76), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121444) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 79) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 80) (ρ' := [(0, 68), (1, 55), (2, 2), (3, 72), (4, 79), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121446) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 68), (1, 55), (2, 2), (3, 72), (4, 82), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121448) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 85) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 68), (1, 55), (2, 2), (3, 72), (4, 85), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 81), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12144a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 89) (ρ' := [(0, 68), (1, 55), (2, 2), (3, 72), (4, 88), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 81), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) f17 (by decide) rfl rfl rfl (by decide)

theorem block_l12140c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12140c :=
  Rest.liftedBlock (rest_l12140c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12140c x hx)

theorem rest_l12144b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12144b bytes_l12144b) (entryMap (live .l12144b))
      7 0x12144b bytes_l12144b b_l12144b := by
  have f0 : InstrSpec 0x12144b [0xC7, 0x44, 0x24, 0x70, 0x03, 0x00, 0x00, 0x00] (StorePre 0x12144b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12144b + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x12144b 8 (.sib 4 none 0 (.d8 0x70)) 0x3)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x12144b 8 (.sib 4 none 0 (.d8 0x70)) 0x3).toInstrSpec (mov_m32_imm32_effect_step 0x12144b (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x121453 [0x48, 0x8D, 0x54, 0x24, 0x70] (fun s => s.RIP = 0x121453) (leaR64Effect 0x121453 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x121453 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x121453 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x121458 [0xBE, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x121458) (movR32Imm32Effect 0x121458 5 6 0xb)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x121458 5 6 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x121458 0xbe (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x12145d [0x48, 0xC7, 0xC7, 0x30, 0x2E, 0x20, 0x00] (fun s => s.RIP = 0x12145d) (movR64Imm32Effect 0x12145d 7 0x202e30)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x12145d 7 0x202e30).toInstrSpec (mov_r64_imm32_effect_step 0x12145d 0x48 0xc7 (by decide) (by decide) (by decide) 0x202e30) pre_rip
  have f4 : InstrSpec 0x121464 [0x48, 0xC7, 0xC1, 0x10, 0x2E, 0x20, 0x00] (fun s => s.RIP = 0x121464) (movR64Imm32Effect 0x121464 1 0x202e10)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x121464 1 0x202e10).toInstrSpec (mov_r64_imm32_effect_step 0x121464 0x48 0xc1 (by decide) (by decide) (by decide) 0x202e10) pre_rip
  have f5 : InstrSpec 0x12146b [0x49, 0xC7, 0xC0, 0x40, 0x2E, 0x20, 0x00] (fun s => s.RIP = 0x12146b) (movR64Imm32Effect 0x12146b 8 0x202e40)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x12146b 8 0x202e40).toInstrSpec (mov_r64_imm32_effect_step 0x12146b 0x49 0xc0 (by decide) (by decide) (by decide) 0x202e40) pre_rip
  have f6 : InstrSpec 0x121472 [0xE8, 0x29, 0x81, 0x00, 0x00] (PushPre 0x121472 5) (callEffect (fun _ => 0x1295a0) 0x121477)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x121472 0x1295a0 0x121477).toInstrSpec (call_rel32_effect_step 0x121472 0x8129 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x121453) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (4, 4), (5, 5)]) (p' := 0x121458) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56)]) (p' := 0x12145d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x121464) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x12146b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x121472) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1295a0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l12144b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12144b :=
  Rest.liftedBlock (rest_l12144b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12144b x hx)

theorem rest_l121477 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121477 bytes_l121477) (entryMap (live .l121477))
      1 0x121477 bytes_l121477 b_l121477 := by
  have f0 : InstrSpec 0x121477 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x121477) (fun _ => nopEffect 0x121477 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x121477 9).toInstrSpec (nop_m_effect_step 0x121477 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121480) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l121477 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121477 :=
  Rest.liftedBlock (rest_l121477 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121477 x hx)

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

theorem_by block_l1211b0_eval :
    program.runBlock (dialect code) ⟨.l1211b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121204_eval :
    program.runBlock (dialect code) ⟨.l121204, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121211_eval :
    program.runBlock (dialect code) ⟨.l121211, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12124d_eval :
    program.runBlock (dialect code) ⟨.l12124d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121260_eval :
    program.runBlock (dialect code) ⟨.l121260, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12126d_eval :
    program.runBlock (dialect code) ⟨.l12126d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121300_eval :
    program.runBlock (dialect code) ⟨.l121300, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121370_eval :
    program.runBlock (dialect code) ⟨.l121370, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121397_eval :
    program.runBlock (dialect code) ⟨.l121397, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1213ce_eval :
    program.runBlock (dialect code) ⟨.l1213ce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1213d5_eval :
    program.runBlock (dialect code) ⟨.l1213d5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1213dc_eval :
    program.runBlock (dialect code) ⟨.l1213dc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1213f4_eval :
    program.runBlock (dialect code) ⟨.l1213f4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1213f9_eval :
    program.runBlock (dialect code) ⟨.l1213f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12140c_eval :
    program.runBlock (dialect code) ⟨.l12140c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12144b_eval :
    program.runBlock (dialect code) ⟨.l12144b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121477_eval :
    program.runBlock (dialect code) ⟨.l121477, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
