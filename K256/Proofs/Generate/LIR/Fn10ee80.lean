import K256.Proofs.Generate.LIR.CallPre
import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Generate.LIR.Generated.Values

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

theorem rest_l10ee80_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x10ee80 bytes_l10ee80) [(0, 68), (1, 87), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      9 0x10eed7 bytes_l10ee80_1 b_l10ee80_1 := by
  have f20 : InstrSpec 0x10eed7 [0x48, 0x8B, 0x40, 0x08] (LoadPre 0x10eed7 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10eed7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eed7 0 (.base 0 (.d8 0x8)))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10eed7 0 (.base 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10eed7 0x48 (by decide) 0 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10eedb [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10eedb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10eedb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eedb 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eedb 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x10eedb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10eee3 [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10eee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10eee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eee3 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eee3 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10eee3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x10eeeb [0x4C, 0x8D, 0xB4, 0x24, 0x08, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x10eeeb) (leaR64Effect 0x10eeeb 14 (.sib 4 none 0 (.d32 0xf08)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10eeeb 14 (.sib 4 none 0 (.d32 0xf08))).toInstrSpec (lea_r64_effect_step 0x10eeeb 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xf08)) (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x10eef3 [0x4C, 0x8D, 0x2D, 0x26, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x10eef3) (leaR64Effect 0x10eef3 13 (.rip 0x1b926))
      [] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10eef3 13 (.rip 0x1b926)).toInstrSpec (lea_r64_effect_step 0x10eef3 0x4c (by decide) 5 (.rip 0x1b926) (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10eefa [0xBA, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10eefa) (movR32Imm32Effect 0x10eefa 5 2 0x98)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10eefa 5 2 0x98).toInstrSpec (mov_r32_imm32_effect_step 0x10eefa 0xba (by decide) 0x98) pre_rip
  have f26 : InstrSpec 0x10eeff [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10eeff) (movR64R64Effect 0x10eeff 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10eeff 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10eeff 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10ef02 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x10ef02) (movR64R64Effect 0x10ef02 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10ef02 6 8).toInstrSpec (mov_r64_r64_effect_step 0x10ef02 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10ef05 [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x10ef05 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10ef08) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10ef08)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10ef05 13 0x10ef08).toInstrSpec (call_r64_rex_effect_step 0x10ef05 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 87), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eedb) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 89), (1, 87), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eee3) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 87), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eeeb) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 87), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eef3) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 89), (1, 87), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 95), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eefa) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 89), (1, 87), (2, 97), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 95), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eeff) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 89), (1, 87), (2, 97), (3, 70), (4, 66), (5, 5), (7, 99), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 95), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef02) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 89), (1, 87), (2, 97), (3, 70), (4, 66), (5, 5), (6, 101), (7, 99), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 95), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef05) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f28 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 89), (1, 87), (2, 97), (3, 70), (4, 103), (5, 5), (6, 101), (7, 99), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 95), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f28 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 105) (by decide) (by decide) rfl rfl

theorem rest_l10ee80 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ee80 bytes_l10ee80) (entryMap (live .l10ee80))
      29 0x10ee80 bytes_l10ee80 b_l10ee80 := by
  have f0 : InstrSpec 0x10ee80 [0x41, 0x57] (PushPre 0x10ee80 2) (pushR64Effect 0x10ee80 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ee80 2 15).toInstrSpec (push_r64_rex_effect_step 0x10ee80 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10ee82 [0x41, 0x56] (PushPre 0x10ee82 2) (pushR64Effect 0x10ee82 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ee82 2 14).toInstrSpec (push_r64_rex_effect_step 0x10ee82 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10ee84 [0x41, 0x55] (PushPre 0x10ee84 2) (pushR64Effect 0x10ee84 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ee84 2 13).toInstrSpec (push_r64_rex_effect_step 0x10ee84 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10ee86 [0x41, 0x54] (PushPre 0x10ee86 2) (pushR64Effect 0x10ee86 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ee86 2 12).toInstrSpec (push_r64_rex_effect_step 0x10ee86 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10ee88 [0x53] (PushPre 0x10ee88 1) (pushR64Effect 0x10ee88 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ee88 1 3).toInstrSpec (push_r64_effect_step 0x10ee88 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10ee89 [0x48, 0x81, 0xEC, 0x00, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x10ee89) (subR64Imm32Effect 0x10ee89 4 0x1000)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10ee89 4 0x1000).toInstrSpec (sub_r64_imm32_effect_step 0x10ee89 0x48 0xec 0x1000 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10ee90 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10ee90 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ee90 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10ee90 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10ee90 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10ee90 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10ee98 [0x48, 0x81, 0xEC, 0x20, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x10ee98) (subR64Imm32Effect 0x10ee98 4 0x720)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10ee98 4 0x720).toInstrSpec (sub_r64_imm32_effect_step 0x10ee98 0x48 0xec 0x720 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ee9f [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x10ee9f) (movR64R64Effect 0x10ee9f 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ee9f 0 6).toInstrSpec (mov_r64_r64_effect_step 0x10ee9f 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10eea2 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10eea2) (movR64R64Effect 0x10eea2 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10eea2 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10eea2 0x48 0xfb (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10eea5 [0x4C, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x10eea5) (leaR64Effect 0x10eea5 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x10eea5 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10eea5 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10eeaa [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10eeaa) (movR32Imm32Effect 0x10eeaa 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10eeaa 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10eeaa 0xb9 (by decide) 0xf) pre_rip
  have f12 : InstrSpec 0x10eeaf [0x4C, 0x89, 0xC7] (fun s => s.RIP = 0x10eeaf) (movR64R64Effect 0x10eeaf 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10eeaf 7 8).toInstrSpec (mov_r64_r64_effect_step 0x10eeaf 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10eeb2 [0x48, 0xC7, 0xC6, 0xC8, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10eeb2) (movR64Imm32Effect 0x10eeb2 6 0x202bc8)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10eeb2 6 0x202bc8).toInstrSpec (mov_r64_imm32_effect_step 0x10eeb2 0x48 0xc6 (by decide) (by decide) (by decide) 0x202bc8) pre_rip
  have f14 : InstrSpec 0x10eeb9 [0xF3, 0x48, 0xA5] (RepPre 0x10eeb9 (RepMovsqPre 0x10eeb9)) (repMovsqEffect 0x10eeb9)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10eeb9).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10eeb9 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x10eebc [0x48, 0x8B, 0x48, 0x18] (LoadPre 0x10eebc (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10eebc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eebc 1 (.base 0 (.d8 0x18)))
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10eebc 1 (.base 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10eebc 0x48 (by decide) 1 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10eec0 [0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x10eec0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10eec0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eec0 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eec0 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x10eec0 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10eec8 [0x48, 0x8B, 0x48, 0x10] (LoadPre 0x10eec8 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10eec8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eec8 1 (.base 0 (.d8 0x10)))
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10eec8 1 (.base 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10eec8 0x48 (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10eecc [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x10eecc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10eecc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eecc 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eecc 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x10eecc 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x10eed4 [0x48, 0x8B, 0x08] (LoadPre 0x10eed4 (fun s => AddrMode.addr (.base 0 .none) s (0x10eed4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10eed4 1 (.base 0 .none))
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10eed4 1 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10eed4 0x48 (by decide) 1 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee82) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee84) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee86) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee88) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee89) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee90) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee98) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee9f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eea2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (3, 70), (4, 66), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eea5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 68), (3, 70), (4, 66), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eeaa) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 68), (1, 74), (3, 70), (4, 66), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eeaf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 68), (1, 74), (3, 70), (4, 66), (5, 5), (6, 6), (7, 76), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eeb2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 68), (1, 74), (3, 70), (4, 66), (5, 5), (6, 78), (7, 76), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eeb9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 68), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eebc) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 68), (1, 81), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eec0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 68), (1, 81), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eec8) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 68), (1, 84), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eecc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 68), (1, 84), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eed4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 68), (1, 87), (3, 70), (4, 66), (5, 5), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eed7) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10ee80_1 code

theorem block_l10ee80 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ee80 :=
  Rest.liftedBlock (rest_l10ee80 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ee80 x hx)

theorem rest_l10ef08_3 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 159) code lifted (codeRange 0x10ef08 bytes_l10ef08) [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x10f05d bytes_l10ef08_3 b_l10ef08_3 := by
  have f60 : InstrSpec 0x10f05d [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10f05d) (movR64Imm32Effect 0x10f05d 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10f05d 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10f05d 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f61 : InstrSpec 0x10f064 [0xF3, 0x48, 0xA5] (RepPre 0x10f064 (RepMovsqPre 0x10f064)) (repMovsqEffect 0x10f064)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f064).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f064 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f62 : InstrSpec 0x10f067 [0x48, 0x8D, 0xBC, 0x24, 0x90, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x10f067) (leaR64Effect 0x10f067 7 (.sib 4 none 0 (.d32 0xe90)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f067 7 (.sib 4 none 0 (.d32 0xe90))).toInstrSpec (lea_r64_effect_step 0x10f067 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe90)) (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x10f06f [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f06f) (movR32Imm32Effect 0x10f06f 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f06f 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f06f 0xb9 (by decide) 0xf) pre_rip
  have f64 : InstrSpec 0x10f074 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10f074) (movR64Imm32Effect 0x10f074 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10f074 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10f074 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f65 : InstrSpec 0x10f07b [0xF3, 0x48, 0xA5] (RepPre 0x10f07b (RepMovsqPre 0x10f07b)) (repMovsqEffect 0x10f07b)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f07b).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f07b 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f66 : InstrSpec 0x10f07e [0x4C, 0x8D, 0x64, 0x24, 0x08] (fun s => s.RIP = 0x10f07e) (leaR64Effect 0x10f07e 12 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x10f07e 12 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10f07e 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x10f083 [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x10f083) (movR32Imm32Effect 0x10f083 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10f083 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x10f083 0xba (by decide) 0x3c0) pre_rip
  have f68 : InstrSpec 0x10f088 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10f088) (movR64R64Effect 0x10f088 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f088 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10f088 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x10f08b [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10f08b) (movR64R64Effect 0x10f08b 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f08b 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10f08b 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10f08e [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x10f08e 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f091) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f091)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10f08e 13 0x10f091).toInstrSpec (call_r64_rex_effect_step 0x10f08e 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f60 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (6, 159), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f064) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f067) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f62 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f06f) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 53), (1, 164), (3, 3), (4, 4), (5, 5), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f074) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f64 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 53), (1, 164), (3, 3), (4, 4), (5, 5), (6, 166), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f07b) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.exec (n := 168) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f07e) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f66 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f083) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f67 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f088) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f68 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f08b) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f69 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (6, 175), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f08e) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f70 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 177), (5, 5), (6, 175), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f70 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 179) (by decide) (by decide) rfl rfl

theorem rest_l10ef08_2 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 124) code lifted (codeRange 0x10ef08 bytes_l10ef08) [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]
      31 0x10efea bytes_l10ef08_2 b_l10ef08_2 := by
  have f40 : InstrSpec 0x10efea [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10efea) (movR64Imm32Effect 0x10efea 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10efea 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10efea 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f41 : InstrSpec 0x10eff1 [0xF3, 0x48, 0xA5] (RepPre 0x10eff1 (RepMovsqPre 0x10eff1)) (repMovsqEffect 0x10eff1)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10eff1).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10eff1 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f42 : InstrSpec 0x10eff4 [0x48, 0x8D, 0xBC, 0x24, 0x38, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x10eff4) (leaR64Effect 0x10eff4 7 (.sib 4 none 0 (.d32 0xc38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10eff4 7 (.sib 4 none 0 (.d32 0xc38))).toInstrSpec (lea_r64_effect_step 0x10eff4 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc38)) (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x10effc [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10effc) (movR32Imm32Effect 0x10effc 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10effc 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10effc 0xb9 (by decide) 0xf) pre_rip
  have f44 : InstrSpec 0x10f001 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10f001) (movR64Imm32Effect 0x10f001 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10f001 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10f001 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f45 : InstrSpec 0x10f008 [0xF3, 0x48, 0xA5] (RepPre 0x10f008 (RepMovsqPre 0x10f008)) (repMovsqEffect 0x10f008)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f008).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f008 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f46 : InstrSpec 0x10f00b [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x10f00b) (leaR64Effect 0x10f00b 7 (.sib 4 none 0 (.d32 0xcb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f00b 7 (.sib 4 none 0 (.d32 0xcb0))).toInstrSpec (lea_r64_effect_step 0x10f00b 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xcb0)) (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10f013 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f013) (movR32Imm32Effect 0x10f013 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f013 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f013 0xb9 (by decide) 0xf) pre_rip
  have f48 : InstrSpec 0x10f018 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10f018) (movR64Imm32Effect 0x10f018 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10f018 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10f018 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f49 : InstrSpec 0x10f01f [0xF3, 0x48, 0xA5] (RepPre 0x10f01f (RepMovsqPre 0x10f01f)) (repMovsqEffect 0x10f01f)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f01f).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f01f 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f50 : InstrSpec 0x10f022 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x0D, 0x00, 0x00] (fun s => s.RIP = 0x10f022) (leaR64Effect 0x10f022 7 (.sib 4 none 0 (.d32 0xd28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f022 7 (.sib 4 none 0 (.d32 0xd28))).toInstrSpec (lea_r64_effect_step 0x10f022 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd28)) (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10f02a [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f02a) (movR32Imm32Effect 0x10f02a 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f02a 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f02a 0xb9 (by decide) 0xf) pre_rip
  have f52 : InstrSpec 0x10f02f [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10f02f) (movR64Imm32Effect 0x10f02f 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10f02f 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10f02f 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f53 : InstrSpec 0x10f036 [0xF3, 0x48, 0xA5] (RepPre 0x10f036 (RepMovsqPre 0x10f036)) (repMovsqEffect 0x10f036)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f036).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f036 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f54 : InstrSpec 0x10f039 [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x0D, 0x00, 0x00] (fun s => s.RIP = 0x10f039) (leaR64Effect 0x10f039 7 (.sib 4 none 0 (.d32 0xda0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f039 7 (.sib 4 none 0 (.d32 0xda0))).toInstrSpec (lea_r64_effect_step 0x10f039 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xda0)) (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10f041 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f041) (movR32Imm32Effect 0x10f041 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f041 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f041 0xb9 (by decide) 0xf) pre_rip
  have f56 : InstrSpec 0x10f046 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10f046) (movR64Imm32Effect 0x10f046 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10f046 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10f046 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f57 : InstrSpec 0x10f04d [0xF3, 0x48, 0xA5] (RepPre 0x10f04d (RepMovsqPre 0x10f04d)) (repMovsqEffect 0x10f04d)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10f04d).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10f04d 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f58 : InstrSpec 0x10f050 [0x48, 0x8D, 0xBC, 0x24, 0x18, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x10f050) (leaR64Effect 0x10f050 7 (.sib 4 none 0 (.d32 0xe18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f050 7 (.sib 4 none 0 (.d32 0xe18))).toInstrSpec (lea_r64_effect_step 0x10f050 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe18)) (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10f058 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f058) (movR32Imm32Effect 0x10f058 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10f058 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10f058 0xb9 (by decide) 0xf) pre_rip
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (6, 124), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eff1) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eff4) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10effc) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 53), (1, 129), (3, 3), (4, 4), (5, 5), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f001) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f44 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 53), (1, 129), (3, 3), (4, 4), (5, 5), (6, 131), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f008) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f00b) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f46 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f013) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 53), (1, 136), (3, 3), (4, 4), (5, 5), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f018) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f48 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 53), (1, 136), (3, 3), (4, 4), (5, 5), (6, 138), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f01f) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f022) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f50 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f02a) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 53), (1, 143), (3, 3), (4, 4), (5, 5), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f02f) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 53), (1, 143), (3, 3), (4, 4), (5, 5), (6, 145), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f036) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f039) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f041) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 53), (1, 150), (3, 3), (4, 4), (5, 5), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f046) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f56 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 53), (1, 150), (3, 3), (4, 4), (5, 5), (6, 152), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f04d) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.exec (n := 154) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f050) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f58 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f058) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f05d) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10ef08_3 hstride code

theorem rest_l10ef08_1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x10ef08 bytes_l10ef08) [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (6, 87), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      51 0x10ef7b bytes_l10ef08_1 b_l10ef08_1 := by
  have f20 : InstrSpec 0x10ef7b [0xF3, 0x48, 0xA5] (RepPre 0x10ef7b (RepMovsqPre 0x10ef7b)) (repMovsqEffect 0x10ef7b)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ef7b).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ef7b 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f21 : InstrSpec 0x10ef7e [0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x10ef7e) (leaR64Effect 0x10ef7e 7 (.sib 4 none 0 (.d32 0x9e0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ef7e 7 (.sib 4 none 0 (.d32 0x9e0))).toInstrSpec (lea_r64_effect_step 0x10ef7e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x9e0)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10ef86 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ef86) (movR32Imm32Effect 0x10ef86 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ef86 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10ef86 0xb9 (by decide) 0xf) pre_rip
  have f23 : InstrSpec 0x10ef8b [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10ef8b) (movR64Imm32Effect 0x10ef8b 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ef8b 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10ef8b 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f24 : InstrSpec 0x10ef92 [0xF3, 0x48, 0xA5] (RepPre 0x10ef92 (RepMovsqPre 0x10ef92)) (repMovsqEffect 0x10ef92)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ef92).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ef92 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f25 : InstrSpec 0x10ef95 [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x10ef95) (leaR64Effect 0x10ef95 7 (.sib 4 none 0 (.d32 0xa58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ef95 7 (.sib 4 none 0 (.d32 0xa58))).toInstrSpec (lea_r64_effect_step 0x10ef95 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa58)) (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10ef9d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ef9d) (movR32Imm32Effect 0x10ef9d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ef9d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10ef9d 0xb9 (by decide) 0xf) pre_rip
  have f27 : InstrSpec 0x10efa2 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10efa2) (movR64Imm32Effect 0x10efa2 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10efa2 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10efa2 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f28 : InstrSpec 0x10efa9 [0xF3, 0x48, 0xA5] (RepPre 0x10efa9 (RepMovsqPre 0x10efa9)) (repMovsqEffect 0x10efa9)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10efa9).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10efa9 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f29 : InstrSpec 0x10efac [0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x10efac) (leaR64Effect 0x10efac 7 (.sib 4 none 0 (.d32 0xad0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10efac 7 (.sib 4 none 0 (.d32 0xad0))).toInstrSpec (lea_r64_effect_step 0x10efac 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xad0)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10efb4 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10efb4) (movR32Imm32Effect 0x10efb4 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10efb4 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10efb4 0xb9 (by decide) 0xf) pre_rip
  have f31 : InstrSpec 0x10efb9 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10efb9) (movR64Imm32Effect 0x10efb9 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10efb9 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10efb9 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f32 : InstrSpec 0x10efc0 [0xF3, 0x48, 0xA5] (RepPre 0x10efc0 (RepMovsqPre 0x10efc0)) (repMovsqEffect 0x10efc0)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10efc0).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10efc0 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f33 : InstrSpec 0x10efc3 [0x4C, 0x8D, 0xBC, 0x24, 0x48, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x10efc3) (leaR64Effect 0x10efc3 15 (.sib 4 none 0 (.d32 0xb48)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10efc3 15 (.sib 4 none 0 (.d32 0xb48))).toInstrSpec (lea_r64_effect_step 0x10efc3 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xb48)) (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10efcb [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10efcb) (movR32Imm32Effect 0x10efcb 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10efcb 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10efcb 0xb9 (by decide) 0xf) pre_rip
  have f35 : InstrSpec 0x10efd0 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10efd0) (movR64R64Effect 0x10efd0 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10efd0 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10efd0 0x4c 0xff (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10efd3 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10efd3) (movR64Imm32Effect 0x10efd3 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10efd3 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10efd3 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f37 : InstrSpec 0x10efda [0xF3, 0x48, 0xA5] (RepPre 0x10efda (RepMovsqPre 0x10efda)) (repMovsqEffect 0x10efda)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10efda).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10efda 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f38 : InstrSpec 0x10efdd [0x48, 0x8D, 0xBC, 0x24, 0xC0, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x10efdd) (leaR64Effect 0x10efdd 7 (.sib 4 none 0 (.d32 0xbc0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10efdd 7 (.sib 4 none 0 (.d32 0xbc0))).toInstrSpec (lea_r64_effect_step 0x10efdd 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xbc0)) (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10efe5 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10efe5) (movR32Imm32Effect 0x10efe5 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10efe5 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10efe5 0xb9 (by decide) 0xf) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef7e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef86) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 53), (1, 92), (3, 3), (4, 4), (5, 5), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef8b) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 53), (1, 92), (3, 3), (4, 4), (5, 5), (6, 94), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef92) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef95) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef9d) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 53), (1, 99), (3, 3), (4, 4), (5, 5), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efa2) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 53), (1, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efa9) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efac) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efb4) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 53), (1, 106), (3, 3), (4, 4), (5, 5), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efb9) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 53), (1, 106), (3, 3), (4, 4), (5, 5), (6, 108), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efc0) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efc3) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efcb) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efd0) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (7, 115), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efd3) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (6, 117), (7, 115), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efda) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efdd) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efe5) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10efea) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10ef08_2 hstride code

theorem rest_l10ef08 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ef08 bytes_l10ef08) (entryMap (live .l10ef08))
      71 0x10ef08 bytes_l10ef08 b_l10ef08 := by
  have f0 : InstrSpec 0x10ef08 [0x48, 0x8D, 0x84, 0x24, 0x88, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x10ef08) (leaR64Effect 0x10ef08 0 (.sib 4 none 0 (.d32 0x788)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10ef08 0 (.sib 4 none 0 (.d32 0x788))).toInstrSpec (lea_r64_effect_step 0x10ef08 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x788)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10ef10 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ef10) (movR32Imm32Effect 0x10ef10 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ef10 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10ef10 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x10ef15 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10ef15) (movR64R64Effect 0x10ef15 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ef15 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10ef15 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10ef18 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10ef18) (movR64Imm32Effect 0x10ef18 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ef18 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10ef18 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f4 : InstrSpec 0x10ef1f [0xF3, 0x48, 0xA5] (RepPre 0x10ef1f (RepMovsqPre 0x10ef1f)) (repMovsqEffect 0x10ef1f)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ef1f).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ef1f 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x10ef22 [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x10ef22) (leaR64Effect 0x10ef22 7 (.sib 4 none 0 (.d32 0x800)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ef22 7 (.sib 4 none 0 (.d32 0x800))).toInstrSpec (lea_r64_effect_step 0x10ef22 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x800)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10ef2a [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ef2a) (movR32Imm32Effect 0x10ef2a 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ef2a 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10ef2a 0xb9 (by decide) 0xf) pre_rip
  have f7 : InstrSpec 0x10ef2f [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10ef2f) (movR64Imm32Effect 0x10ef2f 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ef2f 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10ef2f 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f8 : InstrSpec 0x10ef36 [0xF3, 0x48, 0xA5] (RepPre 0x10ef36 (RepMovsqPre 0x10ef36)) (repMovsqEffect 0x10ef36)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ef36).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ef36 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x10ef39 [0x48, 0x8D, 0xBC, 0x24, 0x78, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x10ef39) (leaR64Effect 0x10ef39 7 (.sib 4 none 0 (.d32 0x878)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ef39 7 (.sib 4 none 0 (.d32 0x878))).toInstrSpec (lea_r64_effect_step 0x10ef39 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x878)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ef41 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ef41) (movR32Imm32Effect 0x10ef41 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ef41 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10ef41 0xb9 (by decide) 0xf) pre_rip
  have f11 : InstrSpec 0x10ef46 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10ef46) (movR64Imm32Effect 0x10ef46 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ef46 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10ef46 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f12 : InstrSpec 0x10ef4d [0xF3, 0x48, 0xA5] (RepPre 0x10ef4d (RepMovsqPre 0x10ef4d)) (repMovsqEffect 0x10ef4d)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ef4d).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ef4d 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x10ef50 [0x48, 0x8D, 0xBC, 0x24, 0xF0, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x10ef50) (leaR64Effect 0x10ef50 7 (.sib 4 none 0 (.d32 0x8f0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ef50 7 (.sib 4 none 0 (.d32 0x8f0))).toInstrSpec (lea_r64_effect_step 0x10ef50 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x8f0)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10ef58 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ef58) (movR32Imm32Effect 0x10ef58 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ef58 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10ef58 0xb9 (by decide) 0xf) pre_rip
  have f15 : InstrSpec 0x10ef5d [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10ef5d) (movR64Imm32Effect 0x10ef5d 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ef5d 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10ef5d 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  have f16 : InstrSpec 0x10ef64 [0xF3, 0x48, 0xA5] (RepPre 0x10ef64 (RepMovsqPre 0x10ef64)) (repMovsqEffect 0x10ef64)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ef64).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ef64 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x10ef67 [0x48, 0x8D, 0xBC, 0x24, 0x68, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x10ef67) (leaR64Effect 0x10ef67 7 (.sib 4 none 0 (.d32 0x968)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ef67 7 (.sib 4 none 0 (.d32 0x968))).toInstrSpec (lea_r64_effect_step 0x10ef67 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x968)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10ef6f [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ef6f) (movR32Imm32Effect 0x10ef6f 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ef6f 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10ef6f 0xb9 (by decide) 0xf) pre_rip
  have f19 : InstrSpec 0x10ef74 [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x10ef74) (movR64Imm32Effect 0x10ef74 6 0x202c40)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ef74 6 0x202c40).toInstrSpec (mov_r64_imm32_effect_step 0x10ef74 0x48 0xc6 (by decide) (by decide) (by decide) 0x202c40) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef10) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef15) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef18) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef1f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef22) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef2a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef2f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef36) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef39) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef41) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 71), (3, 3), (4, 4), (5, 5), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef46) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef4d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef50) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef58) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 53), (1, 78), (3, 3), (4, 4), (5, 5), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef5d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 53), (1, 78), (3, 3), (4, 4), (5, 5), (6, 80), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef64) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef67) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef6f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef74) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (6, 87), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ef7b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10ef08_1 hstride code

theorem block_l10ef08 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ef08 :=
  Rest.liftedBlock (rest_l10ef08 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ef08 x hx)

theorem rest_l10f091 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f091 bytes_l10f091) (entryMap (live .l10f091))
      4 0x10f091 bytes_l10f091 b_l10f091 := by
  have f0 : InstrSpec 0x10f091 [0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x10f091) (leaR64Effect 0x10f091 7 (.sib 4 none 0 (.d32 0x3c8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10f091 7 (.sib 4 none 0 (.d32 0x3c8))).toInstrSpec (lea_r64_effect_step 0x10f091 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x3c8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f099 [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x10f099) (movR32Imm32Effect 0x10f099 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10f099 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x10f099 0xba (by decide) 0x3c0) pre_rip
  have f2 : InstrSpec 0x10f09e [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10f09e) (movR64R64Effect 0x10f09e 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f09e 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10f09e 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f0a1 [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x10f0a1 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0a4) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0a4)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10f0a1 13 0x10f0a4).toInstrSpec (call_r64_rex_effect_step 0x10f0a1 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f099) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f09e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10f091 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f091 :=
  Rest.liftedBlock (rest_l10f091 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f091 x hx)

theorem rest_l10f0a4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f0a4 bytes_l10f0a4) (entryMap (live .l10f0a4))
      5 0x10f0a4 bytes_l10f0a4 b_l10f0a4 := by
  have f0 : InstrSpec 0x10f0a4 [0x4C, 0x8D, 0xBC, 0x24, 0xA0, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x10f0a4) (leaR64Effect 0x10f0a4 15 (.sib 4 none 0 (.d32 0xfa0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10f0a4 15 (.sib 4 none 0 (.d32 0xfa0))).toInstrSpec (lea_r64_effect_step 0x10f0a4 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xfa0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f0ac [0xBA, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x10f0ac) (movR32Imm32Effect 0x10f0ac 5 2 0x780)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10f0ac 5 2 0x780).toInstrSpec (mov_r32_imm32_effect_step 0x10f0ac 0xba (by decide) 0x780) pre_rip
  have f2 : InstrSpec 0x10f0b1 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10f0b1) (movR64R64Effect 0x10f0b1 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f0b1 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10f0b1 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10f0b4 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10f0b4) (movR64R64Effect 0x10f0b4 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f0b4 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10f0b4 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10f0b7 [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x10f0b7 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0ba) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0ba)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10f0b7 13 0x10f0ba).toInstrSpec (call_r64_rex_effect_step 0x10f0b7 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0b1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10f0a4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f0a4 :=
  Rest.liftedBlock (rest_l10f0a4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f0a4 x hx)

theorem rest_l10f0ba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f0ba bytes_l10f0ba) (entryMap (live .l10f0ba))
      17 0x10f0ba bytes_l10f0ba b_l10f0ba := by
  have f0 : InstrSpec 0x10f0ba [0x66, 0xC7, 0x44, 0x24, 0x48, 0x00, 0x00] (StorePre 0x10f0ba 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10f0ba + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x10f0ba (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x10f0ba (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (mov_m16_imm16_effect_step 0x10f0ba (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10f0c1 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10f0c1 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10f0c1 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0c1 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f0c1 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10f0c1 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10f0ca [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10f0ca 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f0ca + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0ca (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f0ca (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10f0ca 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10f0d3 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10f0d3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10f0d3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0d3 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f0d3 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10f0d3 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10f0dc [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10f0dc 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10f0dc + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0dc (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f0dc (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10f0dc 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10f0e5 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10f0e5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10f0e5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0e5 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f0e5 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10f0e5 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10f0ee [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10f0ee 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10f0ee + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0ee (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f0ee (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10f0ee 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10f0f7 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10f0f7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10f0f7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0f7 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f0f7 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10f0f7 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10f100 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10f100 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10f100 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f100 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f100 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10f100 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10f109 [0x48, 0xC7, 0x04, 0x24, 0x01, 0x00, 0x00, 0x00] (StorePre 0x10f109 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10f109 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10f109 (.sib 4 none 0 .none) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10f109 (.sib 4 none 0 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x10f109 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10f111 [0x4C, 0x8D, 0x4C, 0x24, 0x08] (fun s => s.RIP = 0x10f111) (leaR64Effect 0x10f111 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x10f111 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10f111 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10f116 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f116) (movR32Imm32Effect 0x10f116 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10f116 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10f116 0xba (by decide) 0x1) pre_rip
  have f12 : InstrSpec 0x10f11b [0x41, 0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10f11b) (movR32Imm32Effect 0x10f11b 6 8 0x1)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x10f11b 6 8 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10f11b 0x41 0xb8 (by decide) (by decide) 0x1) pre_rip
  have f13 : InstrSpec 0x10f121 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10f121) (movR64R64Effect 0x10f121 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10f121 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10f121 0x48 0xdf (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10f124 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10f124) (movR64R64Effect 0x10f124 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10f124 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10f124 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10f127 [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x10f127) (movR64R64Effect 0x10f127 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10f127 1 15).toInstrSpec (mov_r64_r64_effect_step 0x10f127 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10f12a [0xE8, 0x51, 0xD7, 0x00, 0x00] (PushPre 0x10f12a 5) (callEffect (fun _ => 0x11c880) 0x10f12f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10f12a 0x11c880 0x10f12f).toInstrSpec (call_rel32_effect_step 0x10f12a 0xd751 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0d3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0dc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0e5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0ee) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f0f7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f100) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f109) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f111) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f116) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 65), (3, 3), (4, 4), (5, 5), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f11b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 65), (3, 3), (4, 4), (5, 5), (8, 67), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f121) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 65), (3, 3), (4, 4), (5, 5), (7, 69), (8, 67), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f124) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 65), (3, 3), (4, 4), (5, 5), (6, 71), (7, 69), (8, 67), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f127) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 73), (2, 65), (3, 3), (4, 4), (5, 5), (6, 71), (7, 69), (8, 67), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f12a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 73), (2, 65), (3, 3), (4, 75), (5, 5), (6, 71), (7, 69), (8, 67), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c880) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l10f0ba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f0ba :=
  Rest.liftedBlock (rest_l10f0ba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f0ba x hx)

theorem rest_l10f12f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10f12f bytes_l10f12f) (entryMap (live .l10f12f))
      8 0x10f12f bytes_l10f12f b_l10f12f := by
  have f0 : InstrSpec 0x10f12f [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10f12f) (movR64R64Effect 0x10f12f 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10f12f 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10f12f 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10f132 [0x48, 0x81, 0xC4, 0x20, 0x17, 0x00, 0x00] (fun s => s.RIP = 0x10f132) (addR64Imm32Effect 0x10f132 4 0x1720)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10f132 4 0x1720).toInstrSpec (add_r64_imm32_effect_step 0x10f132 0x48 0xc4 0x1720 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10f139 [0x5B] (PopPre 0x10f139) (popR64Effect 0x10f139 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10f139 1 3).toInstrSpec (pop_r64_effect_step 0x10f139 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10f13a [0x41, 0x5C] (PopPre 0x10f13a) (popR64Effect 0x10f13a 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10f13a 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10f13a 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10f13c [0x41, 0x5D] (PopPre 0x10f13c) (popR64Effect 0x10f13c 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10f13c 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10f13c 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10f13e [0x41, 0x5E] (PopPre 0x10f13e) (popR64Effect 0x10f13e 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10f13e 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10f13e 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10f140 [0x41, 0x5F] (PopPre 0x10f140) (popR64Effect 0x10f140 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10f140 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10f140 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10f142 [0xC3] (RetPre 0x10f142) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10f142).toInstrSpec (ret_effect_step 0x10f142) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f132) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f139) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f13a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f13c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f13e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f140) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f142) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l10f12f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10f12f :=
  Rest.liftedBlock (rest_l10f12f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10f12f x hx)

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

theorem_by block_l10ee80_eval :
    program.runBlock (dialect code) ⟨.l10ee80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ef08_eval :
    program.runBlock (dialect code) ⟨.l10ef08, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f091_eval :
    program.runBlock (dialect code) ⟨.l10f091, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f0a4_eval :
    program.runBlock (dialect code) ⟨.l10f0a4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f0ba_eval :
    program.runBlock (dialect code) ⟨.l10f0ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10f12f_eval :
    program.runBlock (dialect code) ⟨.l10f12f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
