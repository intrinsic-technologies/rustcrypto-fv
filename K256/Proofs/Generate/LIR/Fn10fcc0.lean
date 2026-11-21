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

theorem rest_l10fcc0_5 [Bindings] (code : CodeMap) :
    Rest (n := 243) code lifted (codeRange 0x10fcc0 bytes_l10fcc0) [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x10fe14 bytes_l10fcc0_5 b_l10fcc0_5 := by
  have f100 : InstrSpec 0x10fe14 [0x4C, 0x89, 0x77, 0x30] (StorePre 0x10fe14 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10fe14 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe14 14 (.base 7 (.d8 0x30)))
      [.gpr 14, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe14 14 (.base 7 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10fe14 0x4c (by decide) 6 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f101 : InstrSpec 0x10fe18 [0x4C, 0x89, 0x7F, 0x38] (StorePre 0x10fe18 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x10fe18 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe18 15 (.base 7 (.d8 0x38)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe18 15 (.base 7 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10fe18 0x4c (by decide) 7 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f102 : InstrSpec 0x10fe1c [0x4C, 0x89, 0x67, 0x40] (StorePre 0x10fe1c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x10fe1c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe1c 12 (.base 7 (.d8 0x40)))
      [.gpr 12, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe1c 12 (.base 7 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10fe1c 0x4c (by decide) 4 (.base 7 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f103 : InstrSpec 0x10fe20 [0x4C, 0x89, 0x6F, 0x48] (StorePre 0x10fe20 4 (fun s => AddrMode.addr (.base 7 (.d8 0x48)) s (0x10fe20 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe20 13 (.base 7 (.d8 0x48)))
      [.gpr 13, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe20 13 (.base 7 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10fe20 0x4c (by decide) 5 (.base 7 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f104 : InstrSpec 0x10fe24 [0x48, 0x89, 0x6F, 0x50] (StorePre 0x10fe24 4 (fun s => AddrMode.addr (.base 7 (.d8 0x50)) s (0x10fe24 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe24 5 (.base 7 (.d8 0x50)))
      [.gpr 5, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe24 5 (.base 7 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10fe24 0x48 (by decide) 5 (.base 7 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f105 : InstrSpec 0x10fe28 [0x48, 0x89, 0x77, 0x58] (StorePre 0x10fe28 4 (fun s => AddrMode.addr (.base 7 (.d8 0x58)) s (0x10fe28 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe28 6 (.base 7 (.d8 0x58)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe28 6 (.base 7 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10fe28 0x48 (by decide) 6 (.base 7 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f106 : InstrSpec 0x10fe2c [0x48, 0x89, 0x4F, 0x60] (StorePre 0x10fe2c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x60)) s (0x10fe2c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe2c 1 (.base 7 (.d8 0x60)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe2c 1 (.base 7 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10fe2c 0x48 (by decide) 1 (.base 7 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f107 : InstrSpec 0x10fe30 [0x48, 0x89, 0x47, 0x68] (StorePre 0x10fe30 4 (fun s => AddrMode.addr (.base 7 (.d8 0x68)) s (0x10fe30 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe30 0 (.base 7 (.d8 0x68)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe30 0 (.base 7 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x10fe30 0x48 (by decide) 0 (.base 7 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f108 : InstrSpec 0x10fe34 [0x4C, 0x89, 0x4F, 0x70] (StorePre 0x10fe34 4 (fun s => AddrMode.addr (.base 7 (.d8 0x70)) s (0x10fe34 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe34 9 (.base 7 (.d8 0x70)))
      [.gpr 9, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe34 9 (.base 7 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10fe34 0x4c (by decide) 1 (.base 7 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f109 : InstrSpec 0x10fe38 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x10fe38) (movR64R64Effect 0x10fe38 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10fe38 0 7).toInstrSpec (mov_r64_r64_effect_step 0x10fe38 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x10fe3b [0x48, 0x83, 0xC4, 0x20] (fun s => s.RIP = 0x10fe3b) (addR64Imm8Effect 0x10fe3b 4 0x20)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10fe3b 4 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10fe3b 0x48 0xc4 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x10fe3f [0x5B] (PopPre 0x10fe3f) (popR64Effect 0x10fe3f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fe3f 1 3).toInstrSpec (pop_r64_effect_step 0x10fe3f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f112 : InstrSpec 0x10fe40 [0x41, 0x5C] (PopPre 0x10fe40) (popR64Effect 0x10fe40 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fe40 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10fe40 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f113 : InstrSpec 0x10fe42 [0x41, 0x5D] (PopPre 0x10fe42) (popR64Effect 0x10fe42 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fe42 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10fe42 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f114 : InstrSpec 0x10fe44 [0x41, 0x5E] (PopPre 0x10fe44) (popR64Effect 0x10fe44 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fe44 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10fe44 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f115 : InstrSpec 0x10fe46 [0x41, 0x5F] (PopPre 0x10fe46) (popR64Effect 0x10fe46 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fe46 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10fe46 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f116 : InstrSpec 0x10fe48 [0x5D] (PopPre 0x10fe48) (popR64Effect 0x10fe48 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fe48 1 5).toInstrSpec (pop_r64_effect_step 0x10fe48 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f117 : InstrSpec 0x10fe49 [0xC3] (RetPre 0x10fe49) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10fe49).toInstrSpec (ret_effect_step 0x10fe49) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 243) (RestInside.exec (n := 243) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe18) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 244) (RestInside.exec (n := 244) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe1c) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 245) (RestInside.exec (n := 245) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe20) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 246) (RestInside.exec (n := 246) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe24) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 247) (RestInside.exec (n := 247) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe28) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 248) (RestInside.exec (n := 248) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe2c) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 249) (RestInside.exec (n := 249) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe30) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 250) (RestInside.exec (n := 250) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe34) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 251) (RestInside.exec (n := 251) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe38) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f109 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe3b) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f110 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 137), (4, 254), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe3f) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f111 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 257) f111 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 258) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 256), (4, 257), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe40) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f112 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 260) f112 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 261) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 256), (4, 260), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 259), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe42) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f113 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 263) f113 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 264) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 256), (4, 263), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 259), (13, 262), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe44) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f114 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 266) f114 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 267) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 256), (4, 266), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 259), (13, 262), (14, 265), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe46) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f115 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 269) f115 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 270) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 256), (4, 269), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 259), (13, 262), (14, 265), (15, 268), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe48) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f116 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 272) f116 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 273) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 256), (4, 272), (5, 271), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 259), (13, 262), (14, 265), (15, 268), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe49) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f117 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 275) f117 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 276) (ρ' := [(0, 252), (1, 207), (2, 238), (3, 256), (4, 275), (5, 271), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 259), (13, 262), (14, 265), (15, 268), (22, 22), (39, 39), (50, 50), (51, 51)]) f117 (by decide) rfl rfl rfl (by decide)

theorem rest_l10fcc0_4 [Bindings] (code : CodeMap) :
    Rest (n := 209) code lifted (codeRange 0x10fcc0 bytes_l10fcc0) [(0, 199), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]
      38 0x10fdc8 bytes_l10fcc0_4 b_l10fcc0_4 := by
  have f80 : InstrSpec 0x10fdc8 [0x4D, 0x8B, 0x50, 0x68] (LoadPre 0x10fdc8 (fun s => AddrMode.addr (.base 8 (.d8 0x68)) s (0x10fdc8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdc8 10 (.base 8 (.d8 0x68)))
      [.gpr 8] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10fdc8 10 (.base 8 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10fdc8 0x4d (by decide) 2 (.base 8 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f81 : InstrSpec 0x10fdcc [0x49, 0x8B, 0x41, 0x68] (LoadPre 0x10fdcc (fun s => AddrMode.addr (.base 9 (.d8 0x68)) s (0x10fdcc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdcc 0 (.base 9 (.d8 0x68)))
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fdcc 0 (.base 9 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10fdcc 0x49 (by decide) 0 (.base 9 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f82 : InstrSpec 0x10fdd0 [0x4C, 0x31, 0xD0] (fun s => s.RIP = 0x10fdd0) (xorR64R64Effect 0x10fdd0 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fdd0 0 10).toInstrSpec (xor_r64_r64_effect_step 0x10fdd0 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x10fdd3 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x10fdd3) (andR64R64Effect 0x10fdd3 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fdd3 0 2).toInstrSpec (and_r64_r64_effect_step 0x10fdd3 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x10fdd6 [0x4C, 0x31, 0xD0] (fun s => s.RIP = 0x10fdd6) (xorR64R64Effect 0x10fdd6 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fdd6 0 10).toInstrSpec (xor_r64_r64_effect_step 0x10fdd6 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x10fdd9 [0x4D, 0x8B, 0x40, 0x70] (LoadPre 0x10fdd9 (fun s => AddrMode.addr (.base 8 (.d8 0x70)) s (0x10fdd9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdd9 8 (.base 8 (.d8 0x70)))
      [.gpr 8] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10fdd9 8 (.base 8 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10fdd9 0x4d (by decide) 0 (.base 8 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f86 : InstrSpec 0x10fddd [0x4D, 0x8B, 0x49, 0x70] (LoadPre 0x10fddd (fun s => AddrMode.addr (.base 9 (.d8 0x70)) s (0x10fddd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fddd 9 (.base 9 (.d8 0x70)))
      [.gpr 9] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10fddd 9 (.base 9 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10fddd 0x4d (by decide) 1 (.base 9 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f87 : InstrSpec 0x10fde1 [0x4D, 0x31, 0xC1] (fun s => s.RIP = 0x10fde1) (xorR64R64Effect 0x10fde1 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fde1 9 8).toInstrSpec (xor_r64_r64_effect_step 0x10fde1 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x10fde4 [0x49, 0x21, 0xD1] (fun s => s.RIP = 0x10fde4) (andR64R64Effect 0x10fde4 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fde4 9 2).toInstrSpec (and_r64_r64_effect_step 0x10fde4 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x10fde7 [0x4D, 0x31, 0xC1] (fun s => s.RIP = 0x10fde7) (xorR64R64Effect 0x10fde7 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fde7 9 8).toInstrSpec (xor_r64_r64_effect_step 0x10fde7 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x10fdea [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x10fdea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10fdea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fdea 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10fdea 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10fdea 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f91 : InstrSpec 0x10fdef [0x48, 0x89, 0x17] (StorePre 0x10fdef 3 (fun s => AddrMode.addr (.base 7 .none) s (0x10fdef + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10fdef 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fdef 2 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10fdef 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f92 : InstrSpec 0x10fdf2 [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x10fdf2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fdf2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fdf2 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10fdf2 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10fdf2 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f93 : InstrSpec 0x10fdf7 [0x48, 0x89, 0x57, 0x08] (StorePre 0x10fdf7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10fdf7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fdf7 2 (.base 7 (.d8 0x8)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fdf7 2 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10fdf7 0x48 (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f94 : InstrSpec 0x10fdfb [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x10fdfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fdfb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fdfb 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10fdfb 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10fdfb 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f95 : InstrSpec 0x10fe00 [0x48, 0x89, 0x57, 0x10] (StorePre 0x10fe00 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10fe00 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe00 2 (.base 7 (.d8 0x10)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe00 2 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10fe00 0x48 (by decide) 2 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x10fe04 [0x48, 0x8B, 0x14, 0x24] (LoadPre 0x10fe04 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fe04 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fe04 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10fe04 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10fe04 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x10fe08 [0x48, 0x89, 0x57, 0x18] (StorePre 0x10fe08 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10fe08 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe08 2 (.base 7 (.d8 0x18)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe08 2 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10fe08 0x48 (by decide) 2 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f98 : InstrSpec 0x10fe0c [0x4C, 0x89, 0x5F, 0x20] (StorePre 0x10fe0c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10fe0c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe0c 11 (.base 7 (.d8 0x20)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe0c 11 (.base 7 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10fe0c 0x4c (by decide) 3 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f99 : InstrSpec 0x10fe10 [0x48, 0x89, 0x5F, 0x28] (StorePre 0x10fe10 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x10fe10 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe10 3 (.base 7 (.d8 0x28)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fe10 3 (.base 7 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10fe10 0x48 (by decide) 3 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f80 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 199), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdcc) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f81 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 211), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdd0) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f82 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 213), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdd3) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f83 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 215), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdd6) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f84 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 217), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdd9) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f85 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 217), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 67), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fddd) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f86 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 217), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 221), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fde1) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f87 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 217), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 223), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fde4) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f88 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 217), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 225), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fde7) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f89 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 217), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdea) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f90 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 217), (1, 207), (2, 229), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdef) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.exec (n := 231) (ρ' := [(0, 217), (1, 207), (2, 229), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdf2) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f92 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 217), (1, 207), (2, 232), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdf7) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.exec (n := 234) (ρ' := [(0, 217), (1, 207), (2, 232), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdfb) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f94 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 217), (1, 207), (2, 235), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe00) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.exec (n := 237) (ρ' := [(0, 217), (1, 207), (2, 235), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe04) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f96 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe08) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.exec (n := 240) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe0c) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 241) (RestInside.exec (n := 241) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe10) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 242) (RestInside.exec (n := 242) (ρ' := [(0, 217), (1, 207), (2, 238), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe14) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10fcc0_5 code

theorem rest_l10fcc0_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x10fcc0 bytes_l10fcc0) [(0, 159), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 13), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]
      58 0x10fd84 bytes_l10fcc0_3 b_l10fcc0_3 := by
  have f60 : InstrSpec 0x10fd84 [0x49, 0x8B, 0x40, 0x48] (LoadPre 0x10fd84 (fun s => AddrMode.addr (.base 8 (.d8 0x48)) s (0x10fd84 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd84 0 (.base 8 (.d8 0x48)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd84 0 (.base 8 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10fd84 0x49 (by decide) 0 (.base 8 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x10fd88 [0x4D, 0x8B, 0x69, 0x48] (LoadPre 0x10fd88 (fun s => AddrMode.addr (.base 9 (.d8 0x48)) s (0x10fd88 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd88 13 (.base 9 (.d8 0x48)))
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10fd88 13 (.base 9 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10fd88 0x4d (by decide) 5 (.base 9 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x10fd8c [0x49, 0x31, 0xC5] (fun s => s.RIP = 0x10fd8c) (xorR64R64Effect 0x10fd8c 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd8c 13 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd8c 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x10fd8f [0x49, 0x21, 0xD5] (fun s => s.RIP = 0x10fd8f) (andR64R64Effect 0x10fd8f 13 2)
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fd8f 13 2).toInstrSpec (and_r64_r64_effect_step 0x10fd8f 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x10fd92 [0x49, 0x31, 0xC5] (fun s => s.RIP = 0x10fd92) (xorR64R64Effect 0x10fd92 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd92 13 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd92 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x10fd95 [0x49, 0x8B, 0x40, 0x50] (LoadPre 0x10fd95 (fun s => AddrMode.addr (.base 8 (.d8 0x50)) s (0x10fd95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd95 0 (.base 8 (.d8 0x50)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd95 0 (.base 8 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10fd95 0x49 (by decide) 0 (.base 8 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x10fd99 [0x49, 0x8B, 0x69, 0x50] (LoadPre 0x10fd99 (fun s => AddrMode.addr (.base 9 (.d8 0x50)) s (0x10fd99 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd99 5 (.base 9 (.d8 0x50)))
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10fd99 5 (.base 9 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10fd99 0x49 (by decide) 5 (.base 9 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f67 : InstrSpec 0x10fd9d [0x48, 0x31, 0xC5] (fun s => s.RIP = 0x10fd9d) (xorR64R64Effect 0x10fd9d 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd9d 5 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd9d 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x10fda0 [0x48, 0x21, 0xD5] (fun s => s.RIP = 0x10fda0) (andR64R64Effect 0x10fda0 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fda0 5 2).toInstrSpec (and_r64_r64_effect_step 0x10fda0 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x10fda3 [0x48, 0x31, 0xC5] (fun s => s.RIP = 0x10fda3) (xorR64R64Effect 0x10fda3 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fda3 5 0).toInstrSpec (xor_r64_r64_effect_step 0x10fda3 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10fda6 [0x49, 0x8B, 0x40, 0x58] (LoadPre 0x10fda6 (fun s => AddrMode.addr (.base 8 (.d8 0x58)) s (0x10fda6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fda6 0 (.base 8 (.d8 0x58)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fda6 0 (.base 8 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10fda6 0x49 (by decide) 0 (.base 8 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x10fdaa [0x49, 0x8B, 0x71, 0x58] (LoadPre 0x10fdaa (fun s => AddrMode.addr (.base 9 (.d8 0x58)) s (0x10fdaa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdaa 6 (.base 9 (.d8 0x58)))
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10fdaa 6 (.base 9 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10fdaa 0x49 (by decide) 6 (.base 9 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x10fdae [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x10fdae) (xorR64R64Effect 0x10fdae 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fdae 6 0).toInstrSpec (xor_r64_r64_effect_step 0x10fdae 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10fdb1 [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x10fdb1) (andR64R64Effect 0x10fdb1 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fdb1 6 2).toInstrSpec (and_r64_r64_effect_step 0x10fdb1 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10fdb4 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x10fdb4) (xorR64R64Effect 0x10fdb4 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fdb4 6 0).toInstrSpec (xor_r64_r64_effect_step 0x10fdb4 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x10fdb7 [0x49, 0x8B, 0x40, 0x60] (LoadPre 0x10fdb7 (fun s => AddrMode.addr (.base 8 (.d8 0x60)) s (0x10fdb7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdb7 0 (.base 8 (.d8 0x60)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fdb7 0 (.base 8 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10fdb7 0x49 (by decide) 0 (.base 8 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x10fdbb [0x49, 0x8B, 0x49, 0x60] (LoadPre 0x10fdbb (fun s => AddrMode.addr (.base 9 (.d8 0x60)) s (0x10fdbb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdbb 1 (.base 9 (.d8 0x60)))
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10fdbb 1 (.base 9 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10fdbb 0x49 (by decide) 1 (.base 9 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f77 : InstrSpec 0x10fdbf [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10fdbf) (xorR64R64Effect 0x10fdbf 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fdbf 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10fdbf 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x10fdc2 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x10fdc2) (andR64R64Effect 0x10fdc2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fdc2 1 2).toInstrSpec (and_r64_r64_effect_step 0x10fdc2 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x10fdc5 [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10fdc5) (xorR64R64Effect 0x10fdc5 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fdc5 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10fdc5 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 169), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 13), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd88) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 169), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 171), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd8c) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 169), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 173), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd8f) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 169), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 175), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd92) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 169), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd95) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f65 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 179), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd99) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 179), (1, 116), (2, 73), (3, 137), (4, 65), (5, 181), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd9d) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 179), (1, 116), (2, 73), (3, 137), (4, 65), (5, 183), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fda0) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 179), (1, 116), (2, 73), (3, 137), (4, 65), (5, 185), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fda3) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 179), (1, 116), (2, 73), (3, 137), (4, 65), (5, 187), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fda6) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 189), (1, 116), (2, 73), (3, 137), (4, 65), (5, 187), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdaa) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 189), (1, 116), (2, 73), (3, 137), (4, 65), (5, 187), (6, 191), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdae) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 189), (1, 116), (2, 73), (3, 137), (4, 65), (5, 187), (6, 193), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdb1) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 189), (1, 116), (2, 73), (3, 137), (4, 65), (5, 187), (6, 195), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdb4) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 189), (1, 116), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdb7) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f75 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 199), (1, 116), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdbb) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 199), (1, 201), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdbf) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f77 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 199), (1, 203), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdc2) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f78 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 199), (1, 205), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdc5) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 199), (1, 207), (2, 73), (3, 137), (4, 65), (5, 187), (6, 197), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 177), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fdc8) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fcc0_4 code

theorem rest_l10fcc0_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x10fcc0 bytes_l10fcc0) [(0, 119), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      78 0x10fd40 bytes_l10fcc0_2 b_l10fcc0_2 := by
  have f40 : InstrSpec 0x10fd40 [0x49, 0x8B, 0x40, 0x28] (LoadPre 0x10fd40 (fun s => AddrMode.addr (.base 8 (.d8 0x28)) s (0x10fd40 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd40 0 (.base 8 (.d8 0x28)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd40 0 (.base 8 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10fd40 0x49 (by decide) 0 (.base 8 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10fd44 [0x49, 0x8B, 0x59, 0x28] (LoadPre 0x10fd44 (fun s => AddrMode.addr (.base 9 (.d8 0x28)) s (0x10fd44 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd44 3 (.base 9 (.d8 0x28)))
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10fd44 3 (.base 9 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10fd44 0x49 (by decide) 3 (.base 9 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x10fd48 [0x48, 0x31, 0xC3] (fun s => s.RIP = 0x10fd48) (xorR64R64Effect 0x10fd48 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd48 3 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd48 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x10fd4b [0x48, 0x21, 0xD3] (fun s => s.RIP = 0x10fd4b) (andR64R64Effect 0x10fd4b 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fd4b 3 2).toInstrSpec (and_r64_r64_effect_step 0x10fd4b 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x10fd4e [0x48, 0x31, 0xC3] (fun s => s.RIP = 0x10fd4e) (xorR64R64Effect 0x10fd4e 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd4e 3 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd4e 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10fd51 [0x49, 0x8B, 0x40, 0x30] (LoadPre 0x10fd51 (fun s => AddrMode.addr (.base 8 (.d8 0x30)) s (0x10fd51 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd51 0 (.base 8 (.d8 0x30)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd51 0 (.base 8 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10fd51 0x49 (by decide) 0 (.base 8 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x10fd55 [0x4D, 0x8B, 0x71, 0x30] (LoadPre 0x10fd55 (fun s => AddrMode.addr (.base 9 (.d8 0x30)) s (0x10fd55 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd55 14 (.base 9 (.d8 0x30)))
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10fd55 14 (.base 9 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10fd55 0x4d (by decide) 6 (.base 9 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x10fd59 [0x49, 0x31, 0xC6] (fun s => s.RIP = 0x10fd59) (xorR64R64Effect 0x10fd59 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd59 14 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd59 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10fd5c [0x49, 0x21, 0xD6] (fun s => s.RIP = 0x10fd5c) (andR64R64Effect 0x10fd5c 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fd5c 14 2).toInstrSpec (and_r64_r64_effect_step 0x10fd5c 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10fd5f [0x49, 0x31, 0xC6] (fun s => s.RIP = 0x10fd5f) (xorR64R64Effect 0x10fd5f 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd5f 14 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd5f 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10fd62 [0x49, 0x8B, 0x40, 0x38] (LoadPre 0x10fd62 (fun s => AddrMode.addr (.base 8 (.d8 0x38)) s (0x10fd62 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd62 0 (.base 8 (.d8 0x38)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd62 0 (.base 8 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10fd62 0x49 (by decide) 0 (.base 8 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x10fd66 [0x4D, 0x8B, 0x79, 0x38] (LoadPre 0x10fd66 (fun s => AddrMode.addr (.base 9 (.d8 0x38)) s (0x10fd66 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd66 15 (.base 9 (.d8 0x38)))
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10fd66 15 (.base 9 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10fd66 0x4d (by decide) 7 (.base 9 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x10fd6a [0x49, 0x31, 0xC7] (fun s => s.RIP = 0x10fd6a) (xorR64R64Effect 0x10fd6a 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd6a 15 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd6a 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10fd6d [0x49, 0x21, 0xD7] (fun s => s.RIP = 0x10fd6d) (andR64R64Effect 0x10fd6d 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fd6d 15 2).toInstrSpec (and_r64_r64_effect_step 0x10fd6d 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x10fd70 [0x49, 0x31, 0xC7] (fun s => s.RIP = 0x10fd70) (xorR64R64Effect 0x10fd70 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd70 15 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd70 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10fd73 [0x49, 0x8B, 0x40, 0x40] (LoadPre 0x10fd73 (fun s => AddrMode.addr (.base 8 (.d8 0x40)) s (0x10fd73 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd73 0 (.base 8 (.d8 0x40)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd73 0 (.base 8 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10fd73 0x49 (by decide) 0 (.base 8 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f56 : InstrSpec 0x10fd77 [0x4D, 0x8B, 0x61, 0x40] (LoadPre 0x10fd77 (fun s => AddrMode.addr (.base 9 (.d8 0x40)) s (0x10fd77 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd77 12 (.base 9 (.d8 0x40)))
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10fd77 12 (.base 9 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10fd77 0x4d (by decide) 4 (.base 9 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f57 : InstrSpec 0x10fd7b [0x49, 0x31, 0xC4] (fun s => s.RIP = 0x10fd7b) (xorR64R64Effect 0x10fd7b 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd7b 12 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd7b 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10fd7e [0x49, 0x21, 0xD4] (fun s => s.RIP = 0x10fd7e) (andR64R64Effect 0x10fd7e 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fd7e 12 2).toInstrSpec (and_r64_r64_effect_step 0x10fd7e 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10fd81 [0x49, 0x31, 0xC4] (fun s => s.RIP = 0x10fd81) (xorR64R64Effect 0x10fd81 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd81 12 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd81 0x49 0xc4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 129), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd44) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f41 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 129), (1, 116), (2, 73), (3, 131), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd48) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f42 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 129), (1, 116), (2, 73), (3, 133), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd4b) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f43 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 129), (1, 116), (2, 73), (3, 135), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd4e) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f44 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 129), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd51) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 139), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd55) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f46 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 139), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 141), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd59) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f47 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 139), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 143), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd5c) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f48 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 139), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 145), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd5f) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 139), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 147), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd62) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 149), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 147), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd66) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f51 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 149), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 147), (15, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd6a) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 149), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 147), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd6d) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 149), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 147), (15, 155), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd70) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 149), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd73) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 159), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd77) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 159), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 161), (13, 13), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd7b) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 159), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 163), (13, 13), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd7e) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 159), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 165), (13, 13), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd81) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 159), (1, 116), (2, 73), (3, 137), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 167), (13, 13), (14, 147), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd84) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fcc0_3 code

theorem rest_l10fcc0_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x10fcc0 bytes_l10fcc0) [(0, 90), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      98 0x10fcf9 bytes_l10fcc0_1 b_l10fcc0_1 := by
  have f20 : InstrSpec 0x10fcf9 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x10fcf9) (andR64R64Effect 0x10fcf9 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fcf9 0 2).toInstrSpec (and_r64_r64_effect_step 0x10fcf9 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10fcfc [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x10fcfc) (xorR64R64Effect 0x10fcfc 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fcfc 0 1).toInstrSpec (xor_r64_r64_effect_step 0x10fcfc 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10fcff [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10fcff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fcff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fcff 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fcff 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10fcff 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x10fd04 [0x49, 0x8B, 0x40, 0x10] (LoadPre 0x10fd04 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x10fd04 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd04 0 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd04 0 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10fd04 0x49 (by decide) 0 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10fd08 [0x49, 0x8B, 0x49, 0x10] (LoadPre 0x10fd08 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x10fd08 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd08 1 (.base 9 (.d8 0x10)))
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10fd08 1 (.base 9 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10fd08 0x49 (by decide) 1 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x10fd0c [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10fd0c) (xorR64R64Effect 0x10fd0c 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd0c 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd0c 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10fd0f [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x10fd0f) (andR64R64Effect 0x10fd0f 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fd0f 1 2).toInstrSpec (and_r64_r64_effect_step 0x10fd0f 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10fd12 [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10fd12) (xorR64R64Effect 0x10fd12 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd12 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd12 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10fd15 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x10fd15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fd15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fd15 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fd15 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10fd15 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x10fd1a [0x49, 0x8B, 0x40, 0x18] (LoadPre 0x10fd1a (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x10fd1a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd1a 0 (.base 8 (.d8 0x18)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd1a 0 (.base 8 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10fd1a 0x49 (by decide) 0 (.base 8 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x10fd1e [0x49, 0x8B, 0x49, 0x18] (LoadPre 0x10fd1e (fun s => AddrMode.addr (.base 9 (.d8 0x18)) s (0x10fd1e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd1e 1 (.base 9 (.d8 0x18)))
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10fd1e 1 (.base 9 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10fd1e 0x49 (by decide) 1 (.base 9 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x10fd22 [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10fd22) (xorR64R64Effect 0x10fd22 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd22 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd22 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10fd25 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x10fd25) (andR64R64Effect 0x10fd25 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fd25 1 2).toInstrSpec (and_r64_r64_effect_step 0x10fd25 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10fd28 [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10fd28) (xorR64R64Effect 0x10fd28 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd28 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd28 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10fd2b [0x48, 0x89, 0x0C, 0x24] (StorePre 0x10fd2b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fd2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fd2b 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fd2b 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10fd2b 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x10fd2f [0x49, 0x8B, 0x40, 0x20] (LoadPre 0x10fd2f (fun s => AddrMode.addr (.base 8 (.d8 0x20)) s (0x10fd2f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd2f 0 (.base 8 (.d8 0x20)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fd2f 0 (.base 8 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10fd2f 0x49 (by decide) 0 (.base 8 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x10fd33 [0x4D, 0x8B, 0x59, 0x20] (LoadPre 0x10fd33 (fun s => AddrMode.addr (.base 9 (.d8 0x20)) s (0x10fd33 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd33 11 (.base 9 (.d8 0x20)))
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x10fd33 11 (.base 9 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10fd33 0x4d (by decide) 3 (.base 9 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x10fd37 [0x49, 0x31, 0xC3] (fun s => s.RIP = 0x10fd37) (xorR64R64Effect 0x10fd37 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd37 11 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd37 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x10fd3a [0x49, 0x21, 0xD3] (fun s => s.RIP = 0x10fd3a) (andR64R64Effect 0x10fd3a 11 2)
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fd3a 11 2).toInstrSpec (and_r64_r64_effect_step 0x10fd3a 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10fd3d [0x49, 0x31, 0xC3] (fun s => s.RIP = 0x10fd3d) (xorR64R64Effect 0x10fd3d 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fd3d 11 0).toInstrSpec (xor_r64_r64_effect_step 0x10fd3d 0x49 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcfc) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 94), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcff) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 94), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd04) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 97), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd08) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 97), (1, 99), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd0c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 97), (1, 101), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd0f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 97), (1, 103), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd12) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 97), (1, 105), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd15) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 97), (1, 105), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd1a) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 108), (1, 105), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd1e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 108), (1, 110), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd22) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 108), (1, 112), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd25) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 108), (1, 114), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd28) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 108), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd2b) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.exec (n := 118) (ρ' := [(0, 108), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd2f) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd33) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 119), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 121), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd37) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 119), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 123), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd3a) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 119), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 125), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd3d) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 119), (1, 116), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (11, 127), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fd40) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fcc0_2 code

theorem rest_l10fcc0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fcc0 bytes_l10fcc0) (entryMap (live .l10fcc0))
      118 0x10fcc0 bytes_l10fcc0 b_l10fcc0 := by
  have f0 : InstrSpec 0x10fcc0 [0x55] (PushPre 0x10fcc0 1) (pushR64Effect 0x10fcc0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fcc0 1 5).toInstrSpec (push_r64_effect_step 0x10fcc0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10fcc1 [0x41, 0x57] (PushPre 0x10fcc1 2) (pushR64Effect 0x10fcc1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fcc1 2 15).toInstrSpec (push_r64_rex_effect_step 0x10fcc1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10fcc3 [0x41, 0x56] (PushPre 0x10fcc3 2) (pushR64Effect 0x10fcc3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fcc3 2 14).toInstrSpec (push_r64_rex_effect_step 0x10fcc3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10fcc5 [0x41, 0x55] (PushPre 0x10fcc5 2) (pushR64Effect 0x10fcc5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fcc5 2 13).toInstrSpec (push_r64_rex_effect_step 0x10fcc5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10fcc7 [0x41, 0x54] (PushPre 0x10fcc7 2) (pushR64Effect 0x10fcc7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fcc7 2 12).toInstrSpec (push_r64_rex_effect_step 0x10fcc7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10fcc9 [0x53] (PushPre 0x10fcc9 1) (pushR64Effect 0x10fcc9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fcc9 1 3).toInstrSpec (push_r64_effect_step 0x10fcc9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10fcca [0x48, 0x83, 0xEC, 0x20] (fun s => s.RIP = 0x10fcca) (subR64Imm8Effect 0x10fcca 4 0x20)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10fcca 4 0x20).toInstrSpec (sub_r64_imm8_effect_step 0x10fcca 0x48 0xec 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10fcce [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10fcce) (movR64R64Effect 0x10fcce 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10fcce 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10fcce 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10fcd1 [0x49, 0x89, 0xF0] (fun s => s.RIP = 0x10fcd1) (movR64R64Effect 0x10fcd1 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10fcd1 8 6).toInstrSpec (mov_r64_r64_effect_step 0x10fcd1 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10fcd4 [0x0F, 0xB6, 0xD1] (fun s => s.RIP = 0x10fcd4) (movzxR32R8Effect 0x10fcd4 3 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x10fcd4 3 2 1).toInstrSpec (movzx_r32_r8_effect_step 0x10fcd4 0xd1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10fcd7 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x10fcd7) (negR64Effect 0x10fcd7 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x10fcd7 2).toInstrSpec (neg_r64_effect_step 0x10fcd7 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10fcda [0x48, 0x8B, 0x06] (LoadPre 0x10fcda (fun s => AddrMode.addr (.base 6 .none) s (0x10fcda + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10fcda 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fcda 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10fcda 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10fcdd [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x10fcdd (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10fcdd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fcdd 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10fcdd 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10fcdd 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10fce1 [0x49, 0x8B, 0x31] (LoadPre 0x10fce1 (fun s => AddrMode.addr (.base 9 .none) s (0x10fce1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10fce1 6 (.base 9 .none))
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10fce1 6 (.base 9 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10fce1 0x49 (by decide) 6 (.base 9 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10fce4 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x10fce4) (xorR64R64Effect 0x10fce4 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fce4 6 0).toInstrSpec (xor_r64_r64_effect_step 0x10fce4 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10fce7 [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x10fce7) (andR64R64Effect 0x10fce7 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fce7 6 2).toInstrSpec (and_r64_r64_effect_step 0x10fce7 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10fcea [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x10fcea) (xorR64R64Effect 0x10fcea 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fcea 6 0).toInstrSpec (xor_r64_r64_effect_step 0x10fcea 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10fced [0x48, 0x89, 0x74, 0x24, 0x18] (StorePre 0x10fced 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10fced + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fced 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fced 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10fced 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10fcf2 [0x49, 0x8B, 0x41, 0x08] (LoadPre 0x10fcf2 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x10fcf2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fcf2 0 (.base 9 (.d8 0x8)))
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fcf2 0 (.base 9 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10fcf2 0x49 (by decide) 0 (.base 9 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10fcf6 [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x10fcf6) (xorR64R64Effect 0x10fcf6 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fcf6 0 1).toInstrSpec (xor_r64_r64_effect_step 0x10fcf6 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcce) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcd1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcd4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcd7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcda) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcdd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fce1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 75), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 79), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fce4) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 75), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 81), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fce7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 75), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcea) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 75), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fced) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 75), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcf2) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcf6) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 85), (7, 7), (8, 69), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcf9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fcc0_1 code

theorem block_l10fcc0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fcc0 :=
  Rest.liftedBlock (rest_l10fcc0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fcc0 x hx)

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

theorem_by block_l10fcc0_eval :
    program.runBlock (dialect code) ⟨.l10fcc0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
