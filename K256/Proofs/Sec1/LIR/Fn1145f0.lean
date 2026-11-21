import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Sec1.LIR.Generated.Values

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

theorem rest_l1145f0_9 [Bindings] (code : CodeMap) :
    Rest (n := 446) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 437), (1, 439), (2, 442), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x114888 bytes_l1145f0_9 b_l1145f0_9 := by
  have f180 : InstrSpec 0x114888 [0x48, 0x0F, 0xA4, 0xCA, 0x0C] (fun s => s.RIP = 0x114888) (shldR64R64Effect 0x114888 5 2 1 12)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x114888 5 2 1 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x114888 0x48 (by decide) 0xca (by decide) 0xc) pre_rip
  have f181 : InstrSpec 0x11488d [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x11488d) (movR64Imm64Effect 0x11488d 1 0xffffffffffff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x11488d 1 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x11488d 0x48 0xb9 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f182 : InstrSpec 0x114897 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x114897) (andR64R64Effect 0x114897 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114897 1 9).toInstrSpec (and_r64_r64_effect_step 0x114897 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x11489a [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x11489a) (addR64R64Effect 0x11489a 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11489a 1 2).toInstrSpec (add_r64_r64_effect_step 0x11489a 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f184 : InstrSpec 0x11489d [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x11489d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11489d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11489d 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11489d 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x11489d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f185 : InstrSpec 0x1148a2 [0x48, 0x89, 0x17] (StorePre 0x1148a2 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1148a2 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1148a2 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1148a2 2 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1148a2 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f186 : InstrSpec 0x1148a5 [0x4C, 0x89, 0x7F, 0x08] (StorePre 0x1148a5 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1148a5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1148a5 15 (.base 7 (.d8 0x8)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1148a5 15 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1148a5 0x4c (by decide) 7 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f187 : InstrSpec 0x1148a9 [0x48, 0x89, 0x77, 0x10] (StorePre 0x1148a9 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1148a9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1148a9 6 (.base 7 (.d8 0x10)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1148a9 6 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1148a9 0x48 (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f188 : InstrSpec 0x1148ad [0x4C, 0x89, 0x77, 0x18] (StorePre 0x1148ad 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1148ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1148ad 14 (.base 7 (.d8 0x18)))
      [.gpr 14, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1148ad 14 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1148ad 0x4c (by decide) 6 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f189 : InstrSpec 0x1148b1 [0x48, 0x89, 0x4F, 0x20] (StorePre 0x1148b1 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x1148b1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1148b1 1 (.base 7 (.d8 0x20)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1148b1 1 (.base 7 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1148b1 0x48 (by decide) 1 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f190 : InstrSpec 0x1148b5 [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x1148b5) (addR64Imm8Effect 0x1148b5 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1148b5 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x1148b5 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x1148b9 [0x5B] (PopPre 0x1148b9) (popR64Effect 0x1148b9 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1148b9 1 3).toInstrSpec (pop_r64_effect_step 0x1148b9 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f192 : InstrSpec 0x1148ba [0x41, 0x5C] (PopPre 0x1148ba) (popR64Effect 0x1148ba 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1148ba 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1148ba 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f193 : InstrSpec 0x1148bc [0x41, 0x5D] (PopPre 0x1148bc) (popR64Effect 0x1148bc 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1148bc 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1148bc 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f194 : InstrSpec 0x1148be [0x41, 0x5E] (PopPre 0x1148be) (popR64Effect 0x1148be 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1148be 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1148be 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f195 : InstrSpec 0x1148c0 [0x41, 0x5F] (PopPre 0x1148c0) (popR64Effect 0x1148c0 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1148c0 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1148c0 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f196 : InstrSpec 0x1148c2 [0x5D] (PopPre 0x1148c2) (popR64Effect 0x1148c2 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1148c2 1 5).toInstrSpec (pop_r64_effect_step 0x1148c2 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f197 : InstrSpec 0x1148c3 [0xC3] (RetPre 0x1148c3) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1148c3).toInstrSpec (ret_effect_step 0x1148c3) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 446) (RestInside.out (n := 446) f180 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 447) (ρ' := [(0, 437), (1, 439), (2, 446), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11488d) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.out (n := 448) f181 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 449) (ρ' := [(0, 437), (1, 448), (2, 446), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114897) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 450) (RestInside.out (n := 450) f182 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 451) (ρ' := [(0, 437), (1, 450), (2, 446), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11489a) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 452) (RestInside.out (n := 452) f183 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 453) (ρ' := [(0, 437), (1, 452), (2, 446), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11489d) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.out (n := 454) f184 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 455) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148a2) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 456) (RestInside.exec (n := 456) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148a5) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 457) (RestInside.exec (n := 457) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148a9) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 458) (RestInside.exec (n := 458) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ad) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 459) (RestInside.exec (n := 459) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148b1) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 460) (RestInside.exec (n := 460) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148b5) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 461) (RestInside.out (n := 461) f190 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 462) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 381), (4, 461), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148b9) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 463) (RestInside.out (n := 463) f191 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 464) f191 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 465) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 463), (4, 464), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ba) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.out (n := 466) f192 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 467) f192 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 468) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 463), (4, 467), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 466), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148bc) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 469) (RestInside.out (n := 469) f193 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 470) f193 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 471) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 463), (4, 470), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 466), (13, 469), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148be) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 472) (RestInside.out (n := 472) f194 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 473) f194 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 474) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 463), (4, 473), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 466), (13, 469), (14, 472), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148c0) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 475) (RestInside.out (n := 475) f195 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 476) f195 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 477) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 463), (4, 476), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 466), (13, 469), (14, 472), (15, 475), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148c2) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 478) (RestInside.out (n := 478) f196 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 479) f196 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 480) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 463), (4, 479), (5, 478), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 466), (13, 469), (14, 472), (15, 475), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148c3) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 481) (RestInside.out (n := 481) f197 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 482) f197 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 483) (ρ' := [(0, 437), (1, 452), (2, 454), (3, 463), (4, 482), (5, 478), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 466), (13, 469), (14, 472), (15, 475), (22, 22), (39, 39), (50, 50), (51, 51)]) f197 (by decide) rfl rfl rfl (by decide)

theorem rest_l1145f0_8 [Bindings] (code : CodeMap) :
    Rest (n := 400) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 394), (7, 7), (8, 398), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]
      38 0x114833 bytes_l1145f0_8 b_l1145f0_8 := by
  have f160 : InstrSpec 0x114833 [0x4C, 0x01, 0xEE] (fun s => s.RIP = 0x114833) (addR64R64Effect 0x114833 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114833 6 13).toInstrSpec (add_r64_r64_effect_step 0x114833 0x4c 0xee (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x114836 [0x4C, 0x13, 0x44, 0x24, 0x10] (LoadPre 0x114836 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x114836 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x114836 8 (.sib 4 none 0 (.d8 0x10))))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x114836 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x114836 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f162 : InstrSpec 0x11483b [0x48, 0x01, 0xDE] (fun s => s.RIP = 0x11483b) (addR64R64Effect 0x11483b 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11483b 6 3).toInstrSpec (add_r64_r64_effect_step 0x11483b 0x48 0xde (by decide) (by decide)) pre_rip
  have f163 : InstrSpec 0x11483e [0x4D, 0x11, 0xE0] (fun s => s.RIP = 0x11483e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11483e 8 12))
      [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11483e 8 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11483e 0x4d 0xe0 c (by decide) (by decide))) pre_rip
  have f164 : InstrSpec 0x114841 [0x48, 0x01, 0xEE] (fun s => s.RIP = 0x114841) (addR64R64Effect 0x114841 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114841 6 5).toInstrSpec (add_r64_r64_effect_step 0x114841 0x48 0xee (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x114844 [0x49, 0x83, 0xD0, 0x00] (fun s => s.RIP = 0x114844) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114844 8 0x0))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x114844 8 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x114844 0x49 0xd0 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f166 : InstrSpec 0x114848 [0x4D, 0x0F, 0xA4, 0xDA, 0x0C] (fun s => s.RIP = 0x114848) (shldR64R64Effect 0x114848 5 10 11 12)
      [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x114848 5 10 11 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x114848 0x4d (by decide) 0xda (by decide) 0xc) pre_rip
  have f167 : InstrSpec 0x11484d [0x48, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x11484d) (movR64Imm64Effect 0x11484d 1 0xffffffffffffe)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x11484d 1 0xffffffffffffe).toInstrSpec (mov_r64_imm64_effect_step 0x11484d 0x48 0xb9 (by decide) (by decide) 0xffffffffffffe) pre_rip
  have f168 : InstrSpec 0x114857 [0x48, 0x23, 0x4C, 0x24, 0x30] (LoadPre 0x114857 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x114857 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x114857 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (andR64M64Effect_footprint 0x114857 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (and_r64_m64_effect_step 0x114857 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f169 : InstrSpec 0x11485c [0x49, 0x0F, 0xA4, 0xF0, 0x0C] (fun s => s.RIP = 0x11485c) (shldR64R64Effect 0x11485c 5 8 6 12)
      [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x11485c 5 8 6 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x11485c 0x49 (by decide) 0xf0 (by decide) 0xc) pre_rip
  have f170 : InstrSpec 0x114861 [0x4C, 0x21, 0xF6] (fun s => s.RIP = 0x114861) (andR64R64Effect 0x114861 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114861 6 14).toInstrSpec (and_r64_r64_effect_step 0x114861 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x114864 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x114864) (movR64R64Effect 0x114864 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x114864 0 10).toInstrSpec (mov_r64_r64_effect_step 0x114864 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f172 : InstrSpec 0x114867 [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x114867) (movR64Imm64Effect 0x114867 2 0x1000003d10)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x114867 2 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x114867 0x48 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f173 : InstrSpec 0x114871 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x114871) (mulR64Effect 0x114871 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x114871 2).toInstrSpec (mul_r64_effect_step 0x114871 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f174 : InstrSpec 0x114874 [0x48, 0x01, 0xC1] (fun s => s.RIP = 0x114874) (addR64R64Effect 0x114874 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114874 1 0).toInstrSpec (add_r64_r64_effect_step 0x114874 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x114877 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x114877) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114877 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x114877 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x114877 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f176 : InstrSpec 0x11487b [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11487b) (movR64R64Effect 0x11487b 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11487b 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11487b 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x11487e [0x4C, 0x01, 0xC1] (fun s => s.RIP = 0x11487e) (addR64R64Effect 0x11487e 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11487e 1 8).toInstrSpec (add_r64_r64_effect_step 0x11487e 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f178 : InstrSpec 0x114881 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x114881) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114881 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x114881 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x114881 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f179 : InstrSpec 0x114885 [0x49, 0x21, 0xCE] (fun s => s.RIP = 0x114885) (andR64R64Effect 0x114885 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114885 14 1).toInstrSpec (and_r64_r64_effect_step 0x114885 0x49 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 400) (RestInside.out (n := 400) f160 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 401) f160 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 402) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 400), (7, 7), (8, 398), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (16, 401), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114836) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.out (n := 403) f161 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 404) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 400), (7, 7), (8, 403), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11483b) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 405) (RestInside.out (n := 405) f162 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 406) f162 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 407) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 405), (7, 7), (8, 403), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (16, 406), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11483e) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 408) (RestInside.out (n := 408) f163 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 409) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 405), (7, 7), (8, 408), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114841) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f164 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 411) f164 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 412) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 410), (7, 7), (8, 408), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (16, 411), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114844) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 413) (RestInside.out (n := 413) f165 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 414) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 410), (7, 7), (8, 413), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114848) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 415) (RestInside.out (n := 415) f166 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 416) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 410), (7, 7), (8, 413), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11484d) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 417) (RestInside.out (n := 417) f167 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 418) (ρ' := [(0, 391), (1, 417), (2, 392), (3, 381), (4, 65), (5, 344), (6, 410), (7, 7), (8, 413), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114857) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 419) (RestInside.out (n := 419) f168 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 420) (ρ' := [(0, 391), (1, 419), (2, 392), (3, 381), (4, 65), (5, 344), (6, 410), (7, 7), (8, 413), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11485c) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 421) (RestInside.out (n := 421) f169 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 422) (ρ' := [(0, 391), (1, 419), (2, 392), (3, 381), (4, 65), (5, 344), (6, 410), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114861) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 423) (RestInside.out (n := 423) f170 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 424) (ρ' := [(0, 391), (1, 419), (2, 392), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114864) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f171 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 426) (ρ' := [(0, 425), (1, 419), (2, 392), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114867) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 427) (RestInside.out (n := 427) f172 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 428) (ρ' := [(0, 425), (1, 419), (2, 427), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114871) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 429) (RestInside.out (n := 429) f173 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 430) f173 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 431) (ρ' := [(0, 429), (1, 419), (2, 430), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114874) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 432) (RestInside.out (n := 432) f174 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 433) f174 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 434) (ρ' := [(0, 429), (1, 432), (2, 430), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (16, 433), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114877) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 435) (RestInside.out (n := 435) f175 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 436) (ρ' := [(0, 429), (1, 432), (2, 435), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11487b) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 437) (RestInside.out (n := 437) f176 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 438) (ρ' := [(0, 437), (1, 432), (2, 435), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11487e) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 439) (RestInside.out (n := 439) f177 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 440) f177 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 441) (ρ' := [(0, 437), (1, 439), (2, 435), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (16, 440), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114881) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.out (n := 442) f178 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 443) (ρ' := [(0, 437), (1, 439), (2, 442), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114885) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 444) (RestInside.out (n := 444) f179 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 445) (ρ' := [(0, 437), (1, 439), (2, 442), (3, 381), (4, 65), (5, 344), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 383), (13, 354), (14, 444), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114888) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_9 code

theorem rest_l1145f0_7 [Bindings] (code : CodeMap) :
    Rest (n := 356) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 350), (1, 271), (2, 351), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]
      58 0x1147ee bytes_l1145f0_7 b_l1145f0_7 := by
  have f140 : InstrSpec 0x1147ee [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x1147ee (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1147ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1147ee 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1147ee 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1147ee 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f141 : InstrSpec 0x1147f2 [0x48, 0xF7, 0xE3] (fun s => s.RIP = 0x1147f2) (mulR64Effect 0x1147f2 3)
      [.gpr 3, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1147f2 3).toInstrSpec (mul_r64_effect_step 0x1147f2 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x1147f5 [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x1147f5) (movR64R64Effect 0x1147f5 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1147f5 10 2).toInstrSpec (mov_r64_r64_effect_step 0x1147f5 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x1147f8 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x1147f8) (movR64R64Effect 0x1147f8 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1147f8 11 0).toInstrSpec (mov_r64_r64_effect_step 0x1147f8 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x1147fb [0x49, 0x0F, 0xA4, 0xC2, 0x01] (fun s => s.RIP = 0x1147fb) (shldR64R64Effect 0x1147fb 5 10 0 1)
      [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1147fb 5 10 0 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1147fb 0x49 (by decide) 0xc2 (by decide) 0x1) pre_rip
  have f145 : InstrSpec 0x114800 [0x49, 0x01, 0xC3] (fun s => s.RIP = 0x114800) (addR64R64Effect 0x114800 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114800 11 0).toInstrSpec (add_r64_r64_effect_step 0x114800 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f146 : InstrSpec 0x114803 [0x4D, 0x01, 0xC3] (fun s => s.RIP = 0x114803) (addR64R64Effect 0x114803 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114803 11 8).toInstrSpec (add_r64_r64_effect_step 0x114803 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f147 : InstrSpec 0x114806 [0x49, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x114806) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114806 10 0x0))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x114806 10 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x114806 0x49 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f148 : InstrSpec 0x11480a [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x11480a) (movR64R64Effect 0x11480a 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11480a 0 11).toInstrSpec (mov_r64_r64_effect_step 0x11480a 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x11480d [0x4C, 0x21, 0xF0] (fun s => s.RIP = 0x11480d) (andR64R64Effect 0x11480d 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11480d 0 14).toInstrSpec (and_r64_r64_effect_step 0x11480d 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x114810 [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x114810) (mulR64Effect 0x114810 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x114810 6).toInstrSpec (mul_r64_effect_step 0x114810 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x114813 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x114813) (movR64R64Effect 0x114813 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x114813 3 0).toInstrSpec (mov_r64_r64_effect_step 0x114813 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x114816 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x114816) (movR64R64Effect 0x114816 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x114816 12 2).toInstrSpec (mov_r64_r64_effect_step 0x114816 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f153 : InstrSpec 0x114819 [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x114819 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x114819 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114819 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x114819 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x114819 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f154 : InstrSpec 0x11481e [0x48, 0x0F, 0xAF, 0xCA] (fun s => s.RIP = 0x11481e) (imulR64R64Effect 0x11481e 4 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x11481e 4 1 2).toInstrSpec (imul_r64_r64_effect_step 0x11481e 0x48 (by decide) 0xca (by decide)) pre_rip
  have f155 : InstrSpec 0x114822 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x114822 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x114822 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114822 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x114822 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x114822 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f156 : InstrSpec 0x114827 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x114827) (mulR64Effect 0x114827 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x114827 2).toInstrSpec (mul_r64_effect_step 0x114827 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x11482a [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11482a) (movR64R64Effect 0x11482a 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11482a 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11482a 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x11482d [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x11482d) (movR64R64Effect 0x11482d 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11482d 8 2).toInstrSpec (mov_r64_r64_effect_step 0x11482d 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x114830 [0x49, 0x01, 0xC8] (fun s => s.RIP = 0x114830) (addR64R64Effect 0x114830 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114830 8 1).toInstrSpec (add_r64_r64_effect_step 0x114830 0x49 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 356) (RestInside.out (n := 356) f140 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 357) (ρ' := [(0, 356), (1, 271), (2, 351), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147f2) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 358) (RestInside.out (n := 358) f141 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 359) f141 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 360) (ρ' := [(0, 358), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147f5) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f142 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 358), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 361), (11, 69), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147f8) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f143 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 364) (ρ' := [(0, 358), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 361), (11, 363), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147fb) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f144 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 358), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 365), (11, 363), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114800) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f145 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 358), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 365), (11, 367), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114803) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f146 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 370) f146 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 371) (ρ' := [(0, 358), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 365), (11, 369), (12, 284), (13, 354), (14, 286), (15, 346), (16, 370), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114806) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.out (n := 372) f147 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 373) (ρ' := [(0, 358), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11480a) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 374) (RestInside.out (n := 374) f148 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 375) (ρ' := [(0, 374), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11480d) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f149 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 376), (1, 271), (2, 359), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114810) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f150 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 379) f150 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 380) (ρ' := [(0, 378), (1, 271), (2, 379), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114813) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 381) (RestInside.out (n := 381) f151 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 382) (ρ' := [(0, 378), (1, 271), (2, 379), (3, 381), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114816) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 383) (RestInside.out (n := 383) f152 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 384) (ρ' := [(0, 378), (1, 271), (2, 379), (3, 381), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114819) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 385) (RestInside.out (n := 385) f153 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 386) (ρ' := [(0, 378), (1, 271), (2, 385), (3, 381), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11481e) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 387) (RestInside.out (n := 387) f154 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 388) (ρ' := [(0, 378), (1, 387), (2, 385), (3, 381), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114822) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f155 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 389), (1, 387), (2, 385), (3, 381), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114827) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f156 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 392) f156 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 393) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11482a) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.out (n := 394) f157 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 395) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 394), (7, 7), (8, 321), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11482d) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 396) (RestInside.out (n := 396) f158 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 397) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 394), (7, 7), (8, 396), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114830) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f159 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 391), (1, 387), (2, 392), (3, 381), (4, 65), (5, 344), (6, 394), (7, 7), (8, 398), (9, 190), (10, 372), (11, 369), (12, 383), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114833) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_8 code

theorem rest_l1145f0_6 [Bindings] (code : CodeMap) :
    Rest (n := 311) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 309), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]
      78 0x1147a3 bytes_l1145f0_6 b_l1145f0_6 := by
  have f120 : InstrSpec 0x1147a3 [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x1147a3) (addR64R64Effect 0x1147a3 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1147a3 0 6).toInstrSpec (add_r64_r64_effect_step 0x1147a3 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x1147a6 [0x49, 0x11, 0xD0] (fun s => s.RIP = 0x1147a6) (atFlags StatusFlags.CF (adcR64R64Effect 0x1147a6 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1147a6 8 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1147a6 0x49 0xd0 c (by decide) (by decide))) pre_rip
  have f122 : InstrSpec 0x1147a9 [0x4C, 0x01, 0xF8] (fun s => s.RIP = 0x1147a9) (addR64R64Effect 0x1147a9 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1147a9 0 15).toInstrSpec (add_r64_r64_effect_step 0x1147a9 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x1147ac [0x49, 0x83, 0xD0, 0x00] (fun s => s.RIP = 0x1147ac) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1147ac 8 0x0))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1147ac 8 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1147ac 0x49 0xd0 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f124 : InstrSpec 0x1147b0 [0x49, 0x0F, 0xA4, 0xC0, 0x0C] (fun s => s.RIP = 0x1147b0) (shldR64R64Effect 0x1147b0 5 8 0 12)
      [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1147b0 5 8 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1147b0 0x49 (by decide) 0xc0 (by decide) 0xc) pre_rip
  have f125 : InstrSpec 0x1147b5 [0x4C, 0x21, 0xF0] (fun s => s.RIP = 0x1147b5) (andR64R64Effect 0x1147b5 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1147b5 0 14).toInstrSpec (and_r64_r64_effect_step 0x1147b5 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x1147b8 [0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1147b8) (movR64Imm64Effect 0x1147b8 6 0x1000003d10)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x1147b8 6 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x1147b8 0x48 0xbe (by decide) (by decide) 0x1000003d10) pre_rip
  have f127 : InstrSpec 0x1147c2 [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x1147c2) (mulR64Effect 0x1147c2 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1147c2 6).toInstrSpec (mul_r64_effect_step 0x1147c2 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x1147c5 [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x1147c5) (movR64R64Effect 0x1147c5 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1147c5 5 2).toInstrSpec (mov_r64_r64_effect_step 0x1147c5 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x1147c8 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x1147c8) (movR64R64Effect 0x1147c8 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1147c8 15 0).toInstrSpec (mov_r64_r64_effect_step 0x1147c8 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x1147cb [0x4D, 0x01, 0xD7] (fun s => s.RIP = 0x1147cb) (addR64R64Effect 0x1147cb 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1147cb 15 10).toInstrSpec (add_r64_r64_effect_step 0x1147cb 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x1147ce [0x4C, 0x11, 0xE5] (fun s => s.RIP = 0x1147ce) (atFlags StatusFlags.CF (adcR64R64Effect 0x1147ce 5 12))
      [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1147ce 5 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1147ce 0x4c 0xe5 c (by decide) (by decide))) pre_rip
  have f132 : InstrSpec 0x1147d1 [0x4D, 0x01, 0xEF] (fun s => s.RIP = 0x1147d1) (addR64R64Effect 0x1147d1 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1147d1 15 13).toInstrSpec (add_r64_r64_effect_step 0x1147d1 0x4d 0xef (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x1147d4 [0x48, 0x83, 0xD5, 0x00] (fun s => s.RIP = 0x1147d4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1147d4 5 0x0))
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1147d4 5 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1147d4 0x48 0xd5 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f134 : InstrSpec 0x1147d8 [0x4C, 0x0F, 0xA4, 0xFD, 0x0C] (fun s => s.RIP = 0x1147d8) (shldR64R64Effect 0x1147d8 5 5 15 12)
      [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1147d8 5 5 15 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1147d8 0x4c (by decide) 0xfd (by decide) 0xc) pre_rip
  have f135 : InstrSpec 0x1147dd [0x4D, 0x21, 0xF7] (fun s => s.RIP = 0x1147dd) (andR64R64Effect 0x1147dd 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1147dd 15 14).toInstrSpec (and_r64_r64_effect_step 0x1147dd 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x1147e0 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x1147e0) (movR64R64Effect 0x1147e0 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1147e0 0 11).toInstrSpec (mov_r64_r64_effect_step 0x1147e0 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x1147e3 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x1147e3) (mulR64Effect 0x1147e3 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1147e3 11).toInstrSpec (mul_r64_effect_step 0x1147e3 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x1147e6 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x1147e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1147e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1147e6 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1147e6 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1147e6 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f139 : InstrSpec 0x1147eb [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x1147eb) (movR64R64Effect 0x1147eb 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1147eb 13 0).toInstrSpec (mov_r64_r64_effect_step 0x1147eb 0x49 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f120 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 312) f120 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 313) (ρ' := [(0, 311), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (16, 312), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147a6) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f121 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 311), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 314), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147a9) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f122 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 317) f122 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 318) (ρ' := [(0, 316), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 314), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (16, 317), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147ac) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 319) (RestInside.out (n := 319) f123 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 320) (ρ' := [(0, 316), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 319), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147b0) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 321) (RestInside.out (n := 321) f124 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 322) (ρ' := [(0, 316), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147b5) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f125 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 324) (ρ' := [(0, 323), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147b8) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 325) (RestInside.out (n := 325) f126 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 326) (ρ' := [(0, 323), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147c2) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 327) (RestInside.out (n := 327) f127 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 328) f127 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 329) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 97), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147c5) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f128 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 330), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147c8) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f129 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 330), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147cb) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f130 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 335) f130 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 336) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 330), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 334), (16, 335), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147ce) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f131 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 337), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 334), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147d1) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f132 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 340) f132 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 341) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 337), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 339), (16, 340), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147d4) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f133 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 343) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 342), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 339), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147d8) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f134 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 339), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147dd) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f135 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 327), (1, 271), (2, 328), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147e0) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f136 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 348), (1, 271), (2, 328), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147e3) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f137 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 351) f137 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 352) (ρ' := [(0, 350), (1, 271), (2, 351), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147e6) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.exec (n := 353) (ρ' := [(0, 350), (1, 271), (2, 351), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147eb) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 354) (RestInside.out (n := 354) f139 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 355) (ρ' := [(0, 350), (1, 271), (2, 351), (3, 302), (4, 65), (5, 344), (6, 325), (7, 7), (8, 321), (9, 190), (10, 280), (11, 69), (12, 284), (13, 354), (14, 286), (15, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147ee) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_7 code

theorem rest_l1145f0_5 [Bindings] (code : CodeMap) :
    Rest (n := 270) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 268), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 266), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]
      98 0x114755 bytes_l1145f0_5 b_l1145f0_5 := by
  have f100 : InstrSpec 0x114755 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x114755 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x114755 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114755 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x114755 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x114755 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f101 : InstrSpec 0x11475a [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x11475a) (shrR64Effect 0x11475a 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11475a 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x11475a 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x11475e [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x11475e) (movR64R64Effect 0x11475e 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11475e 6 1).toInstrSpec (mov_r64_r64_effect_step 0x11475e 0x48 0xce (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x114761 [0x49, 0x0F, 0xAF, 0xF3] (fun s => s.RIP = 0x114761) (imulR64R64Effect 0x114761 4 6 11)
      [.gpr 6, .gpr 11] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x114761 4 6 11).toInstrSpec (imul_r64_r64_effect_step 0x114761 0x49 (by decide) 0xf3 (by decide)) pre_rip
  have f104 : InstrSpec 0x114765 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x114765) (mulR64Effect 0x114765 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x114765 11).toInstrSpec (mul_r64_effect_step 0x114765 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x114768 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x114768) (movR64R64Effect 0x114768 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x114768 10 0).toInstrSpec (mov_r64_r64_effect_step 0x114768 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x11476b [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x11476b) (movR64R64Effect 0x11476b 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x11476b 12 2).toInstrSpec (mov_r64_r64_effect_step 0x11476b 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x11476e [0x49, 0x01, 0xF4] (fun s => s.RIP = 0x11476e) (addR64R64Effect 0x11476e 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11476e 12 6).toInstrSpec (add_r64_r64_effect_step 0x11476e 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x114771 [0x49, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x114771) (movR64Imm64Effect 0x114771 14 0xfffffffffffff)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x114771 14 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x114771 0x49 0xbe (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f109 : InstrSpec 0x11477b [0x4D, 0x21, 0xF0] (fun s => s.RIP = 0x11477b) (andR64R64Effect 0x11477b 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11477b 8 14).toInstrSpec (and_r64_r64_effect_step 0x11477b 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x11477e [0x4C, 0x89, 0x44, 0x24, 0x28] (StorePre 0x11477e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11477e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11477e 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11477e 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x11477e 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f111 : InstrSpec 0x114783 [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x114783 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x114783 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x114783 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x114783 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x114783 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f112 : InstrSpec 0x114787 [0x48, 0xF7, 0xE0] (fun s => s.RIP = 0x114787) (mulR64Effect 0x114787 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x114787 0).toInstrSpec (mul_r64_effect_step 0x114787 0x48 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x11478a [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x11478a) (movR64R64Effect 0x11478a 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11478a 8 2).toInstrSpec (mov_r64_r64_effect_step 0x11478a 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x11478d [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11478d) (movR64R64Effect 0x11478d 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11478d 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11478d 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x114790 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x114790) (movR64R64Effect 0x114790 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x114790 0 3).toInstrSpec (mov_r64_r64_effect_step 0x114790 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x114793 [0x48, 0x8B, 0x5C, 0x24, 0x18] (LoadPre 0x114793 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x114793 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114793 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x114793 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x114793 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f117 : InstrSpec 0x114798 [0x48, 0xF7, 0xE3] (fun s => s.RIP = 0x114798) (mulR64Effect 0x114798 3)
      [.gpr 3, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x114798 3).toInstrSpec (mul_r64_effect_step 0x114798 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x11479b [0x48, 0x0F, 0xA4, 0xC2, 0x01] (fun s => s.RIP = 0x11479b) (shldR64R64Effect 0x11479b 5 2 0 1)
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x11479b 5 2 0 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x11479b 0x48 (by decide) 0xc2 (by decide) 0x1) pre_rip
  have f119 : InstrSpec 0x1147a0 [0x48, 0x01, 0xC0] (fun s => s.RIP = 0x1147a0) (addR64R64Effect 0x1147a0 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1147a0 0 0).toInstrSpec (add_r64_r64_effect_step 0x1147a0 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 270) (RestInside.exec (n := 270) (ρ' := [(0, 268), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 266), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11475a) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f101 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 272) (ρ' := [(0, 268), (1, 271), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 266), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11475e) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f102 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 268), (1, 271), (2, 255), (3, 214), (4, 65), (5, 97), (6, 273), (7, 7), (8, 266), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114761) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f103 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 268), (1, 271), (2, 255), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 266), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114765) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f104 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 278) f104 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 279) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 266), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114768) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f105 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 266), (9, 190), (10, 280), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11476b) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f106 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 266), (9, 190), (10, 280), (11, 69), (12, 282), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11476e) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f107 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 266), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114771) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f108 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 266), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11477b) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f109 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 288), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11477e) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.exec (n := 290) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 288), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114783) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f111 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 291), (1, 271), (2, 278), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 288), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114787) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f112 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 294) f112 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 295) (ρ' := [(0, 293), (1, 271), (2, 294), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 288), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11478a) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.out (n := 296) f113 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 297) (ρ' := [(0, 293), (1, 271), (2, 294), (3, 214), (4, 65), (5, 97), (6, 275), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11478d) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f114 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 293), (1, 271), (2, 294), (3, 214), (4, 65), (5, 97), (6, 298), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114790) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f115 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 300), (1, 271), (2, 294), (3, 214), (4, 65), (5, 97), (6, 298), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114793) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f116 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 300), (1, 271), (2, 294), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114798) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f117 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 305) f117 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 306) (ρ' := [(0, 304), (1, 271), (2, 305), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11479b) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f118 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 308) (ρ' := [(0, 304), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147a0) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f119 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 309), (1, 271), (2, 307), (3, 302), (4, 65), (5, 97), (6, 298), (7, 7), (8, 296), (9, 190), (10, 280), (11, 69), (12, 284), (13, 264), (14, 286), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1147a3) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_6 code

theorem rest_l1145f0_4 [Bindings] (code : CodeMap) :
    Rest (n := 225) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 223), (1, 67), (2, 217), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 219), (22, 22), (39, 39), (50, 50), (51, 51)]
      118 0x114702 bytes_l1145f0_4 b_l1145f0_4 := by
  have f80 : InstrSpec 0x114702 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x114702) (mulR64Effect 0x114702 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x114702 11).toInstrSpec (mul_r64_effect_step 0x114702 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x114705 [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x114705) (addR64R64Effect 0x114705 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114705 0 6).toInstrSpec (add_r64_r64_effect_step 0x114705 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x114708 [0x49, 0x11, 0xD7] (fun s => s.RIP = 0x114708) (atFlags StatusFlags.CF (adcR64R64Effect 0x114708 15 2))
      [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x114708 15 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x114708 0x49 0xd7 c (by decide) (by decide))) pre_rip
  have f83 : InstrSpec 0x11470b [0x49, 0x0F, 0xA4, 0xC7, 0x01] (fun s => s.RIP = 0x11470b) (shldR64R64Effect 0x11470b 5 15 0 1)
      [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x11470b 5 15 0 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x11470b 0x49 (by decide) 0xc7 (by decide) 0x1) pre_rip
  have f84 : InstrSpec 0x114710 [0x48, 0x01, 0xC0] (fun s => s.RIP = 0x114710) (addR64R64Effect 0x114710 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114710 0 0).toInstrSpec (add_r64_r64_effect_step 0x114710 0x48 0xc0 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x114713 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x114713) (addR64R64Effect 0x114713 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114713 0 14).toInstrSpec (add_r64_r64_effect_step 0x114713 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x114716 [0x49, 0x83, 0xD7, 0x00] (fun s => s.RIP = 0x114716) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114716 15 0x0))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x114716 15 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x114716 0x49 0xd7 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f87 : InstrSpec 0x11471a [0x49, 0x0F, 0xA4, 0xC7, 0x0C] (fun s => s.RIP = 0x11471a) (shldR64R64Effect 0x11471a 5 15 0 12)
      [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x11471a 5 15 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x11471a 0x49 (by decide) 0xc7 (by decide) 0xc) pre_rip
  have f88 : InstrSpec 0x11471f [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x11471f) (shlR64Effect 0x11471f 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x11471f 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x11471f 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x114723 [0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00] (fun s => s.RIP = 0x114723) (movR64Imm64Effect 0x114723 2 0xfffffffffffff0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x114723 2 0xfffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x114723 0x48 0xba (by decide) (by decide) 0xfffffffffffff0) pre_rip
  have f90 : InstrSpec 0x11472d [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x11472d) (andR64R64Effect 0x11472d 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11472d 0 2).toInstrSpec (and_r64_r64_effect_step 0x11472d 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x114730 [0x4C, 0x09, 0xD0] (fun s => s.RIP = 0x114730) (orR64R64Effect 0x114730 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x114730 0 10).toInstrSpec (or_r64_r64_effect_step 0x114730 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x114733 [0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x114733) (movR64Imm64Effect 0x114733 2 0x1000003d1)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x114733 2 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x114733 0x48 0xba (by decide) (by decide) 0x1000003d1) pre_rip
  have f93 : InstrSpec 0x11473d [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x11473d) (mulR64Effect 0x11473d 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11473d 2).toInstrSpec (mul_r64_effect_step 0x11473d 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x114740 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x114740) (movR64R64Effect 0x114740 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x114740 13 2).toInstrSpec (mov_r64_r64_effect_step 0x114740 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x114743 [0x4C, 0x01, 0xE0] (fun s => s.RIP = 0x114743) (addR64R64Effect 0x114743 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114743 0 12).toInstrSpec (add_r64_r64_effect_step 0x114743 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x114746 [0x4D, 0x11, 0xC5] (fun s => s.RIP = 0x114746) (atFlags StatusFlags.CF (adcR64R64Effect 0x114746 13 8))
      [.gpr 13, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x114746 13 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x114746 0x4d 0xc5 c (by decide) (by decide))) pre_rip
  have f97 : InstrSpec 0x114749 [0x49, 0x0F, 0xA4, 0xC5, 0x0C] (fun s => s.RIP = 0x114749) (shldR64R64Effect 0x114749 5 13 0 12)
      [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x114749 5 13 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x114749 0x49 (by decide) 0xc5 (by decide) 0xc) pre_rip
  have f98 : InstrSpec 0x11474e [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x11474e) (movR64R64Effect 0x11474e 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11474e 8 0).toInstrSpec (mov_r64_r64_effect_step 0x11474e 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x114751 [0x48, 0x8D, 0x04, 0x09] (fun s => s.RIP = 0x114751) (leaR64Effect 0x114751 0 (.sib 1 (some 1) 0 .none))
      [.gpr 1, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x114751 0 (.sib 1 (some 1) 0 .none)).toInstrSpec (lea_r64_effect_step 0x114751 0x48 (by decide) 0 (.sib 1 (some 1) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f80 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 226) f80 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 227) (ρ' := [(0, 225), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 219), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114705) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f81 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 229) f81 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 230) (ρ' := [(0, 228), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 219), (16, 229), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114708) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f82 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 228), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11470b) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f83 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 234) (ρ' := [(0, 228), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114710) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f84 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 235), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114713) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f85 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 238) f85 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 239) (ρ' := [(0, 237), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 233), (16, 238), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114716) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f86 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 237), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 240), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11471a) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f87 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 237), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11471f) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f88 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 244), (1, 67), (2, 226), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114723) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f89 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 244), (1, 67), (2, 246), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11472d) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 248), (1, 67), (2, 246), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114730) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f91 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 250), (1, 67), (2, 246), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114733) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f92 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 250), (1, 67), (2, 252), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11473d) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f93 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 255) f93 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 256) (ρ' := [(0, 254), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114740) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f94 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 254), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 257), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114743) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f95 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 260) f95 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 261) (ρ' := [(0, 259), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 257), (14, 195), (15, 242), (16, 260), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114746) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f96 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 259), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 262), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114749) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f97 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 259), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11474e) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f98 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 259), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 266), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114751) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 268), (1, 67), (2, 255), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 266), (9, 190), (10, 210), (11, 69), (12, 206), (13, 264), (14, 195), (15, 242), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114755) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_5 code

theorem rest_l1145f0_3 [Bindings] (code : CodeMap) :
    Rest (n := 180) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 178), (10, 139), (11, 69), (12, 141), (13, 160), (14, 176), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]
      138 0x1146bf bytes_l1145f0_3 b_l1145f0_3 := by
  have f60 : InstrSpec 0x1146bf [0x4D, 0x01, 0xE1] (fun s => s.RIP = 0x1146bf) (addR64R64Effect 0x1146bf 9 12)
      [.gpr 9, .gpr 12] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1146bf 9 12).toInstrSpec (add_r64_r64_effect_step 0x1146bf 0x4d 0xe1 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x1146c2 [0x4D, 0x11, 0xD6] (fun s => s.RIP = 0x1146c2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1146c2 14 10))
      [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1146c2 14 10).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1146c2 0x4d 0xd6 c (by decide) (by decide))) pre_rip
  have f62 : InstrSpec 0x1146c5 [0x49, 0x01, 0xF1] (fun s => s.RIP = 0x1146c5) (addR64R64Effect 0x1146c5 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1146c5 9 6).toInstrSpec (add_r64_r64_effect_step 0x1146c5 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x1146c8 [0x4D, 0x11, 0xFE] (fun s => s.RIP = 0x1146c8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1146c8 14 15))
      [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1146c8 14 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1146c8 0x4d 0xfe c (by decide) (by decide))) pre_rip
  have f64 : InstrSpec 0x1146cb [0x4D, 0x01, 0xC1] (fun s => s.RIP = 0x1146cb) (addR64R64Effect 0x1146cb 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1146cb 9 8).toInstrSpec (add_r64_r64_effect_step 0x1146cb 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x1146ce [0x49, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x1146ce) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1146ce 14 0x0))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1146ce 14 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1146ce 0x49 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f66 : InstrSpec 0x1146d2 [0x4D, 0x0F, 0xA4, 0xCE, 0x0C] (fun s => s.RIP = 0x1146d2) (shldR64R64Effect 0x1146d2 5 14 9 12)
      [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1146d2 5 14 9 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1146d2 0x4d (by decide) 0xce (by decide) 0xc) pre_rip
  have f67 : InstrSpec 0x1146d7 [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x1146d7) (movR64R64Effect 0x1146d7 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1146d7 10 9).toInstrSpec (mov_r64_r64_effect_step 0x1146d7 0x4d 0xca (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x1146da [0x49, 0xC1, 0xEA, 0x30] (fun s => s.RIP = 0x1146da) (shrR64Effect 0x1146da 4 10 48)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x1146da 4 10 48).toInstrSpec (shr_r64_imm8_effect_step 0x1146da 0x49 0xea 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x1146de [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1146de) (movR64R64Effect 0x1146de 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1146de 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1146de 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x1146e1 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x1146e1) (mulR64Effect 0x1146e1 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1146e1 1).toInstrSpec (mul_r64_effect_step 0x1146e1 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x1146e4 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x1146e4) (movR64R64Effect 0x1146e4 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1146e4 12 0).toInstrSpec (mov_r64_r64_effect_step 0x1146e4 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x1146e7 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x1146e7) (movR64R64Effect 0x1146e7 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1146e7 8 2).toInstrSpec (mov_r64_r64_effect_step 0x1146e7 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x1146ea [0x41, 0x83, 0xE2, 0x0F] (fun s => s.RIP = 0x1146ea) (andR32Imm8Effect 0x1146ea 4 10 0xf)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1146ea 4 10 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x1146ea 0x41 0xe2 0xf (by decide) (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x1146ee [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1146ee) (movR64R64Effect 0x1146ee 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1146ee 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1146ee 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x1146f1 [0x48, 0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x1146f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1146f1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1146f1 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1146f1 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1146f1 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x1146f6 [0x48, 0xF7, 0xE3] (fun s => s.RIP = 0x1146f6) (mulR64Effect 0x1146f6 3)
      [.gpr 3, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1146f6 3).toInstrSpec (mul_r64_effect_step 0x1146f6 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x1146f9 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x1146f9) (movR64R64Effect 0x1146f9 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1146f9 15 2).toInstrSpec (mov_r64_r64_effect_step 0x1146f9 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x1146fc [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x1146fc) (movR64R64Effect 0x1146fc 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1146fc 6 0).toInstrSpec (mov_r64_r64_effect_step 0x1146fc 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x1146ff [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x1146ff) (movR64R64Effect 0x1146ff 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1146ff 0 5).toInstrSpec (mov_r64_r64_effect_step 0x1146ff 0x48 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f60 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 181) f60 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 182) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 180), (10, 139), (11, 69), (12, 141), (13, 160), (14, 176), (15, 148), (16, 181), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146c2) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f61 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 180), (10, 139), (11, 69), (12, 141), (13, 160), (14, 183), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146c5) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f62 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 186) f62 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 187) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 185), (10, 139), (11, 69), (12, 141), (13, 160), (14, 183), (15, 148), (16, 186), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146c8) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f63 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 185), (10, 139), (11, 69), (12, 141), (13, 160), (14, 188), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146cb) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f64 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 191) f64 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 192) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 190), (10, 139), (11, 69), (12, 141), (13, 160), (14, 188), (15, 148), (16, 191), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146ce) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f65 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 190), (10, 139), (11, 69), (12, 141), (13, 160), (14, 193), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146d2) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f66 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 190), (10, 139), (11, 69), (12, 141), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146d7) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f67 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 190), (10, 197), (11, 69), (12, 141), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146da) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f68 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 190), (10, 199), (11, 69), (12, 141), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146de) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f69 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 201), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 190), (10, 199), (11, 69), (12, 141), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146e1) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 204) f70 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 205) (ρ' := [(0, 203), (1, 67), (2, 204), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 190), (10, 199), (11, 69), (12, 141), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146e4) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f71 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 203), (1, 67), (2, 204), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 190), (10, 199), (11, 69), (12, 206), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146e7) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f72 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 203), (1, 67), (2, 204), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 208), (9, 190), (10, 199), (11, 69), (12, 206), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146ea) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f73 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 203), (1, 67), (2, 204), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146ee) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f74 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 212), (1, 67), (2, 204), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146f1) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f75 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 212), (1, 67), (2, 204), (3, 214), (4, 65), (5, 97), (6, 150), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146f6) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f76 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 217) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 218) (ρ' := [(0, 216), (1, 67), (2, 217), (3, 214), (4, 65), (5, 97), (6, 150), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146f9) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f77 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 216), (1, 67), (2, 217), (3, 214), (4, 65), (5, 97), (6, 150), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 219), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146fc) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f78 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 216), (1, 67), (2, 217), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 219), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146ff) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f79 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 223), (1, 67), (2, 217), (3, 214), (4, 65), (5, 97), (6, 221), (7, 7), (8, 208), (9, 190), (10, 210), (11, 69), (12, 206), (13, 160), (14, 195), (15, 219), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114702) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_4 code

theorem rest_l1145f0_2 [Bindings] (code : CodeMap) :
    Rest (n := 136) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 134), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]
      158 0x11467e bytes_l1145f0_2 b_l1145f0_2 := by
  have f40 : InstrSpec 0x11467e [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x11467e) (mulR64Effect 0x11467e 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11467e 15).toInstrSpec (mul_r64_effect_step 0x11467e 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x114681 [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x114681) (movR64R64Effect 0x114681 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x114681 10 2).toInstrSpec (mov_r64_r64_effect_step 0x114681 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x114684 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x114684) (movR64R64Effect 0x114684 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x114684 12 0).toInstrSpec (mov_r64_r64_effect_step 0x114684 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x114687 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x114687) (movR64R64Effect 0x114687 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x114687 0 14).toInstrSpec (mov_r64_r64_effect_step 0x114687 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x11468a [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11468a) (mulR64Effect 0x11468a 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11468a 13).toInstrSpec (mul_r64_effect_step 0x11468a 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x11468d [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x11468d) (movR64R64Effect 0x11468d 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11468d 15 2).toInstrSpec (mov_r64_r64_effect_step 0x11468d 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x114690 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x114690) (movR64R64Effect 0x114690 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x114690 6 0).toInstrSpec (mov_r64_r64_effect_step 0x114690 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x114693 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x114693) (movR64R64Effect 0x114693 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x114693 0 5).toInstrSpec (mov_r64_r64_effect_step 0x114693 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x114696 [0x48, 0x89, 0x6C, 0x24, 0x18] (StorePre 0x114696 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x114696 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114696 5 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x114696 5 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x114696 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x11469b [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x11469b) (mulR64Effect 0x11469b 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11469b 1).toInstrSpec (mul_r64_effect_step 0x11469b 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x11469e [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x11469e) (movR64R64Effect 0x11469e 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11469e 14 2).toInstrSpec (mov_r64_r64_effect_step 0x11469e 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x1146a1 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x1146a1) (movR64R64Effect 0x1146a1 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1146a1 13 0).toInstrSpec (mov_r64_r64_effect_step 0x1146a1 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x1146a4 [0x48, 0x8B, 0x1C, 0x24] (LoadPre 0x1146a4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1146a4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1146a4 3 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1146a4 3 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1146a4 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x1146a8 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1146a8) (movR64R64Effect 0x1146a8 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1146a8 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1146a8 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x1146ab [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x1146ab) (mulR64Effect 0x1146ab 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1146ab 11).toInstrSpec (mul_r64_effect_step 0x1146ab 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x1146ae [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x1146ae) (movR64R64Effect 0x1146ae 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1146ae 9 0).toInstrSpec (mov_r64_r64_effect_step 0x1146ae 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x1146b1 [0x4D, 0x01, 0xE9] (fun s => s.RIP = 0x1146b1) (addR64R64Effect 0x1146b1 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1146b1 9 13).toInstrSpec (add_r64_r64_effect_step 0x1146b1 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x1146b4 [0x49, 0x11, 0xD6] (fun s => s.RIP = 0x1146b4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1146b4 14 2))
      [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1146b4 14 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1146b4 0x49 0xd6 c (by decide) (by decide))) pre_rip
  have f58 : InstrSpec 0x1146b7 [0x4D, 0x0F, 0xA4, 0xCE, 0x01] (fun s => s.RIP = 0x1146b7) (shldR64R64Effect 0x1146b7 5 14 9 1)
      [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1146b7 5 14 9 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1146b7 0x4d (by decide) 0xce (by decide) 0x1) pre_rip
  have f59 : InstrSpec 0x1146bc [0x4D, 0x01, 0xC9] (fun s => s.RIP = 0x1146bc) (addR64R64Effect 0x1146bc 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1146bc 9 9).toInstrSpec (add_r64_r64_effect_step 0x1146bc 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 137) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 138) (ρ' := [(0, 136), (1, 67), (2, 137), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114681) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f41 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 136), (1, 67), (2, 137), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 12), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114684) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f42 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 136), (1, 67), (2, 137), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114687) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 143), (1, 67), (2, 137), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11468a) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 146) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 147) (ρ' := [(0, 145), (1, 67), (2, 146), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11468d) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f45 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 145), (1, 67), (2, 146), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 129), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114690) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 145), (1, 67), (2, 146), (3, 81), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 129), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114693) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f47 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 152), (1, 67), (2, 146), (3, 81), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 129), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114696) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.exec (n := 154) (ρ' := [(0, 152), (1, 67), (2, 146), (3, 81), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 129), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11469b) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 156) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 157) (ρ' := [(0, 155), (1, 67), (2, 156), (3, 81), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 129), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11469e) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f50 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 155), (1, 67), (2, 156), (3, 81), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 116), (14, 158), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146a1) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f51 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 155), (1, 67), (2, 156), (3, 81), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 160), (14, 158), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146a4) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f52 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 155), (1, 67), (2, 156), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 160), (14, 158), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146a8) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 164), (1, 67), (2, 156), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 160), (14, 158), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146ab) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f54 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 167) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 168) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 99), (10, 139), (11, 69), (12, 141), (13, 160), (14, 158), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146ae) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f55 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 169), (10, 139), (11, 69), (12, 141), (13, 160), (14, 158), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146b1) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f56 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 172) f56 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 173) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 171), (10, 139), (11, 69), (12, 141), (13, 160), (14, 158), (15, 148), (16, 172), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146b4) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f57 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 171), (10, 139), (11, 69), (12, 141), (13, 160), (14, 174), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146b7) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f58 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 171), (10, 139), (11, 69), (12, 141), (13, 160), (14, 176), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146bc) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f59 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 166), (1, 67), (2, 167), (3, 162), (4, 65), (5, 97), (6, 150), (7, 7), (8, 131), (9, 178), (10, 139), (11, 69), (12, 141), (13, 160), (14, 176), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1146bf) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_3 code

theorem rest_l1145f0_1 [Bindings] (code : CodeMap) :
    Rest (n := 95) code lifted (codeRange 0x1145f0 bytes_l1145f0) [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (9, 88), (10, 92), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (16, 93), (22, 22), (39, 39), (50, 50), (51, 51)]
      178 0x114629 bytes_l1145f0_1 b_l1145f0_1 := by
  have f20 : InstrSpec 0x114629 [0x4D, 0x11, 0xC1] (fun s => s.RIP = 0x114629) (atFlags StatusFlags.CF (adcR64R64Effect 0x114629 9 8))
      [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x114629 9 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x114629 0x4d 0xc1 c (by decide) (by decide))) pre_rip
  have f21 : InstrSpec 0x11462c [0x48, 0x8B, 0x6E, 0x20] (LoadPre 0x11462c (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x11462c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11462c 5 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x11462c 5 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11462c 0x48 (by decide) 5 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x114630 [0x4D, 0x0F, 0xA4, 0xD1, 0x01] (fun s => s.RIP = 0x114630) (shldR64R64Effect 0x114630 5 9 10 1)
      [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x114630 5 9 10 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x114630 0x4d (by decide) 0xd1 (by decide) 0x1) pre_rip
  have f23 : InstrSpec 0x114635 [0x4D, 0x01, 0xD2] (fun s => s.RIP = 0x114635) (addR64R64Effect 0x114635 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114635 10 10).toInstrSpec (add_r64_r64_effect_step 0x114635 0x4d 0xd2 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x114638 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x114638) (movR64R64Effect 0x114638 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x114638 0 5).toInstrSpec (mov_r64_r64_effect_step 0x114638 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x11463b [0x48, 0xF7, 0xE5] (fun s => s.RIP = 0x11463b) (mulR64Effect 0x11463b 5)
      [.gpr 5, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11463b 5).toInstrSpec (mul_r64_effect_step 0x11463b 0x48 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x11463e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11463e) (movR64R64Effect 0x11463e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11463e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11463e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x114641 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x114641) (movR64R64Effect 0x114641 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x114641 14 2).toInstrSpec (mov_r64_r64_effect_step 0x114641 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x114644 [0x48, 0xB8, 0xFD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x114644) (movR64Imm64Effect 0x114644 0 0xffffffffffffd)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x114644 0 0xffffffffffffd).toInstrSpec (mov_r64_imm64_effect_step 0x114644 0x48 0xb8 (by decide) (by decide) 0xffffffffffffd) pre_rip
  have f29 : InstrSpec 0x11464e [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x11464e) (andR64R64Effect 0x11464e 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11464e 0 6).toInstrSpec (and_r64_r64_effect_step 0x11464e 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x114651 [0x49, 0xBD, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x114651) (movR64Imm64Effect 0x114651 13 0x1000003d10)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x114651 13 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x114651 0x49 0xbd (by decide) (by decide) 0x1000003d10) pre_rip
  have f31 : InstrSpec 0x11465b [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11465b) (mulR64Effect 0x11465b 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11465b 13).toInstrSpec (mul_r64_effect_step 0x11465b 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x11465e [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x11465e) (movR64R64Effect 0x11465e 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11465e 8 2).toInstrSpec (mov_r64_r64_effect_step 0x11465e 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x114661 [0x4C, 0x01, 0xD0] (fun s => s.RIP = 0x114661) (addR64R64Effect 0x114661 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114661 0 10).toInstrSpec (add_r64_r64_effect_step 0x114661 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x114664 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x114664 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x114664 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114664 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x114664 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x114664 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x114669 [0x4D, 0x11, 0xC8] (fun s => s.RIP = 0x114669) (atFlags StatusFlags.CF (adcR64R64Effect 0x114669 8 9))
      [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x114669 8 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x114669 0x4d 0xc8 c (by decide) (by decide))) pre_rip
  have f36 : InstrSpec 0x11466c [0x49, 0x0F, 0xA4, 0xF6, 0x0C] (fun s => s.RIP = 0x11466c) (shldR64R64Effect 0x11466c 5 14 6 12)
      [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x11466c 5 14 6 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x11466c 0x49 (by decide) 0xf6 (by decide) 0xc) pre_rip
  have f37 : InstrSpec 0x114671 [0x49, 0x0F, 0xA4, 0xC0, 0x0C] (fun s => s.RIP = 0x114671) (shldR64R64Effect 0x114671 5 8 0 12)
      [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x114671 5 8 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x114671 0x49 (by decide) 0xc0 (by decide) 0xc) pre_rip
  have f38 : InstrSpec 0x114676 [0x4C, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x114676 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x114676 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114676 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x114676 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x114676 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x11467b [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x11467b) (movR64R64Effect 0x11467b 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11467b 0 15).toInstrSpec (mov_r64_r64_effect_step 0x11467b 0x4c 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f20 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (9, 95), (10, 92), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11462c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f21 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 97), (6, 6), (7, 7), (8, 79), (9, 95), (10, 92), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114630) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 97), (6, 6), (7, 7), (8, 79), (9, 99), (10, 92), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114635) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f23 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 97), (6, 6), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114638) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 67), (2, 86), (3, 81), (4, 65), (5, 97), (6, 6), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11463b) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 107) (ρ' := [(0, 105), (1, 67), (2, 106), (3, 81), (4, 65), (5, 97), (6, 6), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11463e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f26 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 105), (1, 67), (2, 106), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114641) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 105), (1, 67), (2, 106), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 13), (14, 110), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114644) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 112), (1, 67), (2, 106), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 13), (14, 110), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11464e) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 114), (1, 67), (2, 106), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 13), (14, 110), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114651) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f30 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 114), (1, 67), (2, 106), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 110), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11465b) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 119) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 120) (ρ' := [(0, 118), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 79), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 110), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11465e) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f32 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 118), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 121), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 110), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114661) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 124) f33 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 125) (ρ' := [(0, 123), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 121), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 110), (15, 71), (16, 124), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114664) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 123), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 121), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 110), (15, 71), (16, 124), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114669) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f35 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 123), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 127), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 110), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11466c) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f36 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 123), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 127), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114671) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f37 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 123), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114676) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 123), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11467b) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 134), (1, 67), (2, 119), (3, 81), (4, 65), (5, 97), (6, 108), (7, 7), (8, 131), (9, 99), (10, 101), (11, 69), (12, 12), (13, 116), (14, 129), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11467e) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_2 code

theorem rest_l1145f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1145f0 bytes_l1145f0) (entryMap (live .l1145f0))
      198 0x1145f0 bytes_l1145f0 b_l1145f0 := by
  have f0 : InstrSpec 0x1145f0 [0x55] (PushPre 0x1145f0 1) (pushR64Effect 0x1145f0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1145f0 1 5).toInstrSpec (push_r64_effect_step 0x1145f0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1145f1 [0x41, 0x57] (PushPre 0x1145f1 2) (pushR64Effect 0x1145f1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1145f1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1145f1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1145f3 [0x41, 0x56] (PushPre 0x1145f3 2) (pushR64Effect 0x1145f3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1145f3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1145f3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1145f5 [0x41, 0x55] (PushPre 0x1145f5 2) (pushR64Effect 0x1145f5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1145f5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1145f5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1145f7 [0x41, 0x54] (PushPre 0x1145f7 2) (pushR64Effect 0x1145f7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1145f7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1145f7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1145f9 [0x53] (PushPre 0x1145f9 1) (pushR64Effect 0x1145f9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1145f9 1 3).toInstrSpec (push_r64_effect_step 0x1145f9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1145fa [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x1145fa) (subR64Imm8Effect 0x1145fa 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1145fa 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x1145fa 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1145fe [0x48, 0x8B, 0x0E] (LoadPre 0x1145fe (fun s => AddrMode.addr (.base 6 .none) s (0x1145fe + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1145fe 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1145fe 1 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1145fe 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x114601 [0x4C, 0x8B, 0x5E, 0x08] (LoadPre 0x114601 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x114601 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x114601 11 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x114601 11 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x114601 0x4c (by decide) 3 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x114605 [0x4C, 0x8B, 0x7E, 0x10] (LoadPre 0x114605 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x114605 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x114605 15 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x114605 15 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x114605 0x4c (by decide) 7 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x114609 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x114609 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x114609 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x114609 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x114609 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x114609 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11460d [0x48, 0x89, 0x04, 0x24] (StorePre 0x11460d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11460d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11460d 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11460d 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11460d 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x114611 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x114611) (mulR64Effect 0x114611 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x114611 1).toInstrSpec (mul_r64_effect_step 0x114611 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x114614 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x114614) (movR64R64Effect 0x114614 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x114614 8 2).toInstrSpec (mov_r64_r64_effect_step 0x114614 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x114617 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x114617) (movR64R64Effect 0x114617 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x114617 3 0).toInstrSpec (mov_r64_r64_effect_step 0x114617 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11461a [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x11461a) (movR64R64Effect 0x11461a 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11461a 0 15).toInstrSpec (mov_r64_r64_effect_step 0x11461a 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11461d [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x11461d) (mulR64Effect 0x11461d 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11461d 11).toInstrSpec (mul_r64_effect_step 0x11461d 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x114620 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x114620) (movR64R64Effect 0x114620 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x114620 9 2).toInstrSpec (mov_r64_r64_effect_step 0x114620 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x114623 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x114623) (movR64R64Effect 0x114623 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x114623 10 0).toInstrSpec (mov_r64_r64_effect_step 0x114623 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x114626 [0x49, 0x01, 0xDA] (fun s => s.RIP = 0x114626) (addR64R64Effect 0x114626 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114626 10 3).toInstrSpec (add_r64_r64_effect_step 0x114626 0x49 0xda (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145f7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145f9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145fa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1145fe) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114601) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (11, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114605) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114609) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11460d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114611) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 67), (2, 77), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114614) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 76), (1, 67), (2, 77), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114617) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 76), (1, 67), (2, 77), (3, 81), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11461a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 67), (2, 77), (3, 81), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11461d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114620) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (9, 88), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114623) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (9, 88), (10, 90), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114626) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 93) f19 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 94) (ρ' := [(0, 85), (1, 67), (2, 86), (3, 81), (4, 65), (5, 5), (6, 6), (7, 7), (8, 79), (9, 88), (10, 92), (11, 69), (12, 12), (13, 13), (14, 14), (15, 71), (16, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114629) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1145f0_1 code

theorem block_l1145f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1145f0 :=
  Rest.liftedBlock (rest_l1145f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1145f0 x hx)

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

theorem_by block_l1145f0_eval :
    program.runBlock (dialect code) ⟨.l1145f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Sec1.LIR
