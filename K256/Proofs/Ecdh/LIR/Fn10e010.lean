import K256.Proofs.Ecdh.LIR.Program

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l10e010_14 [Bindings] (code : CodeMap) :
    Rest (n := 643) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 579), (1, 594), (2, 628), (3, 637), (4, 641), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 640), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]
      5 0x10e4ac bytes_l10e010_14 b_l10e010_14 := by
  have f280 : InstrSpec 0x10e4ac [0x41, 0x5D] (PopPre 0x10e4ac) (popR64Effect 0x10e4ac 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10e4ac 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10e4ac 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f281 : InstrSpec 0x10e4ae [0x41, 0x5E] (PopPre 0x10e4ae) (popR64Effect 0x10e4ae 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10e4ae 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10e4ae 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f282 : InstrSpec 0x10e4b0 [0x41, 0x5F] (PopPre 0x10e4b0) (popR64Effect 0x10e4b0 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10e4b0 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10e4b0 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f283 : InstrSpec 0x10e4b2 [0x5D] (PopPre 0x10e4b2) (popR64Effect 0x10e4b2 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10e4b2 1 5).toInstrSpec (pop_r64_effect_step 0x10e4b2 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f284 : InstrSpec 0x10e4b3 [0xC3] (RetPre 0x10e4b3) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10e4b3).toInstrSpec (ret_effect_step 0x10e4b3) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 643) (RestInside.out (n := 643) f280 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 644) f280 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 645) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 637), (4, 644), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 640), (13, 643), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4ae) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 646) (RestInside.out (n := 646) f281 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 647) f281 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 648) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 637), (4, 647), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 640), (13, 643), (14, 646), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4b0) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 649) (RestInside.out (n := 649) f282 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 650) f282 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 651) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 637), (4, 650), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 640), (13, 643), (14, 646), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4b2) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 652) (RestInside.out (n := 652) f283 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 653) f283 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 654) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 637), (4, 653), (5, 652), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 640), (13, 643), (14, 646), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4b3) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 655) (RestInside.out (n := 655) f284 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 656) f284 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 657) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 637), (4, 656), (5, 652), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 640), (13, 643), (14, 646), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) f284 (by decide) rfl rfl rfl (by decide)

theorem rest_l10e010_13 [Bindings] (code : CodeMap) :
    Rest (n := 612) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 579), (1, 594), (2, 610), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]
      25 0x10e461 bytes_l10e010_13 b_l10e010_13 := by
  have f260 : InstrSpec 0x10e461 [0x48, 0x89, 0x50, 0x28] (StorePre 0x10e461 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x10e461 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e461 2 (.base 0 (.d8 0x28)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e461 2 (.base 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10e461 0x48 (by decide) 2 (.base 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f261 : InstrSpec 0x10e465 [0x48, 0x8B, 0x57, 0x70] (LoadPre 0x10e465 (fun s => AddrMode.addr (.base 7 (.d8 0x70)) s (0x10e465 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e465 2 (.base 7 (.d8 0x70)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e465 2 (.base 7 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10e465 0x48 (by decide) 2 (.base 7 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f262 : InstrSpec 0x10e469 [0x48, 0x89, 0x50, 0x70] (StorePre 0x10e469 4 (fun s => AddrMode.addr (.base 0 (.d8 0x70)) s (0x10e469 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e469 2 (.base 0 (.d8 0x70)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e469 2 (.base 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10e469 0x48 (by decide) 2 (.base 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f263 : InstrSpec 0x10e46d [0x48, 0x8B, 0x57, 0x68] (LoadPre 0x10e46d (fun s => AddrMode.addr (.base 7 (.d8 0x68)) s (0x10e46d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e46d 2 (.base 7 (.d8 0x68)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e46d 2 (.base 7 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10e46d 0x48 (by decide) 2 (.base 7 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f264 : InstrSpec 0x10e471 [0x48, 0x89, 0x50, 0x68] (StorePre 0x10e471 4 (fun s => AddrMode.addr (.base 0 (.d8 0x68)) s (0x10e471 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e471 2 (.base 0 (.d8 0x68)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e471 2 (.base 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x10e471 0x48 (by decide) 2 (.base 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f265 : InstrSpec 0x10e475 [0x48, 0x8B, 0x57, 0x60] (LoadPre 0x10e475 (fun s => AddrMode.addr (.base 7 (.d8 0x60)) s (0x10e475 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e475 2 (.base 7 (.d8 0x60)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e475 2 (.base 7 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10e475 0x48 (by decide) 2 (.base 7 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f266 : InstrSpec 0x10e479 [0x48, 0x89, 0x50, 0x60] (StorePre 0x10e479 4 (fun s => AddrMode.addr (.base 0 (.d8 0x60)) s (0x10e479 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e479 2 (.base 0 (.d8 0x60)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e479 2 (.base 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10e479 0x48 (by decide) 2 (.base 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f267 : InstrSpec 0x10e47d [0x48, 0x8B, 0x57, 0x58] (LoadPre 0x10e47d (fun s => AddrMode.addr (.base 7 (.d8 0x58)) s (0x10e47d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e47d 2 (.base 7 (.d8 0x58)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e47d 2 (.base 7 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10e47d 0x48 (by decide) 2 (.base 7 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f268 : InstrSpec 0x10e481 [0x48, 0x89, 0x50, 0x58] (StorePre 0x10e481 4 (fun s => AddrMode.addr (.base 0 (.d8 0x58)) s (0x10e481 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e481 2 (.base 0 (.d8 0x58)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e481 2 (.base 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10e481 0x48 (by decide) 2 (.base 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f269 : InstrSpec 0x10e485 [0x48, 0x8B, 0x57, 0x50] (LoadPre 0x10e485 (fun s => AddrMode.addr (.base 7 (.d8 0x50)) s (0x10e485 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e485 2 (.base 7 (.d8 0x50)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e485 2 (.base 7 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10e485 0x48 (by decide) 2 (.base 7 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f270 : InstrSpec 0x10e489 [0x48, 0x89, 0x50, 0x50] (StorePre 0x10e489 4 (fun s => AddrMode.addr (.base 0 (.d8 0x50)) s (0x10e489 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e489 2 (.base 0 (.d8 0x50)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e489 2 (.base 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10e489 0x48 (by decide) 2 (.base 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f271 : InstrSpec 0x10e48d [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x10e48d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e48d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e48d 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e48d 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10e48d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f272 : InstrSpec 0x10e492 [0x48, 0x89, 0x10] (StorePre 0x10e492 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10e492 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10e492 2 (.base 0 .none))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e492 2 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10e492 0x48 (by decide) 2 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f273 : InstrSpec 0x10e495 [0x4C, 0x89, 0x60, 0x08] (StorePre 0x10e495 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10e495 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e495 12 (.base 0 (.d8 0x8)))
      [.gpr 12, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e495 12 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10e495 0x4c (by decide) 4 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f274 : InstrSpec 0x10e499 [0x48, 0x89, 0x58, 0x10] (StorePre 0x10e499 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10e499 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e499 3 (.base 0 (.d8 0x10)))
      [.gpr 3, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e499 3 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10e499 0x48 (by decide) 3 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f275 : InstrSpec 0x10e49d [0x48, 0x89, 0x70, 0x18] (StorePre 0x10e49d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10e49d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e49d 6 (.base 0 (.d8 0x18)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e49d 6 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10e49d 0x48 (by decide) 6 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f276 : InstrSpec 0x10e4a1 [0x48, 0x89, 0x48, 0x20] (StorePre 0x10e4a1 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x10e4a1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e4a1 1 (.base 0 (.d8 0x20)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e4a1 1 (.base 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10e4a1 0x48 (by decide) 1 (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f277 : InstrSpec 0x10e4a5 [0x48, 0x83, 0xC4, 0x50] (fun s => s.RIP = 0x10e4a5) (addR64Imm8Effect 0x10e4a5 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10e4a5 4 0x50).toInstrSpec (add_r64_imm8_effect_step 0x10e4a5 0x48 0xc4 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f278 : InstrSpec 0x10e4a9 [0x5B] (PopPre 0x10e4a9) (popR64Effect 0x10e4a9 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10e4a9 1 3).toInstrSpec (pop_r64_effect_step 0x10e4a9 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f279 : InstrSpec 0x10e4aa [0x41, 0x5C] (PopPre 0x10e4aa) (popR64Effect 0x10e4aa 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10e4aa 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10e4aa 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 612) (RestInside.exec (n := 612) (ρ' := [(0, 579), (1, 594), (2, 610), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e465) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 613) (RestInside.out (n := 613) f261 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 614) (ρ' := [(0, 579), (1, 594), (2, 613), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e469) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 615) (RestInside.exec (n := 615) (ρ' := [(0, 579), (1, 594), (2, 613), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e46d) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 616) (RestInside.out (n := 616) f263 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 617) (ρ' := [(0, 579), (1, 594), (2, 616), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e471) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 618) (RestInside.exec (n := 618) (ρ' := [(0, 579), (1, 594), (2, 616), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e475) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 619) (RestInside.out (n := 619) f265 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 620) (ρ' := [(0, 579), (1, 594), (2, 619), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e479) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 621) (RestInside.exec (n := 621) (ρ' := [(0, 579), (1, 594), (2, 619), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e47d) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 622) (RestInside.out (n := 622) f267 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 623) (ρ' := [(0, 579), (1, 594), (2, 622), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e481) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 624) (RestInside.exec (n := 624) (ρ' := [(0, 579), (1, 594), (2, 622), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e485) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 625) (RestInside.out (n := 625) f269 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 626) (ρ' := [(0, 579), (1, 594), (2, 625), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e489) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 627) (RestInside.exec (n := 627) (ρ' := [(0, 579), (1, 594), (2, 625), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e48d) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 628) (RestInside.out (n := 628) f271 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 629) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e492) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 630) (RestInside.exec (n := 630) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e495) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 631) (RestInside.exec (n := 631) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e499) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 632) (RestInside.exec (n := 632) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e49d) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 633) (RestInside.exec (n := 633) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4a1) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 634) (RestInside.exec (n := 634) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4a5) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 635) (RestInside.out (n := 635) f277 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 636) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 563), (4, 635), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4a9) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 637) (RestInside.out (n := 637) f278 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 638) f278 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 639) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 637), (4, 638), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4aa) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 640) (RestInside.out (n := 640) f279 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 641) f279 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 642) (ρ' := [(0, 579), (1, 594), (2, 628), (3, 637), (4, 641), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 640), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4ac) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_14 code

theorem rest_l10e010_12 [Bindings] (code : CodeMap) :
    Rest (n := 574) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 567), (1, 572), (2, 568), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]
      45 0x10e40f bytes_l10e010_12 b_l10e010_12 := by
  have f240 : InstrSpec 0x10e40f [0x48, 0x01, 0xC1] (fun s => s.RIP = 0x10e40f) (addR64R64Effect 0x10e40f 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e40f 1 0).toInstrSpec (add_r64_r64_effect_step 0x10e40f 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f241 : InstrSpec 0x10e412 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x10e412) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e412 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e412 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e412 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f242 : InstrSpec 0x10e416 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x10e416) (movR64R64Effect 0x10e416 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e416 0 7).toInstrSpec (mov_r64_r64_effect_step 0x10e416 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f243 : InstrSpec 0x10e419 [0x4C, 0x01, 0xC9] (fun s => s.RIP = 0x10e419) (addR64R64Effect 0x10e419 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e419 1 9).toInstrSpec (add_r64_r64_effect_step 0x10e419 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f244 : InstrSpec 0x10e41c [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x10e41c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e41c 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e41c 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e41c 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f245 : InstrSpec 0x10e420 [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x10e420) (andR64R64Effect 0x10e420 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e420 6 1).toInstrSpec (and_r64_r64_effect_step 0x10e420 0x48 0xce (by decide) (by decide)) pre_rip
  have f246 : InstrSpec 0x10e423 [0x48, 0x0F, 0xA4, 0xCA, 0x0C] (fun s => s.RIP = 0x10e423) (shldR64R64Effect 0x10e423 5 2 1 12)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e423 5 2 1 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e423 0x48 (by decide) 0xca (by decide) 0xc) pre_rip
  have f247 : InstrSpec 0x10e428 [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x10e428) (movR64Imm64Effect 0x10e428 1 0xffffffffffff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e428 1 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10e428 0x48 0xb9 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f248 : InstrSpec 0x10e432 [0x4C, 0x21, 0xD1] (fun s => s.RIP = 0x10e432) (andR64R64Effect 0x10e432 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e432 1 10).toInstrSpec (and_r64_r64_effect_step 0x10e432 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f249 : InstrSpec 0x10e435 [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x10e435) (addR64R64Effect 0x10e435 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e435 1 2).toInstrSpec (add_r64_r64_effect_step 0x10e435 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f250 : InstrSpec 0x10e438 [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x10e438 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e438 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e438 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10e438 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10e438 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f251 : InstrSpec 0x10e43d [0x48, 0x8B, 0x57, 0x48] (LoadPre 0x10e43d (fun s => AddrMode.addr (.base 7 (.d8 0x48)) s (0x10e43d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e43d 2 (.base 7 (.d8 0x48)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e43d 2 (.base 7 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10e43d 0x48 (by decide) 2 (.base 7 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f252 : InstrSpec 0x10e441 [0x48, 0x89, 0x50, 0x48] (StorePre 0x10e441 4 (fun s => AddrMode.addr (.base 0 (.d8 0x48)) s (0x10e441 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e441 2 (.base 0 (.d8 0x48)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e441 2 (.base 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10e441 0x48 (by decide) 2 (.base 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f253 : InstrSpec 0x10e445 [0x48, 0x8B, 0x57, 0x40] (LoadPre 0x10e445 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x10e445 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e445 2 (.base 7 (.d8 0x40)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e445 2 (.base 7 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10e445 0x48 (by decide) 2 (.base 7 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f254 : InstrSpec 0x10e449 [0x48, 0x89, 0x50, 0x40] (StorePre 0x10e449 4 (fun s => AddrMode.addr (.base 0 (.d8 0x40)) s (0x10e449 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e449 2 (.base 0 (.d8 0x40)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e449 2 (.base 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10e449 0x48 (by decide) 2 (.base 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f255 : InstrSpec 0x10e44d [0x48, 0x8B, 0x57, 0x38] (LoadPre 0x10e44d (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x10e44d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e44d 2 (.base 7 (.d8 0x38)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e44d 2 (.base 7 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10e44d 0x48 (by decide) 2 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f256 : InstrSpec 0x10e451 [0x48, 0x89, 0x50, 0x38] (StorePre 0x10e451 4 (fun s => AddrMode.addr (.base 0 (.d8 0x38)) s (0x10e451 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e451 2 (.base 0 (.d8 0x38)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e451 2 (.base 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10e451 0x48 (by decide) 2 (.base 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f257 : InstrSpec 0x10e455 [0x48, 0x8B, 0x57, 0x30] (LoadPre 0x10e455 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10e455 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e455 2 (.base 7 (.d8 0x30)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e455 2 (.base 7 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10e455 0x48 (by decide) 2 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f258 : InstrSpec 0x10e459 [0x48, 0x89, 0x50, 0x30] (StorePre 0x10e459 4 (fun s => AddrMode.addr (.base 0 (.d8 0x30)) s (0x10e459 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e459 2 (.base 0 (.d8 0x30)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e459 2 (.base 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10e459 0x48 (by decide) 2 (.base 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f259 : InstrSpec 0x10e45d [0x48, 0x8B, 0x57, 0x28] (LoadPre 0x10e45d (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x10e45d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e45d 2 (.base 7 (.d8 0x28)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e45d 2 (.base 7 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10e45d 0x48 (by decide) 2 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 574) (RestInside.out (n := 574) f240 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 575) f240 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 576) (ρ' := [(0, 567), (1, 574), (2, 568), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (16, 575), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e412) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 577) (RestInside.out (n := 577) f241 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 578) (ρ' := [(0, 567), (1, 574), (2, 577), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e416) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 579) (RestInside.out (n := 579) f242 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 580) (ρ' := [(0, 579), (1, 574), (2, 577), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e419) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 581) (RestInside.out (n := 581) f243 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 582) f243 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 583) (ρ' := [(0, 579), (1, 581), (2, 577), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (16, 582), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e41c) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 584) (RestInside.out (n := 584) f244 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 585) (ρ' := [(0, 579), (1, 581), (2, 584), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e420) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 586) (RestInside.out (n := 586) f245 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 587) (ρ' := [(0, 579), (1, 581), (2, 584), (3, 563), (4, 65), (5, 495), (6, 586), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e423) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 588) (RestInside.out (n := 588) f246 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 589) (ρ' := [(0, 579), (1, 581), (2, 588), (3, 563), (4, 65), (5, 495), (6, 586), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e428) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 590) (RestInside.out (n := 590) f247 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 591) (ρ' := [(0, 579), (1, 590), (2, 588), (3, 563), (4, 65), (5, 495), (6, 586), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e432) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 592) (RestInside.out (n := 592) f248 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 593) (ρ' := [(0, 579), (1, 592), (2, 588), (3, 563), (4, 65), (5, 495), (6, 586), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e435) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 594) (RestInside.out (n := 594) f249 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 595) (ρ' := [(0, 579), (1, 594), (2, 588), (3, 563), (4, 65), (5, 495), (6, 586), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e438) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 596) (RestInside.out (n := 596) f250 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 597) (ρ' := [(0, 579), (1, 594), (2, 588), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e43d) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 598) (RestInside.out (n := 598) f251 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 599) (ρ' := [(0, 579), (1, 594), (2, 598), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e441) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 600) (RestInside.exec (n := 600) (ρ' := [(0, 579), (1, 594), (2, 598), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e445) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 601) (RestInside.out (n := 601) f253 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 602) (ρ' := [(0, 579), (1, 594), (2, 601), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e449) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 603) (RestInside.exec (n := 603) (ρ' := [(0, 579), (1, 594), (2, 601), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e44d) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 604) (RestInside.out (n := 604) f255 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 605) (ρ' := [(0, 579), (1, 594), (2, 604), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e451) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 606) (RestInside.exec (n := 606) (ρ' := [(0, 579), (1, 594), (2, 604), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e455) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 607) (RestInside.out (n := 607) f257 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 608) (ρ' := [(0, 579), (1, 594), (2, 607), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e459) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 609) (RestInside.exec (n := 609) (ρ' := [(0, 579), (1, 594), (2, 607), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e45d) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 610) (RestInside.out (n := 610) f259 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 611) (ρ' := [(0, 579), (1, 594), (2, 610), (3, 563), (4, 65), (5, 495), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e461) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_13 code

theorem rest_l10e010_11 [Bindings] (code : CodeMap) :
    Rest (n := 528) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 515), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 523), (12, 498), (13, 468), (14, 442), (15, 525), (16, 526), (22, 22), (39, 39), (50, 50), (51, 51)]
      65 0x10e3c0 bytes_l10e010_11 b_l10e010_11 := by
  have f220 : InstrSpec 0x10e3c0 [0x4D, 0x11, 0xC3] (fun s => s.RIP = 0x10e3c0) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3c0 11 8))
      [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e3c0 11 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e3c0 0x4d 0xc3 c (by decide) (by decide))) pre_rip
  have f221 : InstrSpec 0x10e3c3 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10e3c3) (movR64R64Effect 0x10e3c3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e3c3 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10e3c3 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f222 : InstrSpec 0x10e3c6 [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x10e3c6) (andR64R64Effect 0x10e3c6 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e3c6 0 6).toInstrSpec (and_r64_r64_effect_step 0x10e3c6 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f223 : InstrSpec 0x10e3c9 [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e3c9) (movR64Imm64Effect 0x10e3c9 1 0x1000003d10)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e3c9 1 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e3c9 0x48 0xb9 (by decide) (by decide) 0x1000003d10) pre_rip
  have f224 : InstrSpec 0x10e3d3 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e3d3) (mulR64Effect 0x10e3d3 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e3d3 1).toInstrSpec (mul_r64_effect_step 0x10e3d3 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f225 : InstrSpec 0x10e3d6 [0x48, 0x03, 0x1C, 0x24] (LoadPre 0x10e3d6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e3d6 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x10e3d6 3 (.sib 4 none 0 .none))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e3d6 3 (.sib 4 none 0 .none)).toInstrSpec (add_r64_m64_effect_step 0x10e3d6 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f226 : InstrSpec 0x10e3da [0x4C, 0x13, 0x4C, 0x24, 0x10] (LoadPre 0x10e3da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e3da + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e3da 9 (.sib 4 none 0 (.d8 0x10))))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e3da 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e3da 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f227 : InstrSpec 0x10e3df [0x48, 0x01, 0xEB] (fun s => s.RIP = 0x10e3df) (addR64R64Effect 0x10e3df 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e3df 3 5).toInstrSpec (add_r64_r64_effect_step 0x10e3df 0x48 0xeb (by decide) (by decide)) pre_rip
  have f228 : InstrSpec 0x10e3e2 [0x4C, 0x13, 0x4C, 0x24, 0x18] (LoadPre 0x10e3e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e3e2 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e3e2 9 (.sib 4 none 0 (.d8 0x18))))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e3e2 9 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e3e2 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f229 : InstrSpec 0x10e3e7 [0x48, 0x01, 0xC3] (fun s => s.RIP = 0x10e3e7) (addR64R64Effect 0x10e3e7 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e3e7 3 0).toInstrSpec (add_r64_r64_effect_step 0x10e3e7 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f230 : InstrSpec 0x10e3ea [0x49, 0x11, 0xD1] (fun s => s.RIP = 0x10e3ea) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3ea 9 2))
      [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e3ea 9 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e3ea 0x49 0xd1 c (by decide) (by decide))) pre_rip
  have f231 : InstrSpec 0x10e3ed [0x4C, 0x01, 0xEB] (fun s => s.RIP = 0x10e3ed) (addR64R64Effect 0x10e3ed 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e3ed 3 13).toInstrSpec (add_r64_r64_effect_step 0x10e3ed 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f232 : InstrSpec 0x10e3f0 [0x49, 0x83, 0xD1, 0x00] (fun s => s.RIP = 0x10e3f0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e3f0 9 0x0))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e3f0 9 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e3f0 0x49 0xd1 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f233 : InstrSpec 0x10e3f4 [0x4D, 0x0F, 0xA4, 0xFB, 0x0C] (fun s => s.RIP = 0x10e3f4) (shldR64R64Effect 0x10e3f4 5 11 15 12)
      [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e3f4 5 11 15 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e3f4 0x4d (by decide) 0xfb (by decide) 0xc) pre_rip
  have f234 : InstrSpec 0x10e3f9 [0x49, 0x0F, 0xA4, 0xD9, 0x0C] (fun s => s.RIP = 0x10e3f9) (shldR64R64Effect 0x10e3f9 5 9 3 12)
      [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e3f9 5 9 3 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e3f9 0x49 (by decide) 0xd9 (by decide) 0xc) pre_rip
  have f235 : InstrSpec 0x10e3fe [0x48, 0x21, 0xF3] (fun s => s.RIP = 0x10e3fe) (andR64R64Effect 0x10e3fe 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e3fe 3 6).toInstrSpec (and_r64_r64_effect_step 0x10e3fe 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f236 : InstrSpec 0x10e401 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x10e401) (movR64R64Effect 0x10e401 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e401 0 11).toInstrSpec (mov_r64_r64_effect_step 0x10e401 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f237 : InstrSpec 0x10e404 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e404) (mulR64Effect 0x10e404 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e404 1).toInstrSpec (mul_r64_effect_step 0x10e404 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f238 : InstrSpec 0x10e407 [0x48, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x10e407 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e407 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e407 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10e407 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10e407 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f239 : InstrSpec 0x10e40c [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x10e40c) (andR64R64Effect 0x10e40c 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e40c 1 6).toInstrSpec (and_r64_r64_effect_step 0x10e40c 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 528) (RestInside.out (n := 528) f220 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 529) (ρ' := [(0, 515), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3c3) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 530) (RestInside.out (n := 530) f221 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 531) (ρ' := [(0, 530), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3c6) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 532) (RestInside.out (n := 532) f222 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 533) (ρ' := [(0, 532), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3c9) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 534) (RestInside.out (n := 534) f223 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 535) (ρ' := [(0, 532), (1, 534), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3d3) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 536) (RestInside.out (n := 536) f224 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 537) f224 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 538) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3d6) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 539) (RestInside.out (n := 539) f225 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 540) f225 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 541) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 539), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (16, 540), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3da) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 542) (RestInside.out (n := 542) f226 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 543) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 539), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 542), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3df) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 544) (RestInside.out (n := 544) f227 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 545) f227 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 546) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 544), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 542), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (16, 545), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3e2) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 547) (RestInside.out (n := 547) f228 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 548) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 544), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 547), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3e7) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 549) (RestInside.out (n := 549) f229 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 550) f229 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 551) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 549), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 547), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (16, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3ea) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 552) (RestInside.out (n := 552) f230 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 553) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 549), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 552), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3ed) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 554) (RestInside.out (n := 554) f231 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 555) f231 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 556) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 554), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 552), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (16, 555), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3f0) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 557) (RestInside.out (n := 557) f232 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 558) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 554), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 557), (10, 257), (11, 528), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3f4) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 559) (RestInside.out (n := 559) f233 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 560) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 554), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 557), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3f9) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 561) (RestInside.out (n := 561) f234 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 562) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 554), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3fe) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 563) (RestInside.out (n := 563) f235 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 564) (ρ' := [(0, 536), (1, 534), (2, 537), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e401) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 565) (RestInside.out (n := 565) f236 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 566) (ρ' := [(0, 565), (1, 534), (2, 537), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e404) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 567) (RestInside.out (n := 567) f237 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 568) f237 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 569) (ρ' := [(0, 567), (1, 534), (2, 568), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e407) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 570) (RestInside.out (n := 570) f238 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 571) (ρ' := [(0, 567), (1, 570), (2, 568), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e40c) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 572) (RestInside.out (n := 572) f239 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 573) (ρ' := [(0, 567), (1, 572), (2, 568), (3, 563), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 561), (10, 257), (11, 559), (12, 498), (13, 468), (14, 442), (15, 525), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e40f) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_12 code

theorem rest_l10e010_10 [Bindings] (code : CodeMap) :
    Rest (n := 484) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 481), (1, 479), (2, 482), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]
      85 0x10e367 bytes_l10e010_10 b_l10e010_10 := by
  have f200 : InstrSpec 0x10e367 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10e367) (movR64R64Effect 0x10e367 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e367 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10e367 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f201 : InstrSpec 0x10e36a [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x10e36a) (movR64R64Effect 0x10e36a 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10e36a 3 0).toInstrSpec (mov_r64_r64_effect_step 0x10e36a 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f202 : InstrSpec 0x10e36d [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10e36d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e36d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e36d 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e36d 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10e36d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f203 : InstrSpec 0x10e372 [0x48, 0xB9, 0xEE, 0x01, 0x95, 0x71, 0x28, 0x6C, 0x09, 0x00] (fun s => s.RIP = 0x10e372) (movR64Imm64Effect 0x10e372 1 0x96c28719501ee)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e372 1 0x96c28719501ee).toInstrSpec (mov_r64_imm64_effect_step 0x10e372 0x48 0xb9 (by decide) (by decide) 0x96c28719501ee) pre_rip
  have f204 : InstrSpec 0x10e37c [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e37c) (mulR64Effect 0x10e37c 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e37c 1).toInstrSpec (mul_r64_effect_step 0x10e37c 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f205 : InstrSpec 0x10e37f [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x10e37f) (movR64R64Effect 0x10e37f 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10e37f 5 0).toInstrSpec (mov_r64_r64_effect_step 0x10e37f 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f206 : InstrSpec 0x10e382 [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x10e382 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e382 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e382 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e382 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10e382 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f207 : InstrSpec 0x10e387 [0x49, 0x21, 0xF4] (fun s => s.RIP = 0x10e387) (andR64R64Effect 0x10e387 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e387 12 6).toInstrSpec (and_r64_r64_effect_step 0x10e387 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f208 : InstrSpec 0x10e38a [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10e38a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e38a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e38a 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e38a 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10e38a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f209 : InstrSpec 0x10e38f [0x48, 0xB9, 0x7C, 0x65, 0x2B, 0x6A, 0xE9, 0x7A, 0x00, 0x00] (fun s => s.RIP = 0x10e38f) (movR64Imm64Effect 0x10e38f 1 0x7ae96a2b657c)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e38f 1 0x7ae96a2b657c).toInstrSpec (mov_r64_imm64_effect_step 0x10e38f 0x48 0xb9 (by decide) (by decide) 0x7ae96a2b657c) pre_rip
  have f210 : InstrSpec 0x10e399 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e399) (mulR64Effect 0x10e399 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e399 1).toInstrSpec (mul_r64_effect_step 0x10e399 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f211 : InstrSpec 0x10e39c [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x10e39c) (movR64R64Effect 0x10e39c 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e39c 11 2).toInstrSpec (mov_r64_r64_effect_step 0x10e39c 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f212 : InstrSpec 0x10e39f [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e39f) (movR64R64Effect 0x10e39f 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e39f 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e39f 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f213 : InstrSpec 0x10e3a2 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x10e3a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e3a2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e3a2 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e3a2 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10e3a2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f214 : InstrSpec 0x10e3a7 [0x48, 0xBA, 0xEA, 0x79, 0x44, 0xE6, 0x06, 0x71, 0x00, 0x00] (fun s => s.RIP = 0x10e3a7) (movR64Imm64Effect 0x10e3a7 2 0x7106e64479ea)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e3a7 2 0x7106e64479ea).toInstrSpec (mov_r64_imm64_effect_step 0x10e3a7 0x48 0xba (by decide) (by decide) 0x7106e64479ea) pre_rip
  have f215 : InstrSpec 0x10e3b1 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e3b1) (mulR64Effect 0x10e3b1 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e3b1 2).toInstrSpec (mul_r64_effect_step 0x10e3b1 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f216 : InstrSpec 0x10e3b4 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x10e3b4) (movR64R64Effect 0x10e3b4 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10e3b4 15 0).toInstrSpec (mov_r64_r64_effect_step 0x10e3b4 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f217 : InstrSpec 0x10e3b7 [0x49, 0x01, 0xCF] (fun s => s.RIP = 0x10e3b7) (addR64R64Effect 0x10e3b7 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e3b7 15 1).toInstrSpec (add_r64_r64_effect_step 0x10e3b7 0x49 0xcf (by decide) (by decide)) pre_rip
  have f218 : InstrSpec 0x10e3ba [0x49, 0x11, 0xD3] (fun s => s.RIP = 0x10e3ba) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3ba 11 2))
      [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e3ba 11 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e3ba 0x49 0xd3 c (by decide) (by decide))) pre_rip
  have f219 : InstrSpec 0x10e3bd [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x10e3bd) (addR64R64Effect 0x10e3bd 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e3bd 15 14).toInstrSpec (add_r64_r64_effect_step 0x10e3bd 0x4d 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 484) (RestInside.out (n := 484) f200 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 485) (ρ' := [(0, 481), (1, 479), (2, 482), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e36a) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 486) (RestInside.out (n := 486) f201 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 487) (ρ' := [(0, 481), (1, 479), (2, 482), (3, 486), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e36d) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 488) (RestInside.out (n := 488) f202 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 489) (ρ' := [(0, 488), (1, 479), (2, 482), (3, 486), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e372) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 490) (RestInside.out (n := 490) f203 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 491) (ρ' := [(0, 488), (1, 490), (2, 482), (3, 486), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e37c) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 492) (RestInside.out (n := 492) f204 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 493) f204 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 494) (ρ' := [(0, 492), (1, 490), (2, 493), (3, 486), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e37f) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 495) (RestInside.out (n := 495) f205 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 496) (ρ' := [(0, 492), (1, 490), (2, 493), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e382) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 497) (RestInside.exec (n := 497) (ρ' := [(0, 492), (1, 490), (2, 493), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e387) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 498) (RestInside.out (n := 498) f207 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 499) (ρ' := [(0, 492), (1, 490), (2, 493), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e38a) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 500) (RestInside.out (n := 500) f208 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 501) (ρ' := [(0, 500), (1, 490), (2, 493), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e38f) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 502) (RestInside.out (n := 502) f209 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 503) (ρ' := [(0, 500), (1, 502), (2, 493), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e399) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 504) (RestInside.out (n := 504) f210 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 505) f210 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 506) (ρ' := [(0, 504), (1, 502), (2, 505), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 367), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e39c) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 507) (RestInside.out (n := 507) f211 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 508) (ρ' := [(0, 504), (1, 502), (2, 505), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 507), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e39f) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 509) (RestInside.out (n := 509) f212 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 510) (ρ' := [(0, 504), (1, 509), (2, 505), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 507), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3a2) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 511) (RestInside.out (n := 511) f213 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 512) (ρ' := [(0, 511), (1, 509), (2, 505), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 507), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3a7) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 513) (RestInside.out (n := 513) f214 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 514) (ρ' := [(0, 511), (1, 509), (2, 513), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 507), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3b1) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 515) (RestInside.out (n := 515) f215 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 516) f215 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 517) (ρ' := [(0, 515), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 507), (12, 498), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3b4) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 518) (RestInside.out (n := 518) f216 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 519) (ρ' := [(0, 515), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 507), (12, 498), (13, 468), (14, 442), (15, 518), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3b7) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 520) (RestInside.out (n := 520) f217 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 521) f217 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 522) (ρ' := [(0, 515), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 507), (12, 498), (13, 468), (14, 442), (15, 520), (16, 521), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3ba) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 523) (RestInside.out (n := 523) f218 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 524) (ρ' := [(0, 515), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 523), (12, 498), (13, 468), (14, 442), (15, 520), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3bd) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 525) (RestInside.out (n := 525) f219 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 526) f219 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 527) (ρ' := [(0, 515), (1, 509), (2, 516), (3, 486), (4, 65), (5, 495), (6, 391), (7, 7), (8, 466), (9, 484), (10, 257), (11, 523), (12, 498), (13, 468), (14, 442), (15, 525), (16, 526), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e3c0) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_11 code

theorem rest_l10e010_9 [Bindings] (code : CodeMap) :
    Rest (n := 440) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 435), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]
      105 0x10e30e bytes_l10e010_9 b_l10e010_9 := by
  have f180 : InstrSpec 0x10e30e [0x4D, 0x89, 0xC6] (fun s => s.RIP = 0x10e30e) (movR64R64Effect 0x10e30e 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10e30e 14 8).toInstrSpec (mov_r64_r64_effect_step 0x10e30e 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x10e311 [0x49, 0x0F, 0xA4, 0xC6, 0x0C] (fun s => s.RIP = 0x10e311) (shldR64R64Effect 0x10e311 5 14 0 12)
      [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e311 5 14 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e311 0x49 (by decide) 0xc6 (by decide) 0xc) pre_rip
  have f182 : InstrSpec 0x10e316 [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x10e316) (andR64R64Effect 0x10e316 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e316 0 6).toInstrSpec (and_r64_r64_effect_step 0x10e316 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x10e319 [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e319) (movR64Imm64Effect 0x10e319 1 0x1000003d10)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e319 1 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e319 0x48 0xb9 (by decide) (by decide) 0x1000003d10) pre_rip
  have f184 : InstrSpec 0x10e323 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e323) (mulR64Effect 0x10e323 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e323 1).toInstrSpec (mul_r64_effect_step 0x10e323 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f185 : InstrSpec 0x10e326 [0x4C, 0x03, 0x64, 0x24, 0x38] (LoadPre 0x10e326 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e326 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e326 12 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 12, .gpr 4] [] [.reg 12, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e326 12 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (add_r64_m64_effect_step 0x10e326 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f186 : InstrSpec 0x10e32b [0x4C, 0x13, 0x2C, 0x24] (LoadPre 0x10e32b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e32b + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e32b 13 (.sib 4 none 0 .none)))
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e32b 13 (.sib 4 none 0 .none)).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e32b 0x4c (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f187 : InstrSpec 0x10e32f [0x49, 0x01, 0xC4] (fun s => s.RIP = 0x10e32f) (addR64R64Effect 0x10e32f 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e32f 12 0).toInstrSpec (add_r64_r64_effect_step 0x10e32f 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x10e332 [0x49, 0x11, 0xD5] (fun s => s.RIP = 0x10e332) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e332 13 2))
      [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e332 13 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e332 0x49 0xd5 c (by decide) (by decide))) pre_rip
  have f189 : InstrSpec 0x10e335 [0x4D, 0x01, 0xCC] (fun s => s.RIP = 0x10e335) (addR64R64Effect 0x10e335 12 9)
      [.gpr 12, .gpr 9] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e335 12 9).toInstrSpec (add_r64_r64_effect_step 0x10e335 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f190 : InstrSpec 0x10e338 [0x4D, 0x11, 0xDD] (fun s => s.RIP = 0x10e338) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e338 13 11))
      [.gpr 13, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e338 13 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e338 0x4d 0xdd c (by decide) (by decide))) pre_rip
  have f191 : InstrSpec 0x10e33b [0x49, 0xC1, 0xE8, 0x34] (fun s => s.RIP = 0x10e33b) (shrR64Effect 0x10e33b 4 8 52)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10e33b 4 8 52).toInstrSpec (shr_r64_imm8_effect_step 0x10e33b 0x49 0xe8 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f192 : InstrSpec 0x10e33f [0x4D, 0x0F, 0xA4, 0xE5, 0x0C] (fun s => s.RIP = 0x10e33f) (shldR64R64Effect 0x10e33f 5 13 12 12)
      [.gpr 13, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e33f 5 13 12 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e33f 0x4d (by decide) 0xe5 (by decide) 0xc) pre_rip
  have f193 : InstrSpec 0x10e344 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10e344 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e344 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e344 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e344 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10e344 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f194 : InstrSpec 0x10e349 [0x48, 0xF7, 0xE3] (fun s => s.RIP = 0x10e349) (mulR64Effect 0x10e349 3)
      [.gpr 3, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e349 3).toInstrSpec (mul_r64_effect_step 0x10e349 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f195 : InstrSpec 0x10e34c [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x10e34c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e34c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e34c 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e34c 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10e34c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f196 : InstrSpec 0x10e351 [0x48, 0x89, 0x04, 0x24] (StorePre 0x10e351 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e351 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e351 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e351 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10e351 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f197 : InstrSpec 0x10e355 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10e355 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e355 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e355 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e355 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10e355 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f198 : InstrSpec 0x10e35a [0x48, 0xB9, 0x13, 0x5C, 0x99, 0x58, 0x2F, 0x51, 0x07, 0x00] (fun s => s.RIP = 0x10e35a) (movR64Imm64Effect 0x10e35a 1 0x7512f58995c13)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e35a 1 0x7512f58995c13).toInstrSpec (mov_r64_imm64_effect_step 0x10e35a 0x48 0xb9 (by decide) (by decide) 0x7512f58995c13) pre_rip
  have f199 : InstrSpec 0x10e364 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e364) (mulR64Effect 0x10e364 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e364 1).toInstrSpec (mul_r64_effect_step 0x10e364 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f180 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 441) (ρ' := [(0, 435), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 440), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e311) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.out (n := 442) f181 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 443) (ρ' := [(0, 435), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e316) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 444) (RestInside.out (n := 444) f182 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 445) (ρ' := [(0, 444), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e319) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 446) (RestInside.out (n := 446) f183 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 447) (ρ' := [(0, 444), (1, 446), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e323) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.out (n := 448) f184 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 449) f184 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 450) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e326) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 451) (RestInside.out (n := 451) f185 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 452) f185 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 453) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 451), (13, 389), (14, 442), (15, 425), (16, 452), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e32b) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.out (n := 454) f186 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 455) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 451), (13, 454), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e32f) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 456) (RestInside.out (n := 456) f187 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 457) f187 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 458) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 456), (13, 454), (14, 442), (15, 425), (16, 457), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e332) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 459) (RestInside.out (n := 459) f188 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 460) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 456), (13, 459), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e335) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 461) (RestInside.out (n := 461) f189 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 462) f189 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 463) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 461), (13, 459), (14, 442), (15, 425), (16, 462), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e338) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 464) (RestInside.out (n := 464) f190 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 465) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 461), (13, 464), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e33b) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.out (n := 466) f191 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 467) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 464), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e33f) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 468) (RestInside.out (n := 468) f192 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 469) (ρ' := [(0, 448), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e344) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 470) (RestInside.out (n := 470) f193 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 471) (ρ' := [(0, 470), (1, 446), (2, 449), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e349) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 472) (RestInside.out (n := 472) f194 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 473) f194 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 474) (ρ' := [(0, 472), (1, 446), (2, 473), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e34c) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 475) (RestInside.exec (n := 475) (ρ' := [(0, 472), (1, 446), (2, 473), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e351) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 476) (RestInside.exec (n := 476) (ρ' := [(0, 472), (1, 446), (2, 473), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e355) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 477) (RestInside.out (n := 477) f197 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 478) (ρ' := [(0, 477), (1, 446), (2, 473), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e35a) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 479) (RestInside.out (n := 479) f198 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 480) (ρ' := [(0, 477), (1, 479), (2, 473), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e364) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 481) (RestInside.out (n := 481) f199 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 482) f199 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 483) (ρ' := [(0, 481), (1, 479), (2, 482), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 466), (9, 369), (10, 257), (11, 367), (12, 461), (13, 468), (14, 442), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e367) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_10 code

theorem rest_l10e010_8 [Bindings] (code : CodeMap) :
    Rest (n := 395) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 384), (1, 393), (2, 385), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]
      125 0x10e2b6 bytes_l10e010_8 b_l10e010_8 := by
  have f160 : InstrSpec 0x10e2b6 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x10e2b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e2b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e2b6 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e2b6 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10e2b6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f161 : InstrSpec 0x10e2bb [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10e2bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e2bb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e2bb 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e2bb 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10e2bb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f162 : InstrSpec 0x10e2c0 [0x48, 0xB9, 0x7C, 0x65, 0x2B, 0x6A, 0xE9, 0x7A, 0x00, 0x00] (fun s => s.RIP = 0x10e2c0) (movR64Imm64Effect 0x10e2c0 1 0x7ae96a2b657c)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e2c0 1 0x7ae96a2b657c).toInstrSpec (mov_r64_imm64_effect_step 0x10e2c0 0x48 0xb9 (by decide) (by decide) 0x7ae96a2b657c) pre_rip
  have f163 : InstrSpec 0x10e2ca [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e2ca) (mulR64Effect 0x10e2ca 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e2ca 1).toInstrSpec (mul_r64_effect_step 0x10e2ca 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f164 : InstrSpec 0x10e2cd [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10e2cd) (movR64R64Effect 0x10e2cd 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e2cd 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10e2cd 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x10e2d0 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x10e2d0) (movR64R64Effect 0x10e2d0 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10e2d0 14 0).toInstrSpec (mov_r64_r64_effect_step 0x10e2d0 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f166 : InstrSpec 0x10e2d3 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x10e2d3) (movR64R64Effect 0x10e2d3 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e2d3 0 8).toInstrSpec (mov_r64_r64_effect_step 0x10e2d3 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x10e2d6 [0x48, 0xBA, 0xEA, 0x79, 0x44, 0xE6, 0x06, 0x71, 0x00, 0x00] (fun s => s.RIP = 0x10e2d6) (movR64Imm64Effect 0x10e2d6 2 0x7106e64479ea)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e2d6 2 0x7106e64479ea).toInstrSpec (mov_r64_imm64_effect_step 0x10e2d6 0x48 0xba (by decide) (by decide) 0x7106e64479ea) pre_rip
  have f168 : InstrSpec 0x10e2e0 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e2e0) (mulR64Effect 0x10e2e0 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e2e0 2).toInstrSpec (mul_r64_effect_step 0x10e2e0 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f169 : InstrSpec 0x10e2e3 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10e2e3) (movR64R64Effect 0x10e2e3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10e2e3 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10e2e3 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x10e2e6 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x10e2e6) (movR64R64Effect 0x10e2e6 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10e2e6 15 0).toInstrSpec (mov_r64_r64_effect_step 0x10e2e6 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x10e2e9 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x10e2e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e2e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e2e9 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e2e9 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10e2e9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f172 : InstrSpec 0x10e2ee [0x48, 0xBB, 0x49, 0xF0, 0x9C, 0xE9, 0x34, 0x34, 0x0C, 0x00] (fun s => s.RIP = 0x10e2ee) (movR64Imm64Effect 0x10e2ee 3 0xc3434e99cf049)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x10e2ee 3 0xc3434e99cf049).toInstrSpec (mov_r64_imm64_effect_step 0x10e2ee 0x48 0xbb (by decide) (by decide) 0xc3434e99cf049) pre_rip
  have f173 : InstrSpec 0x10e2f8 [0x48, 0xF7, 0xE3] (fun s => s.RIP = 0x10e2f8) (mulR64Effect 0x10e2f8 3)
      [.gpr 3, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e2f8 3).toInstrSpec (mul_r64_effect_step 0x10e2f8 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f174 : InstrSpec 0x10e2fb [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x10e2fb) (addR64R64Effect 0x10e2fb 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e2fb 15 14).toInstrSpec (add_r64_r64_effect_step 0x10e2fb 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x10e2fe [0x49, 0x11, 0xC8] (fun s => s.RIP = 0x10e2fe) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e2fe 8 1))
      [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e2fe 8 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e2fe 0x49 0xc8 c (by decide) (by decide))) pre_rip
  have f176 : InstrSpec 0x10e301 [0x4C, 0x01, 0xF8] (fun s => s.RIP = 0x10e301) (addR64R64Effect 0x10e301 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e301 0 15).toInstrSpec (add_r64_r64_effect_step 0x10e301 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x10e304 [0x49, 0x11, 0xD0] (fun s => s.RIP = 0x10e304) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e304 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e304 8 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e304 0x49 0xd0 c (by decide) (by decide))) pre_rip
  have f178 : InstrSpec 0x10e307 [0x48, 0x01, 0xE8] (fun s => s.RIP = 0x10e307) (addR64R64Effect 0x10e307 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e307 0 5).toInstrSpec (add_r64_r64_effect_step 0x10e307 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f179 : InstrSpec 0x10e30a [0x49, 0x83, 0xD0, 0x00] (fun s => s.RIP = 0x10e30a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e30a 8 0x0))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e30a 8 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e30a 0x49 0xd0 0x0 c (by decide) (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 395) (RestInside.exec (n := 395) (ρ' := [(0, 384), (1, 393), (2, 385), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2bb) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 396) (RestInside.out (n := 396) f161 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 397) (ρ' := [(0, 396), (1, 393), (2, 385), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2c0) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f162 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 396), (1, 398), (2, 385), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2ca) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.out (n := 400) f163 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 401) f163 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 402) (ρ' := [(0, 400), (1, 398), (2, 401), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2cd) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.out (n := 403) f164 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 404) (ρ' := [(0, 400), (1, 403), (2, 401), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2d0) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 405) (RestInside.out (n := 405) f165 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 406) (ρ' := [(0, 400), (1, 403), (2, 401), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2d3) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 407) (RestInside.out (n := 407) f166 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 408) (ρ' := [(0, 407), (1, 403), (2, 401), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2d6) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 409) (RestInside.out (n := 409) f167 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 410) (ρ' := [(0, 407), (1, 403), (2, 409), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2e0) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 411) (RestInside.out (n := 411) f168 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 412) f168 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 413) (ρ' := [(0, 411), (1, 403), (2, 412), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2e3) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.out (n := 414) f169 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 415) (ρ' := [(0, 411), (1, 403), (2, 412), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 414), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2e6) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f170 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 411), (1, 403), (2, 412), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 414), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 416), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2e9) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.out (n := 418) f171 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 419) (ρ' := [(0, 418), (1, 403), (2, 412), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 414), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 416), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2ee) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 420) (RestInside.out (n := 420) f172 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 421) (ρ' := [(0, 418), (1, 403), (2, 412), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 414), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 416), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2f8) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 422) (RestInside.out (n := 422) f173 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 423) f173 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 424) (ρ' := [(0, 422), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 414), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 416), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2fb) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f174 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 426) f174 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 427) (ρ' := [(0, 422), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 414), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 425), (16, 426), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2fe) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f175 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 422), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 428), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e301) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.out (n := 430) f176 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 431) f176 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 432) (ρ' := [(0, 430), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 428), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 425), (16, 431), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e304) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 433) (RestInside.out (n := 433) f177 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 434) (ρ' := [(0, 430), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 433), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e307) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 435) (RestInside.out (n := 435) f178 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 436) f178 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 437) (ρ' := [(0, 435), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 433), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 425), (16, 436), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e30a) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 438) (RestInside.out (n := 438) f179 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 439) (ρ' := [(0, 435), (1, 403), (2, 423), (3, 420), (4, 65), (5, 343), (6, 391), (7, 7), (8, 438), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 405), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e30e) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_9 code

theorem rest_l10e010_7 [Bindings] (code : CodeMap) :
    Rest (n := 353) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 351), (1, 347), (2, 319), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]
      145 0x10e25a bytes_l10e010_7 b_l10e010_7 := by
  have f140 : InstrSpec 0x10e25a [0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e25a) (movR64Imm64Effect 0x10e25a 1 0x1000003d1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e25a 1 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x10e25a 0x48 0xb9 (by decide) (by decide) 0x1000003d1) pre_rip
  have f141 : InstrSpec 0x10e264 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e264) (mulR64Effect 0x10e264 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e264 1).toInstrSpec (mul_r64_effect_step 0x10e264 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x10e267 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10e267) (movR64R64Effect 0x10e267 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e267 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10e267 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x10e26a [0x48, 0x03, 0x04, 0x24] (LoadPre 0x10e26a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e26a + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x10e26a 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e26a 0 (.sib 4 none 0 .none)).toInstrSpec (add_r64_m64_effect_step 0x10e26a 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f144 : InstrSpec 0x10e26e [0x4C, 0x13, 0x4C, 0x24, 0x08] (LoadPre 0x10e26e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e26e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e26e 9 (.sib 4 none 0 (.d8 0x8))))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e26e 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e26e 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f145 : InstrSpec 0x10e273 [0x4D, 0x89, 0xCB] (fun s => s.RIP = 0x10e273) (movR64R64Effect 0x10e273 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e273 11 9).toInstrSpec (mov_r64_r64_effect_step 0x10e273 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f146 : InstrSpec 0x10e276 [0x49, 0xC1, 0xEB, 0x34] (fun s => s.RIP = 0x10e276) (shrR64Effect 0x10e276 4 11 52)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64Effect_footprint 0x10e276 4 11 52).toInstrSpec (shr_r64_imm8_effect_step 0x10e276 0x49 0xeb 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f147 : InstrSpec 0x10e27a [0x49, 0x0F, 0xA4, 0xC1, 0x0C] (fun s => s.RIP = 0x10e27a) (shldR64R64Effect 0x10e27a 5 9 0 12)
      [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e27a 5 9 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e27a 0x49 (by decide) 0xc1 (by decide) 0xc) pre_rip
  have f148 : InstrSpec 0x10e27f [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e27f) (movR64R64Effect 0x10e27f 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e27f 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e27f 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x10e282 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10e282 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e282 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e282 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e282 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10e282 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f150 : InstrSpec 0x10e287 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x10e287) (mulR64Effect 0x10e287 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e287 12).toInstrSpec (mul_r64_effect_step 0x10e287 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x10e28a [0x48, 0x89, 0x14, 0x24] (StorePre 0x10e28a 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e28a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e28a 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e28a 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10e28a 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f152 : InstrSpec 0x10e28e [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x10e28e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e28e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e28e 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e28e 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10e28e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f153 : InstrSpec 0x10e293 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e293) (movR64R64Effect 0x10e293 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e293 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e293 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x10e296 [0x48, 0xBA, 0xEE, 0x01, 0x95, 0x71, 0x28, 0x6C, 0x09, 0x00] (fun s => s.RIP = 0x10e296) (movR64Imm64Effect 0x10e296 2 0x96c28719501ee)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e296 2 0x96c28719501ee).toInstrSpec (mov_r64_imm64_effect_step 0x10e296 0x48 0xba (by decide) (by decide) 0x96c28719501ee) pre_rip
  have f155 : InstrSpec 0x10e2a0 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e2a0) (mulR64Effect 0x10e2a0 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e2a0 2).toInstrSpec (mul_r64_effect_step 0x10e2a0 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x10e2a3 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x10e2a3) (movR64R64Effect 0x10e2a3 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10e2a3 12 0).toInstrSpec (mov_r64_r64_effect_step 0x10e2a3 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x10e2a6 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x10e2a6) (movR64R64Effect 0x10e2a6 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10e2a6 13 2).toInstrSpec (mov_r64_r64_effect_step 0x10e2a6 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x10e2a9 [0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10e2a9) (movR64Imm64Effect 0x10e2a9 6 0xfffffffffffff)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10e2a9 6 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10e2a9 0x48 0xbe (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f159 : InstrSpec 0x10e2b3 [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x10e2b3) (andR64R64Effect 0x10e2b3 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e2b3 1 6).toInstrSpec (and_r64_r64_effect_step 0x10e2b3 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f140 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 351), (1, 353), (2, 319), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e264) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f141 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 356) f141 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 357) (ρ' := [(0, 355), (1, 353), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e267) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 358) (RestInside.out (n := 358) f142 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 359) (ρ' := [(0, 355), (1, 353), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 358), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e26a) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 360) (RestInside.out (n := 360) f143 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 361) f143 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 362) (ρ' := [(0, 360), (1, 353), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 358), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (16, 361), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e26e) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f144 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 364) (ρ' := [(0, 360), (1, 353), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 363), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e273) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f145 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 360), (1, 353), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 363), (10, 257), (11, 365), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e276) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f146 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 360), (1, 353), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 363), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e27a) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f147 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 370) (ρ' := [(0, 360), (1, 353), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e27f) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f148 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 360), (1, 371), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e282) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f149 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 373), (1, 371), (2, 356), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e287) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f150 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 376) f150 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 377) (ρ' := [(0, 375), (1, 371), (2, 376), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e28a) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.exec (n := 378) (ρ' := [(0, 375), (1, 371), (2, 376), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e28e) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 379) (RestInside.exec (n := 379) (ρ' := [(0, 375), (1, 371), (2, 376), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e293) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f153 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 380), (1, 371), (2, 376), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e296) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f154 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 380), (1, 371), (2, 382), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2a0) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.out (n := 384) f155 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 385) f155 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 386) (ρ' := [(0, 384), (1, 371), (2, 385), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2a3) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 387) (RestInside.out (n := 387) f156 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 388) (ρ' := [(0, 384), (1, 371), (2, 385), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2a6) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f157 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 384), (1, 371), (2, 385), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2a9) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f158 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 384), (1, 371), (2, 385), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2b3) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 393) (RestInside.out (n := 393) f159 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 394) (ρ' := [(0, 384), (1, 393), (2, 385), (3, 310), (4, 65), (5, 343), (6, 391), (7, 7), (8, 301), (9, 369), (10, 257), (11, 367), (12, 387), (13, 389), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e2b6) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_8 code

theorem rest_l10e010_6 [Bindings] (code : CodeMap) :
    Rest (n := 307) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 303), (1, 282), (2, 305), (3, 198), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]
      165 0x10e20c bytes_l10e010_6 b_l10e010_6 := by
  have f120 : InstrSpec 0x10e20c [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e20c) (mulR64Effect 0x10e20c 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e20c 2).toInstrSpec (mul_r64_effect_step 0x10e20c 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x10e20f [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x10e20f) (movR64R64Effect 0x10e20f 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10e20f 3 2).toInstrSpec (mov_r64_r64_effect_step 0x10e20f 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x10e212 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x10e212) (movR64R64Effect 0x10e212 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10e212 14 0).toInstrSpec (mov_r64_r64_effect_step 0x10e212 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x10e215 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x10e215) (movR64R64Effect 0x10e215 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e215 0 12).toInstrSpec (mov_r64_r64_effect_step 0x10e215 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x10e218 [0x49, 0xBC, 0x13, 0x5C, 0x99, 0x58, 0x2F, 0x51, 0x07, 0x00] (fun s => s.RIP = 0x10e218) (movR64Imm64Effect 0x10e218 12 0x7512f58995c13)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x10e218 12 0x7512f58995c13).toInstrSpec (mov_r64_imm64_effect_step 0x10e218 0x49 0xbc (by decide) (by decide) 0x7512f58995c13) pre_rip
  have f125 : InstrSpec 0x10e222 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x10e222) (mulR64Effect 0x10e222 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e222 12).toInstrSpec (mul_r64_effect_step 0x10e222 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x10e225 [0x83, 0xE6, 0x0F] (fun s => s.RIP = 0x10e225) (andR32Imm8Effect 0x10e225 3 6 0xf)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x10e225 3 6 0xf).toInstrSpec (and_r32_imm8_effect_step 0x10e225 0xe6 0xf (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x10e228 [0x49, 0x01, 0xCB] (fun s => s.RIP = 0x10e228) (addR64R64Effect 0x10e228 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e228 11 1).toInstrSpec (add_r64_r64_effect_step 0x10e228 0x49 0xcb (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x10e22b [0x4C, 0x11, 0xCD] (fun s => s.RIP = 0x10e22b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e22b 5 9))
      [.gpr 5, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e22b 5 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e22b 0x4c 0xcd c (by decide) (by decide))) pre_rip
  have f129 : InstrSpec 0x10e22e [0x4D, 0x01, 0xF3] (fun s => s.RIP = 0x10e22e) (addR64R64Effect 0x10e22e 11 14)
      [.gpr 11, .gpr 14] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e22e 11 14).toInstrSpec (add_r64_r64_effect_step 0x10e22e 0x4d 0xf3 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x10e231 [0x48, 0x11, 0xDD] (fun s => s.RIP = 0x10e231) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e231 5 3))
      [.gpr 5, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e231 5 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e231 0x48 0xdd c (by decide) (by decide))) pre_rip
  have f131 : InstrSpec 0x10e234 [0x4C, 0x01, 0xD8] (fun s => s.RIP = 0x10e234) (addR64R64Effect 0x10e234 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e234 0 11).toInstrSpec (add_r64_r64_effect_step 0x10e234 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x10e237 [0x48, 0x11, 0xD5] (fun s => s.RIP = 0x10e237) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e237 5 2))
      [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e237 5 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e237 0x48 0xd5 c (by decide) (by decide))) pre_rip
  have f133 : InstrSpec 0x10e23a [0x4C, 0x01, 0xF8] (fun s => s.RIP = 0x10e23a) (addR64R64Effect 0x10e23a 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e23a 0 15).toInstrSpec (add_r64_r64_effect_step 0x10e23a 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x10e23d [0x48, 0x83, 0xD5, 0x00] (fun s => s.RIP = 0x10e23d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e23d 5 0x0))
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e23d 5 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e23d 0x48 0xd5 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f135 : InstrSpec 0x10e241 [0x48, 0x0F, 0xA4, 0xC5, 0x0C] (fun s => s.RIP = 0x10e241) (shldR64R64Effect 0x10e241 5 5 0 12)
      [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e241 5 5 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e241 0x48 (by decide) 0xc5 (by decide) 0xc) pre_rip
  have f136 : InstrSpec 0x10e246 [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x10e246) (shlR64Effect 0x10e246 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10e246 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x10e246 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x10e24a [0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00] (fun s => s.RIP = 0x10e24a) (movR64Imm64Effect 0x10e24a 1 0xfffffffffffff0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e24a 1 0xfffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x10e24a 0x48 0xb9 (by decide) (by decide) 0xfffffffffffff0) pre_rip
  have f138 : InstrSpec 0x10e254 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10e254) (andR64R64Effect 0x10e254 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e254 0 1).toInstrSpec (and_r64_r64_effect_step 0x10e254 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x10e257 [0x48, 0x09, 0xF0] (fun s => s.RIP = 0x10e257) (orR64R64Effect 0x10e257 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10e257 0 6).toInstrSpec (or_r64_r64_effect_step 0x10e257 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f120 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 308) f120 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 309) (ρ' := [(0, 307), (1, 282), (2, 308), (3, 198), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e20f) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f121 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 307), (1, 282), (2, 308), (3, 310), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e212) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f122 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 307), (1, 282), (2, 308), (3, 310), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e215) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 314), (1, 282), (2, 308), (3, 310), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e218) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f124 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 314), (1, 282), (2, 308), (3, 310), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e222) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f125 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 319) f125 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 320) (ρ' := [(0, 318), (1, 282), (2, 319), (3, 310), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e225) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 321) (RestInside.out (n := 321) f126 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 322) (ρ' := [(0, 318), (1, 282), (2, 319), (3, 310), (4, 65), (5, 297), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e228) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f127 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 324) f127 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 325) (ρ' := [(0, 318), (1, 282), (2, 319), (3, 310), (4, 65), (5, 297), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 323), (12, 316), (13, 273), (14, 312), (15, 262), (16, 324), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e22b) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f128 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 318), (1, 282), (2, 319), (3, 310), (4, 65), (5, 326), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 323), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e22e) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f129 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 329) f129 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 330) (ρ' := [(0, 318), (1, 282), (2, 319), (3, 310), (4, 65), (5, 326), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (16, 329), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e231) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 331) (RestInside.out (n := 331) f130 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 332) (ρ' := [(0, 318), (1, 282), (2, 319), (3, 310), (4, 65), (5, 331), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e234) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 333) (RestInside.out (n := 333) f131 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 334) f131 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 335) (ρ' := [(0, 333), (1, 282), (2, 319), (3, 310), (4, 65), (5, 331), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (16, 334), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e237) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f132 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 333), (1, 282), (2, 319), (3, 310), (4, 65), (5, 336), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e23a) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f133 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 339) f133 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 340) (ρ' := [(0, 338), (1, 282), (2, 319), (3, 310), (4, 65), (5, 336), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (16, 339), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e23d) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f134 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 338), (1, 282), (2, 319), (3, 310), (4, 65), (5, 341), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e241) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f135 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 338), (1, 282), (2, 319), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e246) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f136 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 346) (ρ' := [(0, 345), (1, 282), (2, 319), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e24a) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f137 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 345), (1, 347), (2, 319), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e254) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f138 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 349), (1, 347), (2, 319), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e257) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f139 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 351), (1, 347), (2, 319), (3, 310), (4, 65), (5, 343), (6, 321), (7, 7), (8, 301), (9, 284), (10, 257), (11, 328), (12, 316), (13, 273), (14, 312), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e25a) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_7 code

theorem rest_l10e010_5 [Bindings] (code : CodeMap) :
    Rest (n := 266) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 264), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]
      185 0x10e1aa bytes_l10e010_5 b_l10e010_5 := by
  have f100 : InstrSpec 0x10e1aa [0x48, 0xB9, 0xEE, 0x01, 0x95, 0x71, 0x28, 0x6C, 0x09, 0x00] (fun s => s.RIP = 0x10e1aa) (movR64Imm64Effect 0x10e1aa 1 0x96c28719501ee)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e1aa 1 0x96c28719501ee).toInstrSpec (mov_r64_imm64_effect_step 0x10e1aa 0x48 0xb9 (by decide) (by decide) 0x96c28719501ee) pre_rip
  have f101 : InstrSpec 0x10e1b4 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e1b4) (mulR64Effect 0x10e1b4 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e1b4 1).toInstrSpec (mul_r64_effect_step 0x10e1b4 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x10e1b7 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x10e1b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e1b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e1b7 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e1b7 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10e1b7 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f103 : InstrSpec 0x10e1bc [0x48, 0x89, 0x04, 0x24] (StorePre 0x10e1bc 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e1bc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e1bc 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e1bc 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10e1bc 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f104 : InstrSpec 0x10e1c0 [0x4C, 0x8B, 0x6C, 0x24, 0x28] (LoadPre 0x10e1c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e1c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e1c0 13 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10e1c0 13 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10e1c0 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f105 : InstrSpec 0x10e1c5 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e1c5) (movR64R64Effect 0x10e1c5 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e1c5 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e1c5 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x10e1c8 [0x48, 0xB9, 0x7C, 0x65, 0x2B, 0x6A, 0xE9, 0x7A, 0x00, 0x00] (fun s => s.RIP = 0x10e1c8) (movR64Imm64Effect 0x10e1c8 1 0x7ae96a2b657c)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e1c8 1 0x7ae96a2b657c).toInstrSpec (mov_r64_imm64_effect_step 0x10e1c8 0x48 0xb9 (by decide) (by decide) 0x7ae96a2b657c) pre_rip
  have f107 : InstrSpec 0x10e1d2 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e1d2) (mulR64Effect 0x10e1d2 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e1d2 1).toInstrSpec (mul_r64_effect_step 0x10e1d2 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x10e1d5 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e1d5) (movR64R64Effect 0x10e1d5 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e1d5 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e1d5 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x10e1d8 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10e1d8) (movR64R64Effect 0x10e1d8 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e1d8 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10e1d8 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x10e1db [0x4C, 0x89, 0xD6] (fun s => s.RIP = 0x10e1db) (movR64R64Effect 0x10e1db 6 10)
      [.gpr 10] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10e1db 6 10).toInstrSpec (mov_r64_r64_effect_step 0x10e1db 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x10e1de [0x48, 0xC1, 0xEE, 0x30] (fun s => s.RIP = 0x10e1de) (shrR64Effect 0x10e1de 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10e1de 4 6 48).toInstrSpec (shr_r64_imm8_effect_step 0x10e1de 0x48 0xee 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x10e1e2 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10e1e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e1e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e1e2 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e1e2 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10e1e2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f113 : InstrSpec 0x10e1e7 [0x48, 0xBA, 0xEA, 0x79, 0x44, 0xE6, 0x06, 0x71, 0x00, 0x00] (fun s => s.RIP = 0x10e1e7) (movR64Imm64Effect 0x10e1e7 2 0x7106e64479ea)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e1e7 2 0x7106e64479ea).toInstrSpec (mov_r64_imm64_effect_step 0x10e1e7 0x48 0xba (by decide) (by decide) 0x7106e64479ea) pre_rip
  have f114 : InstrSpec 0x10e1f1 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e1f1) (mulR64Effect 0x10e1f1 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e1f1 2).toInstrSpec (mul_r64_effect_step 0x10e1f1 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x10e1f4 [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x10e1f4) (movR64R64Effect 0x10e1f4 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10e1f4 5 2).toInstrSpec (mov_r64_r64_effect_step 0x10e1f4 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x10e1f7 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x10e1f7) (movR64R64Effect 0x10e1f7 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e1f7 11 0).toInstrSpec (mov_r64_r64_effect_step 0x10e1f7 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x10e1fa [0x4C, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10e1fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e1fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e1fa 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10e1fa 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10e1fa 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f118 : InstrSpec 0x10e1ff [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x10e1ff) (movR64R64Effect 0x10e1ff 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e1ff 0 8).toInstrSpec (mov_r64_r64_effect_step 0x10e1ff 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x10e202 [0x48, 0xBA, 0x49, 0xF0, 0x9C, 0xE9, 0x34, 0x34, 0x0C, 0x00] (fun s => s.RIP = 0x10e202) (movR64Imm64Effect 0x10e202 2 0xc3434e99cf049)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e202 2 0xc3434e99cf049).toInstrSpec (mov_r64_imm64_effect_step 0x10e202 0x48 0xba (by decide) (by decide) 0xc3434e99cf049) pre_rip
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 264), (1, 266), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1b4) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f101 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 269) f101 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 270) (ρ' := [(0, 268), (1, 266), (2, 269), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1b7) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.exec (n := 271) (ρ' := [(0, 268), (1, 266), (2, 269), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1bc) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 272) (RestInside.exec (n := 272) (ρ' := [(0, 268), (1, 266), (2, 269), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1c0) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f104 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 268), (1, 266), (2, 269), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1c5) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f105 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 275), (1, 266), (2, 269), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1c8) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 275), (1, 277), (2, 269), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1d2) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f107 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 280) f107 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 281) (ρ' := [(0, 279), (1, 277), (2, 280), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1d5) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f108 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 279), (1, 282), (2, 280), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1d8) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f109 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 279), (1, 282), (2, 280), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 284), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1db) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f110 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 279), (1, 282), (2, 280), (3, 198), (4, 65), (5, 209), (6, 286), (7, 7), (8, 169), (9, 284), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1de) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f111 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 279), (1, 282), (2, 280), (3, 198), (4, 65), (5, 209), (6, 288), (7, 7), (8, 169), (9, 284), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1e2) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f112 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 290), (1, 282), (2, 280), (3, 198), (4, 65), (5, 209), (6, 288), (7, 7), (8, 169), (9, 284), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1e7) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f113 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 290), (1, 282), (2, 292), (3, 198), (4, 65), (5, 209), (6, 288), (7, 7), (8, 169), (9, 284), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1f1) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f114 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 295) f114 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 296) (ρ' := [(0, 294), (1, 282), (2, 295), (3, 198), (4, 65), (5, 209), (6, 288), (7, 7), (8, 169), (9, 284), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1f4) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f115 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 294), (1, 282), (2, 295), (3, 198), (4, 65), (5, 297), (6, 288), (7, 7), (8, 169), (9, 284), (10, 257), (11, 221), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1f7) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f116 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 300) (ρ' := [(0, 294), (1, 282), (2, 295), (3, 198), (4, 65), (5, 297), (6, 288), (7, 7), (8, 169), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1fa) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 301) (RestInside.out (n := 301) f117 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 302) (ρ' := [(0, 294), (1, 282), (2, 295), (3, 198), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1ff) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 303) (RestInside.out (n := 303) f118 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 304) (ρ' := [(0, 303), (1, 282), (2, 295), (3, 198), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e202) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 305) (RestInside.out (n := 305) f119 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 306) (ρ' := [(0, 303), (1, 282), (2, 305), (3, 198), (4, 65), (5, 297), (6, 288), (7, 7), (8, 301), (9, 284), (10, 257), (11, 299), (12, 98), (13, 273), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e20c) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_6 code

theorem rest_l10e010_4 [Bindings] (code : CodeMap) :
    Rest (n := 218) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 214), (1, 216), (2, 207), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]
      205 0x10e161 bytes_l10e010_4 b_l10e010_4 := by
  have f80 : InstrSpec 0x10e161 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e161) (mulR64Effect 0x10e161 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e161 1).toInstrSpec (mul_r64_effect_step 0x10e161 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x10e164 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x10e164) (movR64R64Effect 0x10e164 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e164 11 2).toInstrSpec (mov_r64_r64_effect_step 0x10e164 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x10e167 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e167) (movR64R64Effect 0x10e167 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e167 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e167 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x10e16a [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x10e16a) (movR64R64Effect 0x10e16a 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e16a 0 9).toInstrSpec (mov_r64_r64_effect_step 0x10e16a 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x10e16d [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e16d) (movR64Imm64Effect 0x10e16d 2 0x1000003d10)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e16d 2 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e16d 0x48 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f85 : InstrSpec 0x10e177 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e177) (mulR64Effect 0x10e177 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e177 2).toInstrSpec (mul_r64_effect_step 0x10e177 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x10e17a [0x4C, 0x03, 0x14, 0x24] (LoadPre 0x10e17a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e17a + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x10e17a 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e17a 10 (.sib 4 none 0 .none)).toInstrSpec (add_r64_m64_effect_step 0x10e17a 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f87 : InstrSpec 0x10e17e [0x4C, 0x13, 0x7C, 0x24, 0x08] (LoadPre 0x10e17e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e17e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e17e 15 (.sib 4 none 0 (.d8 0x8))))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e17e 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e17e 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f88 : InstrSpec 0x10e183 [0x4D, 0x01, 0xEA] (fun s => s.RIP = 0x10e183) (addR64R64Effect 0x10e183 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e183 10 13).toInstrSpec (add_r64_r64_effect_step 0x10e183 0x4d 0xea (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x10e186 [0x49, 0x11, 0xDF] (fun s => s.RIP = 0x10e186) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e186 15 3))
      [.gpr 15, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e186 15 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e186 0x49 0xdf c (by decide) (by decide))) pre_rip
  have f90 : InstrSpec 0x10e189 [0x4D, 0x01, 0xF2] (fun s => s.RIP = 0x10e189) (addR64R64Effect 0x10e189 10 14)
      [.gpr 10, .gpr 14] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e189 10 14).toInstrSpec (add_r64_r64_effect_step 0x10e189 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x10e18c [0x49, 0x11, 0xEF] (fun s => s.RIP = 0x10e18c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e18c 15 5))
      [.gpr 15, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e18c 15 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e18c 0x49 0xef c (by decide) (by decide))) pre_rip
  have f92 : InstrSpec 0x10e18f [0x49, 0x01, 0xCA] (fun s => s.RIP = 0x10e18f) (addR64R64Effect 0x10e18f 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e18f 10 1).toInstrSpec (add_r64_r64_effect_step 0x10e18f 0x49 0xca (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x10e192 [0x4D, 0x11, 0xDF] (fun s => s.RIP = 0x10e192) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e192 15 11))
      [.gpr 15, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e192 15 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e192 0x4d 0xdf c (by decide) (by decide))) pre_rip
  have f94 : InstrSpec 0x10e195 [0x49, 0x01, 0xC2] (fun s => s.RIP = 0x10e195) (addR64R64Effect 0x10e195 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e195 10 0).toInstrSpec (add_r64_r64_effect_step 0x10e195 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x10e198 [0x49, 0x11, 0xD7] (fun s => s.RIP = 0x10e198) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e198 15 2))
      [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e198 15 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e198 0x49 0xd7 c (by decide) (by decide))) pre_rip
  have f96 : InstrSpec 0x10e19b [0x4D, 0x01, 0xC2] (fun s => s.RIP = 0x10e19b) (addR64R64Effect 0x10e19b 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e19b 10 8).toInstrSpec (add_r64_r64_effect_step 0x10e19b 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x10e19e [0x49, 0x83, 0xD7, 0x00] (fun s => s.RIP = 0x10e19e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e19e 15 0x0))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e19e 15 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e19e 0x49 0xd7 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f98 : InstrSpec 0x10e1a2 [0x4D, 0x0F, 0xA4, 0xD7, 0x0C] (fun s => s.RIP = 0x10e1a2) (shldR64R64Effect 0x10e1a2 5 15 10 12)
      [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e1a2 5 15 10 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e1a2 0x4d (by decide) 0xd7 (by decide) 0xc) pre_rip
  have f99 : InstrSpec 0x10e1a7 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x10e1a7) (movR64R64Effect 0x10e1a7 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e1a7 0 6).toInstrSpec (mov_r64_r64_effect_step 0x10e1a7 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f80 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 219) f80 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 220) (ρ' := [(0, 218), (1, 216), (2, 219), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e164) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f81 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 218), (1, 216), (2, 219), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 221), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e167) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 218), (1, 223), (2, 219), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 221), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e16a) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f83 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 225), (1, 223), (2, 219), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 221), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e16d) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f84 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 225), (1, 223), (2, 227), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 221), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e177) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f85 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 230) f85 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 231) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 221), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e17a) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f86 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 233) f86 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 234) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 232), (11, 221), (12, 98), (13, 200), (14, 211), (15, 187), (16, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e17e) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f87 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 232), (11, 221), (12, 98), (13, 200), (14, 211), (15, 235), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e183) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f88 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 238) f88 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 239) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 237), (11, 221), (12, 98), (13, 200), (14, 211), (15, 235), (16, 238), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e186) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f89 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 237), (11, 221), (12, 98), (13, 200), (14, 211), (15, 240), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e189) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f90 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 243) f90 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 244) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 242), (11, 221), (12, 98), (13, 200), (14, 211), (15, 240), (16, 243), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e18c) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f91 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 242), (11, 221), (12, 98), (13, 200), (14, 211), (15, 245), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e18f) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f92 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 248) f92 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 249) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 247), (11, 221), (12, 98), (13, 200), (14, 211), (15, 245), (16, 248), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e192) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f93 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 247), (11, 221), (12, 98), (13, 200), (14, 211), (15, 250), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e195) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f94 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 253) f94 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 254) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 252), (11, 221), (12, 98), (13, 200), (14, 211), (15, 250), (16, 253), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e198) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f95 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 252), (11, 221), (12, 98), (13, 200), (14, 211), (15, 255), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e19b) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f96 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 258) f96 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 259) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 255), (16, 258), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e19e) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.out (n := 260) f97 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 261) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 260), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1a2) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f98 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 229), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1a7) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 264), (1, 223), (2, 230), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 257), (11, 221), (12, 98), (13, 200), (14, 211), (15, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e1aa) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_5 code

theorem rest_l10e010_3 [Bindings] (code : CodeMap) :
    Rest (n := 178) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 175), (1, 154), (2, 176), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]
      225 0x10e104 bytes_l10e010_3 b_l10e010_3 := by
  have f60 : InstrSpec 0x10e104 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x10e104 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e104 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e104 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e104 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10e104 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x10e109 [0x48, 0x89, 0x04, 0x24] (StorePre 0x10e109 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e109 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e109 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e109 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10e109 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f62 : InstrSpec 0x10e10d [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10e10d) (movR64R64Effect 0x10e10d 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e10d 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10e10d 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x10e110 [0x48, 0xB9, 0xEA, 0x79, 0x44, 0xE6, 0x06, 0x71, 0x00, 0x00] (fun s => s.RIP = 0x10e110) (movR64Imm64Effect 0x10e110 1 0x7106e64479ea)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e110 1 0x7106e64479ea).toInstrSpec (mov_r64_imm64_effect_step 0x10e110 0x48 0xb9 (by decide) (by decide) 0x7106e64479ea) pre_rip
  have f64 : InstrSpec 0x10e11a [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e11a) (mulR64Effect 0x10e11a 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e11a 1).toInstrSpec (mul_r64_effect_step 0x10e11a 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x10e11d [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x10e11d) (movR64R64Effect 0x10e11d 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10e11d 15 2).toInstrSpec (mov_r64_r64_effect_step 0x10e11d 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x10e120 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x10e120) (movR64R64Effect 0x10e120 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10e120 10 0).toInstrSpec (mov_r64_r64_effect_step 0x10e120 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x10e123 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e123) (movR64R64Effect 0x10e123 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e123 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e123 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x10e126 [0x48, 0xB9, 0x49, 0xF0, 0x9C, 0xE9, 0x34, 0x34, 0x0C, 0x00] (fun s => s.RIP = 0x10e126) (movR64Imm64Effect 0x10e126 1 0xc3434e99cf049)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e126 1 0xc3434e99cf049).toInstrSpec (mov_r64_imm64_effect_step 0x10e126 0x48 0xb9 (by decide) (by decide) 0xc3434e99cf049) pre_rip
  have f69 : InstrSpec 0x10e130 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e130) (mulR64Effect 0x10e130 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e130 1).toInstrSpec (mul_r64_effect_step 0x10e130 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10e133 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x10e133) (movR64R64Effect 0x10e133 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10e133 3 2).toInstrSpec (mov_r64_r64_effect_step 0x10e133 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x10e136 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x10e136) (movR64R64Effect 0x10e136 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10e136 13 0).toInstrSpec (mov_r64_r64_effect_step 0x10e136 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x10e139 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x10e139) (movR64R64Effect 0x10e139 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e139 0 5).toInstrSpec (mov_r64_r64_effect_step 0x10e139 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10e13c [0x48, 0xB9, 0x13, 0x5C, 0x99, 0x58, 0x2F, 0x51, 0x07, 0x00] (fun s => s.RIP = 0x10e13c) (movR64Imm64Effect 0x10e13c 1 0x7512f58995c13)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e13c 1 0x7512f58995c13).toInstrSpec (mov_r64_imm64_effect_step 0x10e13c 0x48 0xb9 (by decide) (by decide) 0x7512f58995c13) pre_rip
  have f74 : InstrSpec 0x10e146 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e146) (mulR64Effect 0x10e146 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e146 1).toInstrSpec (mul_r64_effect_step 0x10e146 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x10e149 [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x10e149) (movR64R64Effect 0x10e149 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10e149 5 2).toInstrSpec (mov_r64_r64_effect_step 0x10e149 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x10e14c [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x10e14c) (movR64R64Effect 0x10e14c 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10e14c 14 0).toInstrSpec (mov_r64_r64_effect_step 0x10e14c 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x10e14f [0x4C, 0x89, 0x64, 0x24, 0x30] (StorePre 0x10e14f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e14f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e14f 12 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e14f 12 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10e14f 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x10e154 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x10e154) (movR64R64Effect 0x10e154 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e154 0 12).toInstrSpec (mov_r64_r64_effect_step 0x10e154 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x10e157 [0x48, 0xB9, 0xEE, 0x01, 0x95, 0x71, 0x28, 0x6C, 0x09, 0x00] (fun s => s.RIP = 0x10e157) (movR64Imm64Effect 0x10e157 1 0x96c28719501ee)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e157 1 0x96c28719501ee).toInstrSpec (mov_r64_imm64_effect_step 0x10e157 0x48 0xb9 (by decide) (by decide) 0x96c28719501ee) pre_rip
  refine Rest.ofInside (n := 178) (RestInside.exec (n := 178) (ρ' := [(0, 175), (1, 154), (2, 176), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e109) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 179) (RestInside.exec (n := 179) (ρ' := [(0, 175), (1, 154), (2, 176), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e10d) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f62 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 180), (1, 154), (2, 176), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e110) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 180), (1, 182), (2, 176), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e11a) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f64 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 185) f64 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 186) (ρ' := [(0, 184), (1, 182), (2, 185), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e11d) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f65 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 184), (1, 182), (2, 185), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e120) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f66 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 184), (1, 182), (2, 185), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 72), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e123) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 191), (1, 182), (2, 185), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 72), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e126) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 191), (1, 193), (2, 185), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 72), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e130) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f69 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 196) f69 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 197) (ρ' := [(0, 195), (1, 193), (2, 196), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 72), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e133) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f70 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 195), (1, 193), (2, 196), (3, 198), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 72), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e136) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f71 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 195), (1, 193), (2, 196), (3, 198), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e139) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f72 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 202), (1, 193), (2, 196), (3, 198), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e13c) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f73 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 202), (1, 204), (2, 196), (3, 198), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e146) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f74 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 207) f74 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 208) (ρ' := [(0, 206), (1, 204), (2, 207), (3, 198), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e149) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f75 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 206), (1, 204), (2, 207), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 139), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e14c) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f76 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 206), (1, 204), (2, 207), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e14f) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.exec (n := 213) (ρ' := [(0, 206), (1, 204), (2, 207), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e154) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 214), (1, 204), (2, 207), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e157) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 214), (1, 216), (2, 207), (3, 198), (4, 65), (5, 209), (6, 171), (7, 7), (8, 169), (9, 167), (10, 189), (11, 134), (12, 98), (13, 200), (14, 211), (15, 187), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e161) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_4 code

theorem rest_l10e010_2 [Bindings] (code : CodeMap) :
    Rest (n := 134) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 127), (1, 120), (2, 128), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 130), (11, 132), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]
      245 0x10e0ab bytes_l10e010_2 b_l10e010_2 := by
  have f40 : InstrSpec 0x10e0ab [0x4D, 0x01, 0xC3] (fun s => s.RIP = 0x10e0ab) (addR64R64Effect 0x10e0ab 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e0ab 11 8).toInstrSpec (add_r64_r64_effect_step 0x10e0ab 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10e0ae [0x49, 0x11, 0xCA] (fun s => s.RIP = 0x10e0ae) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e0ae 10 1))
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e0ae 10 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e0ae 0x49 0xca c (by decide) (by decide))) pre_rip
  have f42 : InstrSpec 0x10e0b1 [0x49, 0xBE, 0x7C, 0x65, 0x2B, 0x6A, 0xE9, 0x7A, 0x00, 0x00] (fun s => s.RIP = 0x10e0b1) (movR64Imm64Effect 0x10e0b1 14 0x7ae96a2b657c)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x10e0b1 14 0x7ae96a2b657c).toInstrSpec (mov_r64_imm64_effect_step 0x10e0b1 0x49 0xbe (by decide) (by decide) 0x7ae96a2b657c) pre_rip
  have f43 : InstrSpec 0x10e0bb [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x10e0bb) (movR64R64Effect 0x10e0bb 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e0bb 0 12).toInstrSpec (mov_r64_r64_effect_step 0x10e0bb 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x10e0be [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x10e0be) (mulR64Effect 0x10e0be 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e0be 14).toInstrSpec (mul_r64_effect_step 0x10e0be 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10e0c1 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x10e0c1) (movR64R64Effect 0x10e0c1 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10e0c1 3 0).toInstrSpec (mov_r64_r64_effect_step 0x10e0c1 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10e0c4 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10e0c4) (movR64R64Effect 0x10e0c4 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e0c4 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10e0c4 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10e0c7 [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10e0c7) (movR64Imm64Effect 0x10e0c7 0 0xffffffffffffc)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10e0c7 0 0xffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x10e0c7 0x48 0xb8 (by decide) (by decide) 0xffffffffffffc) pre_rip
  have f48 : InstrSpec 0x10e0d1 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x10e0d1) (andR64R64Effect 0x10e0d1 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e0d1 0 3).toInstrSpec (and_r64_r64_effect_step 0x10e0d1 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10e0d4 [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e0d4) (movR64Imm64Effect 0x10e0d4 1 0x1000003d10)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e0d4 1 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e0d4 0x48 0xb9 (by decide) (by decide) 0x1000003d10) pre_rip
  have f50 : InstrSpec 0x10e0de [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e0de) (mulR64Effect 0x10e0de 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e0de 1).toInstrSpec (mul_r64_effect_step 0x10e0de 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10e0e1 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10e0e1) (movR64R64Effect 0x10e0e1 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10e0e1 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10e0e1 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10e0e4 [0x4C, 0x01, 0xD8] (fun s => s.RIP = 0x10e0e4) (addR64R64Effect 0x10e0e4 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e0e4 0 11).toInstrSpec (add_r64_r64_effect_step 0x10e0e4 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10e0e7 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x10e0e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e0e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e0e7 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e0e7 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10e0e7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x10e0ec [0x4D, 0x11, 0xD0] (fun s => s.RIP = 0x10e0ec) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e0ec 8 10))
      [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e0ec 8 10).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e0ec 0x4d 0xd0 c (by decide) (by decide))) pre_rip
  have f55 : InstrSpec 0x10e0ef [0x49, 0x0F, 0xA4, 0xD9, 0x0C] (fun s => s.RIP = 0x10e0ef) (shldR64R64Effect 0x10e0ef 5 9 3 12)
      [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e0ef 5 9 3 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e0ef 0x49 (by decide) 0xd9 (by decide) 0xc) pre_rip
  have f56 : InstrSpec 0x10e0f4 [0x49, 0x0F, 0xA4, 0xC0, 0x0C] (fun s => s.RIP = 0x10e0f4) (shldR64R64Effect 0x10e0f4 5 8 0 12)
      [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e0f4 5 8 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e0f4 0x49 (by decide) 0xc0 (by decide) 0xc) pre_rip
  have f57 : InstrSpec 0x10e0f9 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x10e0f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e0f9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e0f9 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10e0f9 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10e0f9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x10e0fe [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x10e0fe) (movR64R64Effect 0x10e0fe 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e0fe 0 6).toInstrSpec (mov_r64_r64_effect_step 0x10e0fe 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10e101 [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x10e101) (mulR64Effect 0x10e101 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e101 14).toInstrSpec (mul_r64_effect_step 0x10e101 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f40 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 135) f40 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 136) (ρ' := [(0, 127), (1, 120), (2, 128), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 130), (11, 134), (12, 98), (13, 72), (14, 14), (15, 70), (16, 135), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0ae) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f41 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 127), (1, 120), (2, 128), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 137), (11, 134), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0b1) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f42 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 127), (1, 120), (2, 128), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0bb) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 141), (1, 120), (2, 128), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0be) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 144) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 145) (ρ' := [(0, 143), (1, 120), (2, 144), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0c1) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f45 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 143), (1, 120), (2, 144), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0c4) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f46 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 143), (1, 120), (2, 144), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0c7) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f47 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 150), (1, 120), (2, 144), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0d1) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f48 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 152), (1, 120), (2, 144), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0d4) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f49 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 152), (1, 154), (2, 144), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0de) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 157) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 158) (ρ' := [(0, 156), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0e1) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f51 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 156), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 159), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0e4) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 162) f52 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 163) (ρ' := [(0, 161), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 159), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (16, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0e7) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.exec (n := 164) (ρ' := [(0, 161), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 159), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (16, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0ec) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f54 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 161), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 165), (9, 148), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0ef) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f55 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 161), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 165), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0f4) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f56 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 161), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 6), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0f9) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f57 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 161), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0fe) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 173), (1, 154), (2, 157), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e101) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f59 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 176) f59 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 177) (ρ' := [(0, 175), (1, 154), (2, 176), (3, 146), (4, 65), (5, 74), (6, 171), (7, 7), (8, 169), (9, 167), (10, 137), (11, 134), (12, 98), (13, 72), (14, 139), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e104) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_3 code

theorem rest_l10e010_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x10e010 bytes_l10e010) [(0, 88), (1, 82), (2, 86), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]
      265 0x10e05c bytes_l10e010_1 b_l10e010_1 := by
  have f20 : InstrSpec 0x10e05c [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e05c) (mulR64Effect 0x10e05c 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e05c 2).toInstrSpec (mul_r64_effect_step 0x10e05c 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10e05f [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x10e05f) (movR64R64Effect 0x10e05f 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e05f 9 0).toInstrSpec (mov_r64_r64_effect_step 0x10e05f 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10e062 [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x10e062) (movR64R64Effect 0x10e062 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10e062 10 2).toInstrSpec (mov_r64_r64_effect_step 0x10e062 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10e065 [0x4C, 0x8B, 0x66, 0x20] (LoadPre 0x10e065 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x10e065 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e065 12 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10e065 12 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10e065 0x4c (by decide) 4 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10e069 [0x49, 0x01, 0xC9] (fun s => s.RIP = 0x10e069) (addR64R64Effect 0x10e069 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e069 9 1).toInstrSpec (add_r64_r64_effect_step 0x10e069 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10e06c [0x4D, 0x11, 0xC2] (fun s => s.RIP = 0x10e06c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e06c 10 8))
      [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e06c 10 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e06c 0x4d 0xc2 c (by decide) (by decide))) pre_rip
  have f26 : InstrSpec 0x10e06f [0x48, 0xB9, 0x13, 0x5C, 0x99, 0x58, 0x2F, 0x51, 0x07, 0x00] (fun s => s.RIP = 0x10e06f) (movR64Imm64Effect 0x10e06f 1 0x7512f58995c13)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e06f 1 0x7512f58995c13).toInstrSpec (mov_r64_imm64_effect_step 0x10e06f 0x48 0xb9 (by decide) (by decide) 0x7512f58995c13) pre_rip
  have f27 : InstrSpec 0x10e079 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e079) (movR64R64Effect 0x10e079 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e079 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e079 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10e07c [0x4C, 0x89, 0x6C, 0x24, 0x18] (StorePre 0x10e07c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e07c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e07c 13 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e07c 13 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10e07c 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x10e081 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e081) (mulR64Effect 0x10e081 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e081 1).toInstrSpec (mul_r64_effect_step 0x10e081 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10e084 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10e084) (movR64R64Effect 0x10e084 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e084 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10e084 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10e087 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x10e087) (movR64R64Effect 0x10e087 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10e087 8 0).toInstrSpec (mov_r64_r64_effect_step 0x10e087 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10e08a [0x4D, 0x01, 0xC8] (fun s => s.RIP = 0x10e08a) (addR64R64Effect 0x10e08a 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e08a 8 9).toInstrSpec (add_r64_r64_effect_step 0x10e08a 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10e08d [0x4C, 0x11, 0xD1] (fun s => s.RIP = 0x10e08d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e08d 1 10))
      [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e08d 1 10).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e08d 0x4c 0xd1 c (by decide) (by decide))) pre_rip
  have f34 : InstrSpec 0x10e090 [0x48, 0xBA, 0xEE, 0x01, 0x95, 0x71, 0x28, 0x6C, 0x09, 0x00] (fun s => s.RIP = 0x10e090) (movR64Imm64Effect 0x10e090 2 0x96c28719501ee)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e090 2 0x96c28719501ee).toInstrSpec (mov_r64_imm64_effect_step 0x10e090 0x48 0xba (by decide) (by decide) 0x96c28719501ee) pre_rip
  have f35 : InstrSpec 0x10e09a [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x10e09a) (movR64R64Effect 0x10e09a 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e09a 0 5).toInstrSpec (mov_r64_r64_effect_step 0x10e09a 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10e09d [0x48, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x10e09d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e09d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e09d 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e09d 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10e09d 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x10e0a2 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e0a2) (mulR64Effect 0x10e0a2 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e0a2 2).toInstrSpec (mul_r64_effect_step 0x10e0a2 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x10e0a5 [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x10e0a5) (movR64R64Effect 0x10e0a5 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10e0a5 10 2).toInstrSpec (mov_r64_r64_effect_step 0x10e0a5 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10e0a8 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x10e0a8) (movR64R64Effect 0x10e0a8 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e0a8 11 0).toInstrSpec (mov_r64_r64_effect_step 0x10e0a8 0x49 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 91), (1, 82), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e05f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 91), (1, 82), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 94), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e062) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 91), (1, 82), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 94), (10, 96), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e065) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 91), (1, 82), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 94), (10, 96), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e069) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 101) f24 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 102) (ρ' := [(0, 91), (1, 82), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 100), (10, 96), (12, 98), (13, 72), (14, 14), (15, 70), (16, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e06c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 91), (1, 82), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e06f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 91), (1, 105), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e079) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 107), (1, 105), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e07c) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 107), (1, 105), (2, 92), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e081) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 111) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 112) (ρ' := [(0, 110), (1, 105), (2, 111), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e084) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 110), (1, 113), (2, 111), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e087) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 110), (1, 113), (2, 111), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 115), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e08a) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 118) f32 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 119) (ρ' := [(0, 110), (1, 113), (2, 111), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (16, 118), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e08d) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 110), (1, 120), (2, 111), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e090) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 110), (1, 120), (2, 122), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e09a) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 124), (1, 120), (2, 122), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e09d) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 124), (1, 120), (2, 122), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0a2) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 129) (ρ' := [(0, 127), (1, 120), (2, 128), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 103), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0a5) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f38 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 127), (1, 120), (2, 128), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 130), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0a8) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f39 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 127), (1, 120), (2, 128), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 117), (9, 100), (10, 130), (11, 132), (12, 98), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e0ab) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e010_2 code

theorem rest_l10e010 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10e010 bytes_l10e010) (entryMap (live .l10e010))
      285 0x10e010 bytes_l10e010 b_l10e010 := by
  have f0 : InstrSpec 0x10e010 [0x55] (PushPre 0x10e010 1) (pushR64Effect 0x10e010 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e010 1 5).toInstrSpec (push_r64_effect_step 0x10e010 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10e011 [0x41, 0x57] (PushPre 0x10e011 2) (pushR64Effect 0x10e011 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e011 2 15).toInstrSpec (push_r64_rex_effect_step 0x10e011 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10e013 [0x41, 0x56] (PushPre 0x10e013 2) (pushR64Effect 0x10e013 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e013 2 14).toInstrSpec (push_r64_rex_effect_step 0x10e013 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10e015 [0x41, 0x55] (PushPre 0x10e015 2) (pushR64Effect 0x10e015 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e015 2 13).toInstrSpec (push_r64_rex_effect_step 0x10e015 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10e017 [0x41, 0x54] (PushPre 0x10e017 2) (pushR64Effect 0x10e017 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e017 2 12).toInstrSpec (push_r64_rex_effect_step 0x10e017 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10e019 [0x53] (PushPre 0x10e019 1) (pushR64Effect 0x10e019 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e019 1 3).toInstrSpec (push_r64_effect_step 0x10e019 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10e01a [0x48, 0x83, 0xEC, 0x50] (fun s => s.RIP = 0x10e01a) (subR64Imm8Effect 0x10e01a 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10e01a 4 0x50).toInstrSpec (sub_r64_imm8_effect_step 0x10e01a 0x48 0xec 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10e01e [0x48, 0x8B, 0x06] (LoadPre 0x10e01e (fun s => AddrMode.addr (.base 6 .none) s (0x10e01e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10e01e 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e01e 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10e01e 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10e021 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10e021 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e021 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e021 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e021 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10e021 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10e026 [0x4C, 0x8B, 0x7E, 0x08] (LoadPre 0x10e026 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10e026 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e026 15 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10e026 15 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10e026 0x4c (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10e02a [0x4C, 0x8B, 0x6E, 0x10] (LoadPre 0x10e02a (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10e02a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e02a 13 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10e02a 13 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10e02a 0x4c (by decide) 5 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10e02e [0x48, 0x8B, 0x6E, 0x18] (LoadPre 0x10e02e (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10e02e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e02e 5 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10e02e 5 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10e02e 0x48 (by decide) 5 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10e032 [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x10e032 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e032 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e032 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e032 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10e032 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10e037 [0x48, 0xB9, 0xEA, 0x79, 0x44, 0xE6, 0x06, 0x71, 0x00, 0x00] (fun s => s.RIP = 0x10e037) (movR64Imm64Effect 0x10e037 1 0x7106e64479ea)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e037 1 0x7106e64479ea).toInstrSpec (mov_r64_imm64_effect_step 0x10e037 0x48 0xb9 (by decide) (by decide) 0x7106e64479ea) pre_rip
  have f14 : InstrSpec 0x10e041 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e041) (mulR64Effect 0x10e041 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e041 1).toInstrSpec (mul_r64_effect_step 0x10e041 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10e044 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e044) (movR64R64Effect 0x10e044 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e044 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e044 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10e047 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10e047) (movR64R64Effect 0x10e047 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10e047 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10e047 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10e04a [0x48, 0xBA, 0x49, 0xF0, 0x9C, 0xE9, 0x34, 0x34, 0x0C, 0x00] (fun s => s.RIP = 0x10e04a) (movR64Imm64Effect 0x10e04a 2 0xc3434e99cf049)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e04a 2 0xc3434e99cf049).toInstrSpec (mov_r64_imm64_effect_step 0x10e04a 0x48 0xba (by decide) (by decide) 0xc3434e99cf049) pre_rip
  have f18 : InstrSpec 0x10e054 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10e054) (movR64R64Effect 0x10e054 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e054 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10e054 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10e057 [0x4C, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x10e057 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e057 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e057 15 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e057 15 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10e057 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e011) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e013) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e015) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e017) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e019) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e01a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e01e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e021) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e026) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e02a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e02e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e032) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e037) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 67), (1, 77), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e041) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 77), (2, 80), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e044) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 79), (1, 82), (2, 80), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e047) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 79), (1, 82), (2, 80), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e04a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 79), (1, 82), (2, 86), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e054) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 82), (2, 86), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e057) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 88), (1, 82), (2, 86), (3, 3), (4, 65), (5, 74), (6, 6), (7, 7), (8, 84), (12, 12), (13, 72), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e05c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10e010_1 code

theorem block_l10e010 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10e010 :=
  Rest.liftedBlock (rest_l10e010 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10e010 x hx)

end K256.Proofs.Ecdh.LIR
