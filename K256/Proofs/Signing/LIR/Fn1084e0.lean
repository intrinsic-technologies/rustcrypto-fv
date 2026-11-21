import K256.Proofs.Signing.LIR.Program

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

theorem rest_l1084e0_13 [Bindings] (code : CodeMap) :
    Rest (n := 554) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 512), (1, 552), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x10885c bytes_l1084e0_13 b_l1084e0_13 := by
  have f260 : InstrSpec 0x10885c [0x22, 0x4C, 0x24, 0x20] (LoadPre 0x10885c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10885c + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x10885c 4 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (andR8M8Effect_footprint 0x10885c 4 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (and_r8_m8_effect_step 0x10885c 1 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f261 : InstrSpec 0x108860 [0x48, 0x89, 0x37] (StorePre 0x108860 3 (fun s => AddrMode.addr (.base 7 .none) s (0x108860 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x108860 6 (.base 7 .none))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x108860 6 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x108860 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f262 : InstrSpec 0x108863 [0x48, 0x89, 0x47, 0x08] (StorePre 0x108863 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x108863 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108863 0 (.base 7 (.d8 0x8)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x108863 0 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108863 0x48 (by decide) 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f263 : InstrSpec 0x108867 [0x4C, 0x89, 0x47, 0x10] (StorePre 0x108867 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x108867 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108867 8 (.base 7 (.d8 0x10)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x108867 8 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108867 0x4c (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f264 : InstrSpec 0x10886b [0x4C, 0x89, 0x4F, 0x18] (StorePre 0x10886b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10886b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10886b 9 (.base 7 (.d8 0x18)))
      [.gpr 9, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10886b 9 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10886b 0x4c (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f265 : InstrSpec 0x10886f [0x4C, 0x89, 0x57, 0x20] (StorePre 0x10886f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10886f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10886f 10 (.base 7 (.d8 0x20)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10886f 10 (.base 7 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10886f 0x4c (by decide) 2 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f266 : InstrSpec 0x108873 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x108873) (movR64R64Effect 0x108873 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108873 0 2).toInstrSpec (mov_r64_r64_effect_step 0x108873 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f267 : InstrSpec 0x108876 [0x08, 0xC8] (fun s => s.RIP = 0x108876) (orR8R8Effect 0x108876 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR8R8Effect_footprint 0x108876 2 0 1).toInstrSpec (or_r8_r8_effect_step 0x108876 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f268 : InstrSpec 0x108878 [0x88, 0x47, 0x28] (StorePre 0x108878 3 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x108878 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108878 3 0 (.base 7 (.d8 0x28)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x108878 3 0 (.base 7 (.d8 0x28))).toInstrSpec (mov_m8_r8_effect_step 0x108878 0 (by decide) (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f269 : InstrSpec 0x10887b [0x48, 0x83, 0xC4, 0x40] (fun s => s.RIP = 0x10887b) (addR64Imm8Effect 0x10887b 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10887b 4 0x40).toInstrSpec (add_r64_imm8_effect_step 0x10887b 0x48 0xc4 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f270 : InstrSpec 0x10887f [0x5B] (PopPre 0x10887f) (popR64Effect 0x10887f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10887f 1 3).toInstrSpec (pop_r64_effect_step 0x10887f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f271 : InstrSpec 0x108880 [0x41, 0x5C] (PopPre 0x108880) (popR64Effect 0x108880 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108880 2 12).toInstrSpec (pop_r64_rex_effect_step 0x108880 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f272 : InstrSpec 0x108882 [0x41, 0x5D] (PopPre 0x108882) (popR64Effect 0x108882 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108882 2 13).toInstrSpec (pop_r64_rex_effect_step 0x108882 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f273 : InstrSpec 0x108884 [0x41, 0x5E] (PopPre 0x108884) (popR64Effect 0x108884 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108884 2 14).toInstrSpec (pop_r64_rex_effect_step 0x108884 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f274 : InstrSpec 0x108886 [0x41, 0x5F] (PopPre 0x108886) (popR64Effect 0x108886 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108886 2 15).toInstrSpec (pop_r64_rex_effect_step 0x108886 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f275 : InstrSpec 0x108888 [0x5D] (PopPre 0x108888) (popR64Effect 0x108888 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108888 1 5).toInstrSpec (pop_r64_effect_step 0x108888 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f276 : InstrSpec 0x108889 [0xC3] (RetPre 0x108889) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x108889).toInstrSpec (ret_effect_step 0x108889) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 554) (RestInside.out (n := 554) f260 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 555) (ρ' := [(0, 512), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108860) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 556) (RestInside.exec (n := 556) (ρ' := [(0, 512), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108863) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 557) (RestInside.exec (n := 557) (ρ' := [(0, 512), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108867) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 558) (RestInside.exec (n := 558) (ρ' := [(0, 512), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10886b) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 559) (RestInside.exec (n := 559) (ρ' := [(0, 512), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10886f) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 560) (RestInside.exec (n := 560) (ρ' := [(0, 512), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108873) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 561) (RestInside.out (n := 561) f266 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 562) (ρ' := [(0, 561), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108876) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 563) (RestInside.out (n := 563) f267 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 564) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108878) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 565) (RestInside.exec (n := 565) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10887b) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 566) (RestInside.out (n := 566) f269 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 567) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 439), (4, 566), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10887f) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 568) (RestInside.out (n := 568) f270 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 569) f270 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 570) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 568), (4, 569), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108880) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 571) (RestInside.out (n := 571) f271 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 572) f271 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 573) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 568), (4, 572), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108882) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 574) (RestInside.out (n := 574) f272 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 575) f272 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 576) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 568), (4, 575), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 574), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108884) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 577) (RestInside.out (n := 577) f273 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 578) f273 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 579) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 568), (4, 578), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 574), (14, 577), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108886) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 580) (RestInside.out (n := 580) f274 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 581) f274 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 582) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 568), (4, 581), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 574), (14, 577), (15, 580), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108888) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 583) (RestInside.out (n := 583) f275 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 584) f275 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 585) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 568), (4, 584), (5, 583), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 574), (14, 577), (15, 580), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108889) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 586) (RestInside.out (n := 586) f276 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 587) f276 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 588) (ρ' := [(0, 563), (1, 554), (2, 550), (3, 568), (4, 587), (5, 583), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 574), (14, 577), (15, 580), (22, 22), (39, 39), (50, 50), (51, 51)]) f276 (by decide) rfl rfl rfl (by decide)

theorem rest_l1084e0_12 [Bindings] (code : CodeMap) :
    Rest (n := 517) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 515), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]
      37 0x10881b bytes_l1084e0_12 b_l1084e0_12 := by
  have f240 : InstrSpec 0x10881b [0x4D, 0x31, 0xCB] (fun s => s.RIP = 0x10881b) (xorR64R64Effect 0x10881b 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10881b 11 9).toInstrSpec (xor_r64_r64_effect_step 0x10881b 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f241 : InstrSpec 0x10881e [0x49, 0xF7, 0xD8] (fun s => s.RIP = 0x10881e) (negR64Effect 0x10881e 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR64Effect_footprint 0x10881e 8).toInstrSpec (neg_r64_effect_step 0x10881e 0x49 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f242 : InstrSpec 0x108821 [0x4D, 0x21, 0xD8] (fun s => s.RIP = 0x108821) (andR64R64Effect 0x108821 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108821 8 11).toInstrSpec (and_r64_r64_effect_step 0x108821 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f243 : InstrSpec 0x108824 [0x4D, 0x31, 0xC8] (fun s => s.RIP = 0x108824) (xorR64R64Effect 0x108824 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108824 8 9).toInstrSpec (xor_r64_r64_effect_step 0x108824 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f244 : InstrSpec 0x108827 [0x88, 0x0C, 0x24] (StorePre 0x108827 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108827 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108827 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108827 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x108827 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f245 : InstrSpec 0x10882a [0x44, 0x0F, 0xB6, 0x0C, 0x24] (LoadPre 0x10882a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10882a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10882a 5 9 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x10882a 5 9 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10882a 0x44 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f246 : InstrSpec 0x10882f [0x4D, 0x31, 0xD5] (fun s => s.RIP = 0x10882f) (xorR64R64Effect 0x10882f 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10882f 13 10).toInstrSpec (xor_r64_r64_effect_step 0x10882f 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f247 : InstrSpec 0x108832 [0x49, 0xF7, 0xD9] (fun s => s.RIP = 0x108832) (negR64Effect 0x108832 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR64Effect_footprint 0x108832 9).toInstrSpec (neg_r64_effect_step 0x108832 0x49 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f248 : InstrSpec 0x108835 [0x4D, 0x21, 0xE9] (fun s => s.RIP = 0x108835) (andR64R64Effect 0x108835 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108835 9 13).toInstrSpec (and_r64_r64_effect_step 0x108835 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f249 : InstrSpec 0x108838 [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x108838) (xorR64R64Effect 0x108838 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108838 9 10).toInstrSpec (xor_r64_r64_effect_step 0x108838 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f250 : InstrSpec 0x10883b [0x88, 0x0C, 0x24] (StorePre 0x10883b 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10883b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10883b 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10883b 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x10883b 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f251 : InstrSpec 0x10883e [0x49, 0x89, 0xE2] (fun s => s.RIP = 0x10883e) (movR64R64Effect 0x10883e 10 4)
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10883e 10 4).toInstrSpec (mov_r64_r64_effect_step 0x10883e 0x49 0xe2 (by decide) (by decide)) pre_rip
  have f252 : InstrSpec 0x108841 [0x44, 0x0F, 0xB6, 0x14, 0x24] (LoadPre 0x108841 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108841 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108841 5 10 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x108841 5 10 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108841 0x44 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f253 : InstrSpec 0x108846 [0x48, 0x31, 0xDA] (fun s => s.RIP = 0x108846) (xorR64R64Effect 0x108846 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108846 2 3).toInstrSpec (xor_r64_r64_effect_step 0x108846 0x48 0xda (by decide) (by decide)) pre_rip
  have f254 : InstrSpec 0x108849 [0x49, 0xF7, 0xDA] (fun s => s.RIP = 0x108849) (negR64Effect 0x108849 10)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (negR64Effect_footprint 0x108849 10).toInstrSpec (neg_r64_effect_step 0x108849 0x49 0xda (by decide) (by decide) (by decide)) pre_rip
  have f255 : InstrSpec 0x10884c [0x49, 0x21, 0xD2] (fun s => s.RIP = 0x10884c) (andR64R64Effect 0x10884c 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10884c 10 2).toInstrSpec (and_r64_r64_effect_step 0x10884c 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f256 : InstrSpec 0x10884f [0x49, 0x31, 0xDA] (fun s => s.RIP = 0x10884f) (xorR64R64Effect 0x10884f 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10884f 10 3).toInstrSpec (xor_r64_r64_effect_step 0x10884f 0x49 0xda (by decide) (by decide)) pre_rip
  have f257 : InstrSpec 0x108852 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x108852 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108852 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108852 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x108852 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x108852 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f258 : InstrSpec 0x108857 [0x20, 0xCA] (fun s => s.RIP = 0x108857) (andR8R8Effect 0x108857 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR8R8Effect_footprint 0x108857 2 2 1).toInstrSpec (and_r8_r8_effect_step 0x108857 0xca (by decide) (by decide) (by decide)) pre_rip
  have f259 : InstrSpec 0x108859 [0x80, 0xF1, 0x01] (fun s => s.RIP = 0x108859) (xorR8Imm8Effect 0x108859 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR8Imm8Effect_footprint 0x108859 3 1 0x1).toInstrSpec (xor_r8_imm8_effect_step 0x108859 0xf1 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 517) (RestInside.out (n := 517) f240 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 518) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 515), (9, 357), (10, 384), (11, 517), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10881e) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 519) (RestInside.out (n := 519) f241 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 520) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 519), (9, 357), (10, 384), (11, 517), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108821) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 521) (RestInside.out (n := 521) f242 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 522) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 521), (9, 357), (10, 384), (11, 517), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108824) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 523) (RestInside.out (n := 523) f243 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 524) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 357), (10, 384), (11, 517), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108827) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 525) (RestInside.exec (n := 525) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 357), (10, 384), (11, 517), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10882a) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 526) (RestInside.out (n := 526) f245 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 527) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 526), (10, 384), (11, 517), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10882f) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 528) (RestInside.out (n := 528) f246 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 529) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 526), (10, 384), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108832) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 530) (RestInside.out (n := 530) f247 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 531) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 530), (10, 384), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108835) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 532) (RestInside.out (n := 532) f248 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 533) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 532), (10, 384), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108838) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 534) (RestInside.out (n := 534) f249 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 535) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 384), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10883b) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 536) (RestInside.exec (n := 536) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 384), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10883e) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 537) (RestInside.exec (n := 537) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108841) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 538) (RestInside.out (n := 538) f252 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 539) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 538), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108846) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 540) (RestInside.out (n := 540) f253 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 541) (ρ' := [(0, 512), (1, 459), (2, 540), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 538), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108849) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 542) (RestInside.out (n := 542) f254 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 543) (ρ' := [(0, 512), (1, 459), (2, 540), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 542), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10884c) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 544) (RestInside.out (n := 544) f255 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 545) (ρ' := [(0, 512), (1, 459), (2, 540), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 544), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10884f) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 546) (RestInside.out (n := 546) f256 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 547) (ρ' := [(0, 512), (1, 459), (2, 540), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108852) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 548) (RestInside.out (n := 548) f257 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 549) (ρ' := [(0, 512), (1, 459), (2, 548), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108857) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 550) (RestInside.out (n := 550) f258 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 551) (ρ' := [(0, 512), (1, 459), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108859) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 552) (RestInside.out (n := 552) f259 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 553) (ρ' := [(0, 512), (1, 552), (2, 550), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 493), (13, 528), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10885c) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_13 code

theorem rest_l1084e0_11 [Bindings] (code : CodeMap) :
    Rest (n := 483) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (16, 477), (22, 22), (39, 39), (50, 50), (51, 51)]
      57 0x1087d9 bytes_l1084e0_11 b_l1084e0_11 := by
  have f220 : InstrSpec 0x1087d9 [0x0F, 0x93, 0x04, 0x24] (StorePre 0x1087d9 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087d9 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x1087d9 4 (.sib 4 none 0 .none)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x1087d9 4 (.sib 4 none 0 .none) 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1087d9 3 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f221 : InstrSpec 0x1087dd [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x1087dd) (movR64R64Effect 0x1087dd 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1087dd 2 4).toInstrSpec (mov_r64_r64_effect_step 0x1087dd 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f222 : InstrSpec 0x1087e0 [0x0F, 0xB6, 0x14, 0x24] (LoadPre 0x1087e0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087e0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1087e0 4 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1087e0 4 2 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x1087e0 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f223 : InstrSpec 0x1087e4 [0x83, 0xE2, 0x01] (fun s => s.RIP = 0x1087e4) (andR32Imm8Effect 0x1087e4 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1087e4 3 2 0x1).toInstrSpec (and_r32_imm8_effect_step 0x1087e4 0xe2 0x1 (by decide) (by decide)) pre_rip
  have f224 : InstrSpec 0x1087e7 [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x1087e7) (addR64R64Effect 0x1087e7 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1087e7 2 6).toInstrSpec (add_r64_r64_effect_step 0x1087e7 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f225 : InstrSpec 0x1087ea [0x88, 0x0C, 0x24] (StorePre 0x1087ea 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087ea + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1087ea 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1087ea 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x1087ea 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f226 : InstrSpec 0x1087ed [0x49, 0x89, 0xE7] (fun s => s.RIP = 0x1087ed) (movR64R64Effect 0x1087ed 15 4)
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1087ed 15 4).toInstrSpec (mov_r64_r64_effect_step 0x1087ed 0x49 0xe7 (by decide) (by decide)) pre_rip
  have f227 : InstrSpec 0x1087f0 [0x49, 0x31, 0xC4] (fun s => s.RIP = 0x1087f0) (xorR64R64Effect 0x1087f0 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1087f0 12 0).toInstrSpec (xor_r64_r64_effect_step 0x1087f0 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f228 : InstrSpec 0x1087f3 [0x0F, 0xB6, 0x34, 0x24] (LoadPre 0x1087f3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087f3 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1087f3 4 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1087f3 4 6 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x1087f3 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f229 : InstrSpec 0x1087f7 [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x1087f7) (negR64Effect 0x1087f7 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x1087f7 6).toInstrSpec (neg_r64_effect_step 0x1087f7 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f230 : InstrSpec 0x1087fa [0x4C, 0x21, 0xE6] (fun s => s.RIP = 0x1087fa) (andR64R64Effect 0x1087fa 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1087fa 6 12).toInstrSpec (and_r64_r64_effect_step 0x1087fa 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f231 : InstrSpec 0x1087fd [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x1087fd) (xorR64R64Effect 0x1087fd 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1087fd 6 0).toInstrSpec (xor_r64_r64_effect_step 0x1087fd 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f232 : InstrSpec 0x108800 [0x88, 0x0C, 0x24] (StorePre 0x108800 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108800 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108800 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108800 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x108800 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f233 : InstrSpec 0x108803 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x108803 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108803 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108803 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x108803 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x108803 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f234 : InstrSpec 0x108807 [0x4D, 0x31, 0xC6] (fun s => s.RIP = 0x108807) (xorR64R64Effect 0x108807 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108807 14 8).toInstrSpec (xor_r64_r64_effect_step 0x108807 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f235 : InstrSpec 0x10880a [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x10880a) (negR64Effect 0x10880a 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x10880a 0).toInstrSpec (neg_r64_effect_step 0x10880a 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f236 : InstrSpec 0x10880d [0x4C, 0x21, 0xF0] (fun s => s.RIP = 0x10880d) (andR64R64Effect 0x10880d 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10880d 0 14).toInstrSpec (and_r64_r64_effect_step 0x10880d 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f237 : InstrSpec 0x108810 [0x4C, 0x31, 0xC0] (fun s => s.RIP = 0x108810) (xorR64R64Effect 0x108810 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108810 0 8).toInstrSpec (xor_r64_r64_effect_step 0x108810 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f238 : InstrSpec 0x108813 [0x88, 0x0C, 0x24] (StorePre 0x108813 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108813 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108813 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108813 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x108813 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f239 : InstrSpec 0x108816 [0x44, 0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x108816 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108816 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108816 5 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x108816 5 8 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108816 0x44 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 483) (RestInside.exec (n := 483) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (16, 477), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087dd) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 484) (RestInside.exec (n := 484) (ρ' := [(0, 300), (1, 459), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (16, 477), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087e0) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 485) (RestInside.out (n := 485) f222 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 486) (ρ' := [(0, 300), (1, 459), (2, 485), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (16, 477), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087e4) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 487) (RestInside.out (n := 487) f223 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 488) (ρ' := [(0, 300), (1, 459), (2, 487), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087e7) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 489) (RestInside.out (n := 489) f224 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 490) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087ea) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 491) (RestInside.exec (n := 491) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087ed) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 492) (RestInside.exec (n := 492) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087f0) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 493) (RestInside.out (n := 493) f227 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 494) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087f3) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 495) (RestInside.out (n := 495) f228 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 496) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 495), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087f7) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 497) (RestInside.out (n := 497) f229 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 498) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 497), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087fa) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 499) (RestInside.out (n := 499) f230 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 500) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 499), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087fd) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 501) (RestInside.out (n := 501) f231 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 502) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108800) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 503) (RestInside.exec (n := 503) (ρ' := [(0, 300), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108803) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 504) (RestInside.out (n := 504) f233 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 505) (ρ' := [(0, 504), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108807) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 506) (RestInside.out (n := 506) f234 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 507) (ρ' := [(0, 504), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10880a) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 508) (RestInside.out (n := 508) f235 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 509) (ρ' := [(0, 508), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10880d) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 510) (RestInside.out (n := 510) f236 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 511) (ρ' := [(0, 510), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108810) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 512) (RestInside.out (n := 512) f237 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 513) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108813) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 514) (RestInside.exec (n := 514) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108816) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 515) (RestInside.out (n := 515) f239 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 516) (ρ' := [(0, 512), (1, 459), (2, 489), (3, 439), (4, 65), (5, 283), (6, 501), (7, 7), (8, 515), (9, 357), (10, 384), (11, 473), (12, 493), (13, 476), (14, 506), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10881b) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_12 code

theorem rest_l1084e0_10 [Bindings] (code : CodeMap) :
    Rest (n := 441) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 300), (1, 435), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]
      77 0x10878d bytes_l1084e0_10 b_l1084e0_10 := by
  have f200 : InstrSpec 0x10878d [0x48, 0x21, 0xD9] (fun s => s.RIP = 0x10878d) (andR64R64Effect 0x10878d 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10878d 1 3).toInstrSpec (and_r64_r64_effect_step 0x10878d 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f201 : InstrSpec 0x108790 [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x108790) (orR64R64Effect 0x108790 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108790 1 6).toInstrSpec (or_r64_r64_effect_step 0x108790 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f202 : InstrSpec 0x108793 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x108793) (shrR64Effect 0x108793 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x108793 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x108793 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f203 : InstrSpec 0x108797 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x108797 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108797 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108797 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108797 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x108797 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f204 : InstrSpec 0x10879b [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x10879b) (movR64R64Effect 0x10879b 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10879b 1 4).toInstrSpec (mov_r64_r64_effect_step 0x10879b 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f205 : InstrSpec 0x10879e [0x0F, 0xB6, 0x4C, 0x24, 0x10] (LoadPre 0x10879e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10879e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10879e 5 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10879e 5 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x10879e 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f206 : InstrSpec 0x1087a3 [0x80, 0xE1, 0x01] (fun s => s.RIP = 0x1087a3) (andR8Imm8Effect 0x1087a3 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x1087a3 3 1 0x1).toInstrSpec (and_r8_imm8_effect_step 0x1087a3 0xe1 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f207 : InstrSpec 0x1087a6 [0x48, 0x83, 0x3C, 0x24, 0x00] (LoadPre 0x1087a6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087a6 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x1087a6 5 64 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x1087a6 5 (.sib 4 none 0 .none) 0x0).toInstrSpec (cmp_m64_imm8_effect_step 0x1087a6 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  have f208 : InstrSpec 0x1087ab [0x0F, 0xB6, 0xC9] (fun s => s.RIP = 0x1087ab) (movzxR32R8Effect 0x1087ab 3 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x1087ab 3 1 1).toInstrSpec (movzx_r32_r8_effect_step 0x1087ab 0xc9 (by decide) (by decide)) pre_rip
  have f209 : InstrSpec 0x1087ae [0x41, 0xBD, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1087ae) (movR32Imm32Effect 0x1087ae 6 13 0x0)
      [] [] [.reg 13, .rip] :=
    (movR32Imm32Effect_footprint 0x1087ae 6 13 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1087ae 0x41 0xbd (by decide) (by decide) 0x0) pre_rip
  have f210 : InstrSpec 0x1087b4 [0x41, 0x0F, 0x44, 0xCD] (fun s => s.RIP = 0x1087b4) (atFlags (condHolds 4) (cmovR32R32Effect 0x1087b4 4 1 13))
      [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (cmovR32R32Effect_footprint 0x1087b4 4 1 13 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x1087b4 4 0x41 (by decide) 0xcd (by decide) c)) pre_rip
  have f211 : InstrSpec 0x1087b8 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x1087b8) (movR64R64Effect 0x1087b8 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1087b8 12 0).toInstrSpec (mov_r64_r64_effect_step 0x1087b8 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f212 : InstrSpec 0x1087bb [0x49, 0xF7, 0xDC] (fun s => s.RIP = 0x1087bb) (negR64Effect 0x1087bb 12)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (negR64Effect_footprint 0x1087bb 12).toInstrSpec (neg_r64_effect_step 0x1087bb 0x49 0xdc (by decide) (by decide) (by decide)) pre_rip
  have f213 : InstrSpec 0x1087be [0x41, 0xBE, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1087be) (movR32Imm32Effect 0x1087be 6 14 0x0)
      [] [] [.reg 14, .rip] :=
    (movR32Imm32Effect_footprint 0x1087be 6 14 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1087be 0x41 0xbe (by decide) (by decide) 0x0) pre_rip
  have f214 : InstrSpec 0x1087c4 [0x4D, 0x19, 0xC6] (fun s => s.RIP = 0x1087c4) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087c4 14 8))
      [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x1087c4 14 8).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x1087c4 0x4d 0xc6 c (by decide) (by decide))) pre_rip
  have f215 : InstrSpec 0x1087c7 [0x41, 0xBB, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1087c7) (movR32Imm32Effect 0x1087c7 6 11 0x0)
      [] [] [.reg 11, .rip] :=
    (movR32Imm32Effect_footprint 0x1087c7 6 11 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1087c7 0x41 0xbb (by decide) (by decide) 0x0) pre_rip
  have f216 : InstrSpec 0x1087cd [0x4D, 0x19, 0xCB] (fun s => s.RIP = 0x1087cd) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087cd 11 9))
      [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x1087cd 11 9).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x1087cd 0x4d 0xcb c (by decide) (by decide))) pre_rip
  have f217 : InstrSpec 0x1087d0 [0x4D, 0x19, 0xD5] (fun s => s.RIP = 0x1087d0) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087d0 13 10))
      [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x1087d0 13 10).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x1087d0 0x4d 0xd5 c (by decide) (by decide))) pre_rip
  have f218 : InstrSpec 0x1087d3 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1087d3) (movR64R64Effect 0x1087d3 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1087d3 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1087d3 0x48 0xde (by decide) (by decide)) pre_rip
  have f219 : InstrSpec 0x1087d6 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x1087d6) (notR64Effect 0x1087d6 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x1087d6 6).toInstrSpec (not_r64_effect_step 0x1087d6 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 441) (RestInside.out (n := 441) f200 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 442) (ρ' := [(0, 300), (1, 441), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108790) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 443) (RestInside.out (n := 443) f201 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 444) (ρ' := [(0, 300), (1, 443), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108793) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 445) (RestInside.out (n := 445) f202 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 446) (ρ' := [(0, 300), (1, 445), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108797) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 447) (RestInside.exec (n := 447) (ρ' := [(0, 300), (1, 445), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10879b) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 448) (RestInside.exec (n := 448) (ρ' := [(0, 300), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10879e) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 449) (RestInside.out (n := 449) f205 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 450) (ρ' := [(0, 300), (1, 449), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087a3) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 451) (RestInside.out (n := 451) f206 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 452) (ρ' := [(0, 300), (1, 451), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087a6) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 453) (RestInside.out (n := 453) f207 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 454) (ρ' := [(0, 300), (1, 451), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (19, 453), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087ab) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 455) (RestInside.out (n := 455) f208 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 456) (ρ' := [(0, 300), (1, 455), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (19, 453), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087ae) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 457) (RestInside.out (n := 457) f209 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 458) (ρ' := [(0, 300), (1, 455), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 457), (14, 423), (15, 294), (19, 453), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087b4) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 459) (RestInside.out (n := 459) f210 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 460) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 457), (14, 423), (15, 294), (19, 453), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087b8) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 461) (RestInside.out (n := 461) f211 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 462) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 461), (13, 457), (14, 423), (15, 294), (19, 453), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087bb) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 463) (RestInside.out (n := 463) f212 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 464) f212 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 465) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 463), (13, 457), (14, 423), (15, 294), (16, 464), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087be) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.out (n := 466) f213 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 467) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 463), (13, 457), (14, 466), (15, 294), (16, 464), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087c4) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 468) (RestInside.out (n := 468) f214 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 469) f214 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x1087c4 14 8 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 470) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 463), (13, 457), (14, 468), (15, 294), (16, 469), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087c7) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 471) (RestInside.out (n := 471) f215 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 472) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 471), (12, 463), (13, 457), (14, 468), (15, 294), (16, 469), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087cd) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 473) (RestInside.out (n := 473) f216 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 474) f216 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x1087cd 11 9 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 475) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 457), (14, 468), (15, 294), (16, 474), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087d0) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f217 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 477) f217 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x1087d0 13 10 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 478) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (16, 477), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087d3) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 479) (RestInside.out (n := 479) f218 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 480) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 479), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (16, 477), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087d6) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 481) (RestInside.out (n := 481) f219 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 482) (ρ' := [(0, 300), (1, 459), (2, 427), (3, 439), (4, 65), (5, 283), (6, 481), (7, 7), (8, 330), (9, 357), (10, 384), (11, 473), (12, 463), (13, 476), (14, 468), (15, 294), (16, 477), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1087d9) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_11 code

theorem rest_l1084e0_9 [Bindings] (code : CodeMap) :
    Rest (n := 401) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 300), (1, 156), (2, 390), (3, 398), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]
      97 0x10874b bytes_l1084e0_9 b_l1084e0_9 := by
  have f180 : InstrSpec 0x10874b [0x31, 0xDB] (fun s => s.RIP = 0x10874b) (xorR32R32Effect 0x10874b 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10874b 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x10874b 0xdb (by decide)) pre_rip
  have f181 : InstrSpec 0x10874d [0x48, 0x2B, 0x1C, 0x24] (LoadPre 0x10874d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10874d + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10874d 3 (.sib 4 none 0 .none))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10874d 3 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x10874d 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f182 : InstrSpec 0x108751 [0x4C, 0x8B, 0x5C, 0x24, 0x38] (LoadPre 0x108751 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108751 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108751 11 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x108751 11 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x108751 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f183 : InstrSpec 0x108756 [0x41, 0x83, 0xE3, 0x01] (fun s => s.RIP = 0x108756) (andR32Imm8Effect 0x108756 4 11 0x1)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x108756 4 11 0x1).toInstrSpec (and_r32_imm8_rex_effect_step 0x108756 0x41 0xe3 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f184 : InstrSpec 0x10875a [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x10875a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10875a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10875a 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10875a 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10875a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f185 : InstrSpec 0x10875f [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10875f) (movR64R64Effect 0x10875f 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10875f 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10875f 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x108762 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x108762) (notR64Effect 0x108762 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x108762 2).toInstrSpec (not_r64_effect_step 0x108762 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f187 : InstrSpec 0x108765 [0x4C, 0x01, 0xDA] (fun s => s.RIP = 0x108765) (addR64R64Effect 0x108765 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108765 2 11).toInstrSpec (add_r64_r64_effect_step 0x108765 0x4c 0xda (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x108768 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x108768) (xorR64R64Effect 0x108768 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108768 2 6).toInstrSpec (xor_r64_r64_effect_step 0x108768 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f189 : InstrSpec 0x10876b [0x49, 0xF7, 0xDE] (fun s => s.RIP = 0x10876b) (negR64Effect 0x10876b 14)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (negR64Effect_footprint 0x10876b 14).toInstrSpec (neg_r64_effect_step 0x10876b 0x49 0xde (by decide) (by decide) (by decide)) pre_rip
  have f190 : InstrSpec 0x10876e [0x49, 0x21, 0xD6] (fun s => s.RIP = 0x10876e) (andR64R64Effect 0x10876e 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10876e 14 2).toInstrSpec (and_r64_r64_effect_step 0x10876e 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x108771 [0x49, 0x31, 0xF6] (fun s => s.RIP = 0x108771) (xorR64R64Effect 0x108771 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108771 14 6).toInstrSpec (xor_r64_r64_effect_step 0x108771 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f192 : InstrSpec 0x108774 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x108774) (movR64R64Effect 0x108774 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108774 2 1).toInstrSpec (mov_r64_r64_effect_step 0x108774 0x48 0xca (by decide) (by decide)) pre_rip
  have f193 : InstrSpec 0x108777 [0x4C, 0x29, 0xF2] (fun s => s.RIP = 0x108777) (subR64R64Effect 0x108777 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108777 2 14).toInstrSpec (sub_r64_r64_effect_step 0x108777 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f194 : InstrSpec 0x10877a [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x10877a) (notR64Effect 0x10877a 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x10877a 1).toInstrSpec (not_r64_effect_step 0x10877a 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f195 : InstrSpec 0x10877d [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10877d) (movR64R64Effect 0x10877d 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10877d 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10877d 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f196 : InstrSpec 0x108780 [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x108780) (andR64R64Effect 0x108780 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108780 6 1).toInstrSpec (and_r64_r64_effect_step 0x108780 0x48 0xce (by decide) (by decide)) pre_rip
  have f197 : InstrSpec 0x108783 [0x4C, 0x09, 0xF1] (fun s => s.RIP = 0x108783) (orR64R64Effect 0x108783 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108783 1 14).toInstrSpec (or_r64_r64_effect_step 0x108783 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f198 : InstrSpec 0x108786 [0x48, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x108786) (sarR64Effect 0x108786 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (sarR64Effect_footprint 0x108786 4 3 63).toInstrSpec (sar_r64_imm8_effect_step 0x108786 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f199 : InstrSpec 0x10878a [0x48, 0x01, 0xD3] (fun s => s.RIP = 0x10878a) (addR64R64Effect 0x10878a 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10878a 3 2).toInstrSpec (add_r64_r64_effect_step 0x10878a 0x48 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 401) (RestInside.out (n := 401) f180 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 402) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 401), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10874d) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.out (n := 403) f181 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 404) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 403), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108751) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 405) (RestInside.out (n := 405) f182 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 406) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 403), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (11, 405), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108756) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 407) (RestInside.out (n := 407) f183 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 408) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 403), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10875a) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 409) (RestInside.out (n := 409) f184 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 410) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10875f) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 411) (RestInside.out (n := 411) f185 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 412) (ρ' := [(0, 300), (1, 156), (2, 411), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108762) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 413) (RestInside.out (n := 413) f186 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 414) (ρ' := [(0, 300), (1, 156), (2, 413), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108765) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 415) (RestInside.out (n := 415) f187 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 416) (ρ' := [(0, 300), (1, 156), (2, 415), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108768) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 417) (RestInside.out (n := 417) f188 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 418) (ρ' := [(0, 300), (1, 156), (2, 417), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10876b) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 419) (RestInside.out (n := 419) f189 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 420) (ρ' := [(0, 300), (1, 156), (2, 417), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 419), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10876e) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 421) (RestInside.out (n := 421) f190 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 422) (ρ' := [(0, 300), (1, 156), (2, 417), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 421), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108771) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 423) (RestInside.out (n := 423) f191 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 424) (ρ' := [(0, 300), (1, 156), (2, 417), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108774) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f192 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 426) (ρ' := [(0, 300), (1, 156), (2, 425), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108777) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 427) (RestInside.out (n := 427) f193 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 428) (ρ' := [(0, 300), (1, 156), (2, 427), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10877a) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 429) (RestInside.out (n := 429) f194 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 430) (ρ' := [(0, 300), (1, 429), (2, 427), (3, 403), (4, 65), (5, 283), (6, 409), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10877d) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 431) (RestInside.out (n := 431) f195 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 432) (ρ' := [(0, 300), (1, 429), (2, 427), (3, 403), (4, 65), (5, 283), (6, 431), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108780) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 433) (RestInside.out (n := 433) f196 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 434) (ρ' := [(0, 300), (1, 429), (2, 427), (3, 403), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108783) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 435) (RestInside.out (n := 435) f197 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 436) (ρ' := [(0, 300), (1, 435), (2, 427), (3, 403), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108786) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 437) (RestInside.out (n := 437) f198 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 438) (ρ' := [(0, 300), (1, 435), (2, 427), (3, 437), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10878a) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 439) (RestInside.out (n := 439) f199 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 440) (ρ' := [(0, 300), (1, 435), (2, 427), (3, 439), (4, 65), (5, 283), (6, 433), (7, 7), (8, 330), (9, 357), (10, 384), (11, 407), (12, 371), (13, 269), (14, 423), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10878d) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_10 code

theorem rest_l1084e0_8 [Bindings] (code : CodeMap) :
    Rest (n := 363) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 300), (1, 156), (2, 361), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 359), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]
      117 0x108709 bytes_l1084e0_8 b_l1084e0_8 := by
  have f160 : InstrSpec 0x108709 [0x4C, 0x21, 0xE2] (fun s => s.RIP = 0x108709) (andR64R64Effect 0x108709 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108709 2 12).toInstrSpec (and_r64_r64_effect_step 0x108709 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x10870c [0x49, 0x09, 0xEC] (fun s => s.RIP = 0x10870c) (orR64R64Effect 0x10870c 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10870c 12 5).toInstrSpec (or_r64_r64_effect_step 0x10870c 0x49 0xec (by decide) (by decide)) pre_rip
  have f162 : InstrSpec 0x10870f [0x4D, 0x21, 0xCC] (fun s => s.RIP = 0x10870f) (andR64R64Effect 0x10870f 12 9)
      [.gpr 12, .gpr 9] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10870f 12 9).toInstrSpec (and_r64_r64_effect_step 0x10870f 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f163 : InstrSpec 0x108712 [0x49, 0x09, 0xD4] (fun s => s.RIP = 0x108712) (orR64R64Effect 0x108712 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108712 12 2).toInstrSpec (or_r64_r64_effect_step 0x108712 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f164 : InstrSpec 0x108715 [0x49, 0xC1, 0xEC, 0x3F] (fun s => s.RIP = 0x108715) (shrR64Effect 0x108715 4 12 63)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64Effect_footprint 0x108715 4 12 63).toInstrSpec (shr_r64_imm8_effect_step 0x108715 0x49 0xec 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x108719 [0x4C, 0x89, 0x24, 0x24] (StorePre 0x108719 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108719 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108719 12 (.sib 4 none 0 .none))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108719 12 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x108719 0x4c (by decide) 4 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f166 : InstrSpec 0x10871d [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x10871d) (xorR32R32Effect 0x10871d 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10871d 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10871d 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x108720 [0x4C, 0x2B, 0x14, 0x24] (LoadPre 0x108720 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108720 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x108720 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108720 10 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x108720 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f168 : InstrSpec 0x108724 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x108724) (movR64R64Effect 0x108724 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108724 2 3).toInstrSpec (mov_r64_r64_effect_step 0x108724 0x48 0xda (by decide) (by decide)) pre_rip
  have f169 : InstrSpec 0x108727 [0x4C, 0x29, 0xFA] (fun s => s.RIP = 0x108727) (subR64R64Effect 0x108727 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108727 2 15).toInstrSpec (sub_r64_r64_effect_step 0x108727 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x10872a [0x49, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x10872a) (sarR64Effect 0x10872a 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (sarR64Effect_footprint 0x10872a 4 10 63).toInstrSpec (sar_r64_imm8_effect_step 0x10872a 0x49 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x10872e [0x49, 0x01, 0xD2] (fun s => s.RIP = 0x10872e) (addR64R64Effect 0x10872e 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10872e 10 2).toInstrSpec (add_r64_r64_effect_step 0x10872e 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f172 : InstrSpec 0x108731 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x108731) (notR64Effect 0x108731 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x108731 3).toInstrSpec (not_r64_effect_step 0x108731 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f173 : InstrSpec 0x108734 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x108734) (movR64R64Effect 0x108734 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108734 2 15).toInstrSpec (mov_r64_r64_effect_step 0x108734 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f174 : InstrSpec 0x108737 [0x48, 0x21, 0xDA] (fun s => s.RIP = 0x108737) (andR64R64Effect 0x108737 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108737 2 3).toInstrSpec (and_r64_r64_effect_step 0x108737 0x48 0xda (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x10873a [0x4C, 0x09, 0xFB] (fun s => s.RIP = 0x10873a) (orR64R64Effect 0x10873a 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10873a 3 15).toInstrSpec (or_r64_r64_effect_step 0x10873a 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f176 : InstrSpec 0x10873d [0x4C, 0x21, 0xD3] (fun s => s.RIP = 0x10873d) (andR64R64Effect 0x10873d 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10873d 3 10).toInstrSpec (and_r64_r64_effect_step 0x10873d 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x108740 [0x48, 0x09, 0xD3] (fun s => s.RIP = 0x108740) (orR64R64Effect 0x108740 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108740 3 2).toInstrSpec (or_r64_r64_effect_step 0x108740 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f178 : InstrSpec 0x108743 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x108743) (shrR64Effect 0x108743 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x108743 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x108743 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f179 : InstrSpec 0x108747 [0x48, 0x89, 0x1C, 0x24] (StorePre 0x108747 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108747 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108747 3 (.sib 4 none 0 .none))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108747 3 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x108747 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f160 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 364) (ρ' := [(0, 300), (1, 156), (2, 363), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 359), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10870c) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f161 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 300), (1, 156), (2, 363), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 365), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10870f) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f162 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 300), (1, 156), (2, 363), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 367), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108712) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f163 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 370) (ρ' := [(0, 300), (1, 156), (2, 363), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 369), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108715) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f164 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 300), (1, 156), (2, 363), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108719) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.exec (n := 373) (ρ' := [(0, 300), (1, 156), (2, 363), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10871d) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 374) (RestInside.out (n := 374) f166 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 375) (ρ' := [(0, 300), (1, 156), (2, 363), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 374), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108720) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f167 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 300), (1, 156), (2, 363), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 376), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108724) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f168 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 300), (1, 156), (2, 378), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 376), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108727) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f169 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 300), (1, 156), (2, 380), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 376), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10872a) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f170 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 300), (1, 156), (2, 380), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 382), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10872e) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.out (n := 384) f171 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 385) (ρ' := [(0, 300), (1, 156), (2, 380), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108731) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 386) (RestInside.out (n := 386) f172 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 387) (ρ' := [(0, 300), (1, 156), (2, 380), (3, 386), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108734) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.out (n := 388) f173 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 389) (ρ' := [(0, 300), (1, 156), (2, 388), (3, 386), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108737) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 390) (RestInside.out (n := 390) f174 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 391) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 386), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10873a) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 392) (RestInside.out (n := 392) f175 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 393) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 392), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10873d) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.out (n := 394) f176 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 395) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 394), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108740) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 396) (RestInside.out (n := 396) f177 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 397) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 396), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108743) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f178 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 398), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108747) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.exec (n := 400) (ρ' := [(0, 300), (1, 156), (2, 390), (3, 398), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 384), (12, 371), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10874b) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1084e0_9 code

theorem rest_l1084e0_7 [Bindings] (code : CodeMap) :
    Rest (n := 324) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 322), (9, 147), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]
      137 0x1086c8 bytes_l1084e0_7 b_l1084e0_7 := by
  have f140 : InstrSpec 0x1086c8 [0x4C, 0x89, 0xCA] (fun s => s.RIP = 0x1086c8) (movR64R64Effect 0x1086c8 2 9)
      [.gpr 9] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1086c8 2 9).toInstrSpec (mov_r64_r64_effect_step 0x1086c8 0x4c 0xca (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x1086cb [0x4C, 0x29, 0xEA] (fun s => s.RIP = 0x1086cb) (subR64R64Effect 0x1086cb 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1086cb 2 13).toInstrSpec (sub_r64_r64_effect_step 0x1086cb 0x4c 0xea (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x1086ce [0x49, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x1086ce) (sarR64Effect 0x1086ce 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (sarR64Effect_footprint 0x1086ce 4 8 63).toInstrSpec (sar_r64_imm8_effect_step 0x1086ce 0x49 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x1086d2 [0x49, 0x01, 0xD0] (fun s => s.RIP = 0x1086d2) (addR64R64Effect 0x1086d2 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1086d2 8 2).toInstrSpec (add_r64_r64_effect_step 0x1086d2 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x1086d5 [0x49, 0xF7, 0xD1] (fun s => s.RIP = 0x1086d5) (notR64Effect 0x1086d5 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR64Effect_footprint 0x1086d5 9).toInstrSpec (not_r64_effect_step 0x1086d5 0x49 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x1086d8 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1086d8) (movR64R64Effect 0x1086d8 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1086d8 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1086d8 0x4c 0xea (by decide) (by decide)) pre_rip
  have f146 : InstrSpec 0x1086db [0x4C, 0x21, 0xCA] (fun s => s.RIP = 0x1086db) (andR64R64Effect 0x1086db 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1086db 2 9).toInstrSpec (and_r64_r64_effect_step 0x1086db 0x4c 0xca (by decide) (by decide)) pre_rip
  have f147 : InstrSpec 0x1086de [0x4D, 0x09, 0xE9] (fun s => s.RIP = 0x1086de) (orR64R64Effect 0x1086de 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1086de 9 13).toInstrSpec (or_r64_r64_effect_step 0x1086de 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x1086e1 [0x4D, 0x21, 0xC1] (fun s => s.RIP = 0x1086e1) (andR64R64Effect 0x1086e1 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1086e1 9 8).toInstrSpec (and_r64_r64_effect_step 0x1086e1 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x1086e4 [0x49, 0x09, 0xD1] (fun s => s.RIP = 0x1086e4) (orR64R64Effect 0x1086e4 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1086e4 9 2).toInstrSpec (or_r64_r64_effect_step 0x1086e4 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x1086e7 [0x49, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x1086e7) (shrR64Effect 0x1086e7 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x1086e7 4 9 63).toInstrSpec (shr_r64_imm8_effect_step 0x1086e7 0x49 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x1086eb [0x4C, 0x89, 0x0C, 0x24] (StorePre 0x1086eb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086eb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1086eb 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1086eb 9 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1086eb 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f152 : InstrSpec 0x1086ef [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x1086ef) (xorR32R32Effect 0x1086ef 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1086ef 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1086ef 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f153 : InstrSpec 0x1086f2 [0x4C, 0x2B, 0x0C, 0x24] (LoadPre 0x1086f2 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086f2 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x1086f2 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1086f2 9 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x1086f2 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f154 : InstrSpec 0x1086f6 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x1086f6) (movR64R64Effect 0x1086f6 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1086f6 2 12).toInstrSpec (mov_r64_r64_effect_step 0x1086f6 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x1086f9 [0x48, 0x29, 0xEA] (fun s => s.RIP = 0x1086f9) (subR64R64Effect 0x1086f9 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1086f9 2 5).toInstrSpec (sub_r64_r64_effect_step 0x1086f9 0x48 0xea (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x1086fc [0x49, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x1086fc) (sarR64Effect 0x1086fc 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (sarR64Effect_footprint 0x1086fc 4 9 63).toInstrSpec (sar_r64_imm8_effect_step 0x1086fc 0x49 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x108700 [0x49, 0x01, 0xD1] (fun s => s.RIP = 0x108700) (addR64R64Effect 0x108700 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108700 9 2).toInstrSpec (add_r64_r64_effect_step 0x108700 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x108703 [0x49, 0xF7, 0xD4] (fun s => s.RIP = 0x108703) (notR64Effect 0x108703 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (notR64Effect_footprint 0x108703 12).toInstrSpec (not_r64_effect_step 0x108703 0x49 0xd4 (by decide) (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x108706 [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x108706) (movR64R64Effect 0x108706 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108706 2 5).toInstrSpec (mov_r64_r64_effect_step 0x108706 0x48 0xea (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f140 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 300), (1, 156), (2, 324), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 322), (9, 147), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086cb) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f141 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 300), (1, 156), (2, 326), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 322), (9, 147), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086ce) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f142 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 329) (ρ' := [(0, 300), (1, 156), (2, 326), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 328), (9, 147), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086d2) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f143 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 300), (1, 156), (2, 326), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 147), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086d5) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f144 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 300), (1, 156), (2, 326), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 332), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086d8) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f145 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 300), (1, 156), (2, 334), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 332), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086db) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f146 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 300), (1, 156), (2, 336), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 332), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086de) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f147 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 339) (ρ' := [(0, 300), (1, 156), (2, 336), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 338), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086e1) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 340) (RestInside.out (n := 340) f148 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 341) (ρ' := [(0, 300), (1, 156), (2, 336), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 340), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086e4) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f149 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 343) (ρ' := [(0, 300), (1, 156), (2, 336), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 342), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086e7) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f150 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 300), (1, 156), (2, 336), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 344), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086eb) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.exec (n := 346) (ρ' := [(0, 300), (1, 156), (2, 336), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 344), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086ef) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f152 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 300), (1, 156), (2, 336), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 347), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086f2) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f153 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 300), (1, 156), (2, 336), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 349), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086f6) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f154 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 300), (1, 156), (2, 351), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 349), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086f9) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f155 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 300), (1, 156), (2, 353), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 349), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086fc) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f156 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 300), (1, 156), (2, 353), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 355), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108700) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f157 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 300), (1, 156), (2, 353), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108703) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f158 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 300), (1, 156), (2, 353), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 359), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108706) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f159 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 300), (1, 156), (2, 361), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 330), (9, 357), (10, 314), (12, 359), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108709) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_8 code

theorem rest_l1084e0_6 [Bindings] (code : CodeMap) :
    Rest (n := 288) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 201), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]
      157 0x108684 bytes_l1084e0_6 b_l1084e0_6 := by
  have f120 : InstrSpec 0x108684 [0x44, 0x0F, 0xB6, 0x3C, 0x24] (LoadPre 0x108684 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108684 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108684 5 15 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x108684 5 15 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108684 0x44 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x108689 [0x49, 0xF7, 0xDF] (fun s => s.RIP = 0x108689) (negR64Effect 0x108689 15)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (negR64Effect_footprint 0x108689 15).toInstrSpec (neg_r64_effect_step 0x108689 0x49 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x10868c [0x49, 0x21, 0xD7] (fun s => s.RIP = 0x10868c) (andR64R64Effect 0x10868c 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10868c 15 2).toInstrSpec (and_r64_r64_effect_step 0x10868c 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x10868f [0x49, 0x31, 0xC7] (fun s => s.RIP = 0x10868f) (xorR64R64Effect 0x10868f 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10868f 15 0).toInstrSpec (xor_r64_r64_effect_step 0x10868f 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x108692 [0x44, 0x88, 0x1C, 0x24] (StorePre 0x108692 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108692 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108692 4 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108692 4 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x108692 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f125 : InstrSpec 0x108696 [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x108696) (movR64R64Effect 0x108696 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108696 0 4).toInstrSpec (mov_r64_r64_effect_step 0x108696 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x108699 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x108699) (movR64R64Effect 0x108699 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108699 0 10).toInstrSpec (mov_r64_r64_effect_step 0x108699 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x10869c [0x48, 0x29, 0xF0] (fun s => s.RIP = 0x10869c) (subR64R64Effect 0x10869c 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10869c 0 6).toInstrSpec (sub_r64_r64_effect_step 0x10869c 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x10869f [0x49, 0xF7, 0xD2] (fun s => s.RIP = 0x10869f) (notR64Effect 0x10869f 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (notR64Effect_footprint 0x10869f 10).toInstrSpec (not_r64_effect_step 0x10869f 0x49 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x1086a2 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x1086a2) (movR64R64Effect 0x1086a2 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1086a2 2 6).toInstrSpec (mov_r64_r64_effect_step 0x1086a2 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x1086a5 [0x4C, 0x21, 0xD2] (fun s => s.RIP = 0x1086a5) (andR64R64Effect 0x1086a5 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1086a5 2 10).toInstrSpec (and_r64_r64_effect_step 0x1086a5 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x1086a8 [0x49, 0x09, 0xF2] (fun s => s.RIP = 0x1086a8) (orR64R64Effect 0x1086a8 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1086a8 10 6).toInstrSpec (or_r64_r64_effect_step 0x1086a8 0x49 0xf2 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x1086ab [0x49, 0x21, 0xC2] (fun s => s.RIP = 0x1086ab) (andR64R64Effect 0x1086ab 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1086ab 10 0).toInstrSpec (and_r64_r64_effect_step 0x1086ab 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x1086ae [0x49, 0x09, 0xD2] (fun s => s.RIP = 0x1086ae) (orR64R64Effect 0x1086ae 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1086ae 10 2).toInstrSpec (or_r64_r64_effect_step 0x1086ae 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x1086b1 [0x49, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x1086b1) (shrR64Effect 0x1086b1 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x1086b1 4 10 63).toInstrSpec (shr_r64_imm8_effect_step 0x1086b1 0x49 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x1086b5 [0x44, 0x0F, 0xB6, 0x34, 0x24] (LoadPre 0x1086b5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086b5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1086b5 5 14 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1086b5 5 14 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1086b5 0x44 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f136 : InstrSpec 0x1086ba [0x4C, 0x89, 0x14, 0x24] (StorePre 0x1086ba 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086ba + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1086ba 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1086ba 10 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1086ba 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f137 : InstrSpec 0x1086be [0x49, 0x89, 0xE3] (fun s => s.RIP = 0x1086be) (movR64R64Effect 0x1086be 11 4)
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1086be 11 4).toInstrSpec (mov_r64_r64_effect_step 0x1086be 0x49 0xe3 (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x1086c1 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1086c1) (xorR32R32Effect 0x1086c1 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1086c1 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1086c1 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x1086c4 [0x4C, 0x2B, 0x04, 0x24] (LoadPre 0x1086c4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086c4 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x1086c4 8 (.sib 4 none 0 .none))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1086c4 8 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x1086c4 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f120 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 201), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (15, 288), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108689) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f121 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 201), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (15, 290), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10868c) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f122 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 201), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (15, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10868f) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f123 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 201), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108692) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.exec (n := 296) (ρ' := [(0, 201), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108696) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 297) (RestInside.exec (n := 297) (ρ' := [(1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108699) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f126 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 298), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10869c) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f127 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 300), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10869f) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f128 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 300), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 302), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086a2) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f129 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 300), (1, 156), (2, 304), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 302), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086a5) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f130 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 302), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086a8) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f131 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 308), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086ab) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f132 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 310), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086ae) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f133 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 312), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086b1) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f134 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 314), (11, 217), (12, 150), (13, 269), (14, 273), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086b5) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f135 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 314), (11, 217), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086ba) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.exec (n := 318) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 314), (11, 217), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086be) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 319) (RestInside.exec (n := 319) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086c1) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f138 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 320), (9, 147), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086c4) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f139 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 300), (1, 156), (2, 306), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 322), (9, 147), (10, 314), (12, 150), (13, 269), (14, 316), (15, 294), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1086c8) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_7 code

theorem rest_l1084e0_5 [Bindings] (code : CodeMap) :
    Rest (n := 252) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 250), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]
      177 0x108640 bytes_l1084e0_5 b_l1084e0_5 := by
  have f100 : InstrSpec 0x108640 [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x108640) (negR64Effect 0x108640 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x108640 6).toInstrSpec (neg_r64_effect_step 0x108640 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x108643 [0x4C, 0x21, 0xEE] (fun s => s.RIP = 0x108643) (andR64R64Effect 0x108643 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108643 6 13).toInstrSpec (and_r64_r64_effect_step 0x108643 0x4c 0xee (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x108646 [0x4C, 0x31, 0xF6] (fun s => s.RIP = 0x108646) (xorR64R64Effect 0x108646 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108646 6 14).toInstrSpec (xor_r64_r64_effect_step 0x108646 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x108649 [0x44, 0x88, 0x1C, 0x24] (StorePre 0x108649 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108649 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108649 4 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108649 4 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x108649 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f104 : InstrSpec 0x10864d [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x10864d) (movR64R64Effect 0x10864d 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10864d 14 4).toInstrSpec (mov_r64_r64_effect_step 0x10864d 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x108650 [0x4C, 0x31, 0xFD] (fun s => s.RIP = 0x108650) (xorR64R64Effect 0x108650 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108650 5 15).toInstrSpec (xor_r64_r64_effect_step 0x108650 0x4c 0xfd (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x108653 [0x44, 0x0F, 0xB6, 0x2C, 0x24] (LoadPre 0x108653 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108653 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108653 5 13 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108653 5 13 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108653 0x44 (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f107 : InstrSpec 0x108658 [0x49, 0xF7, 0xDD] (fun s => s.RIP = 0x108658) (negR64Effect 0x108658 13)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (negR64Effect_footprint 0x108658 13).toInstrSpec (neg_r64_effect_step 0x108658 0x49 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x10865b [0x49, 0x21, 0xED] (fun s => s.RIP = 0x10865b) (andR64R64Effect 0x10865b 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10865b 13 5).toInstrSpec (and_r64_r64_effect_step 0x10865b 0x49 0xed (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x10865e [0x4D, 0x31, 0xFD] (fun s => s.RIP = 0x10865e) (xorR64R64Effect 0x10865e 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10865e 13 15).toInstrSpec (xor_r64_r64_effect_step 0x10865e 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x108661 [0x44, 0x88, 0x1C, 0x24] (StorePre 0x108661 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108661 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108661 4 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108661 4 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x108661 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f111 : InstrSpec 0x108665 [0x4D, 0x89, 0xF7] (fun s => s.RIP = 0x108665) (movR64R64Effect 0x108665 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x108665 15 14).toInstrSpec (mov_r64_r64_effect_step 0x108665 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x108668 [0x4C, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x108668 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108668 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108668 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x108668 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x108668 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f113 : InstrSpec 0x10866d [0x4D, 0x31, 0xF0] (fun s => s.RIP = 0x10866d) (xorR64R64Effect 0x10866d 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10866d 8 14).toInstrSpec (xor_r64_r64_effect_step 0x10866d 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x108670 [0x0F, 0xB6, 0x2C, 0x24] (LoadPre 0x108670 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108670 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108670 4 5 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x108670 4 5 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x108670 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f115 : InstrSpec 0x108674 [0x48, 0xF7, 0xDD] (fun s => s.RIP = 0x108674) (negR64Effect 0x108674 5)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (negR64Effect_footprint 0x108674 5).toInstrSpec (neg_r64_effect_step 0x108674 0x48 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x108677 [0x4C, 0x21, 0xC5] (fun s => s.RIP = 0x108677) (andR64R64Effect 0x108677 5 8)
      [.gpr 5, .gpr 8] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108677 5 8).toInstrSpec (and_r64_r64_effect_step 0x108677 0x4c 0xc5 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x10867a [0x4C, 0x31, 0xF5] (fun s => s.RIP = 0x10867a) (xorR64R64Effect 0x10867a 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10867a 5 14).toInstrSpec (xor_r64_r64_effect_step 0x10867a 0x4c 0xf5 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x10867d [0x44, 0x88, 0x1C, 0x24] (StorePre 0x10867d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10867d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10867d 4 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10867d 4 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x10867d 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f119 : InstrSpec 0x108681 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x108681) (xorR64R64Effect 0x108681 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108681 2 0).toInstrSpec (xor_r64_r64_effect_step 0x108681 0x48 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f100 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 252), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108643) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f101 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 254), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108646) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f102 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108649) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.exec (n := 258) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10864d) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f104 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 259), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108650) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f105 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 259), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108653) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f106 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 263), (14, 259), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108658) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f107 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 265), (14, 259), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10865b) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f108 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 267), (14, 259), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10865e) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.out (n := 269) f109 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 270) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 259), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108661) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.exec (n := 271) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 259), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108665) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 272) (RestInside.exec (n := 272) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108668) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f112 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10866d) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f113 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 261), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108670) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f114 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 277), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108674) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f115 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 279), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108677) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.out (n := 281) f116 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 282) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 281), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10867a) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f117 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10867d) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.exec (n := 285) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108681) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f119 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 201), (1, 156), (2, 286), (3, 153), (4, 65), (5, 283), (6, 256), (7, 7), (8, 275), (9, 147), (10, 102), (11, 217), (12, 150), (13, 269), (14, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108684) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_6 code

theorem rest_l1084e0_4 [Bindings] (code : CodeMap) :
    Rest (n := 214) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 212), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]
      197 0x1085f2 bytes_l1084e0_4 b_l1084e0_4 := by
  have f80 : InstrSpec 0x1085f2 [0x45, 0x30, 0xC3] (fun s => s.RIP = 0x1085f2) (xorR8R8Effect 0x1085f2 3 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (xorR8R8Effect_footprint 0x1085f2 3 11 8).toInstrSpec (xor_r8_r8_rex_effect_step 0x1085f2 0x45 0xc3 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x1085f5 [0x44, 0x88, 0x5C, 0x24, 0x10] (StorePre 0x1085f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1085f5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1085f5 5 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1085f5 5 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1085f5 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f82 : InstrSpec 0x1085fa [0x41, 0x80, 0xF3, 0x01] (fun s => s.RIP = 0x1085fa) (xorR8Imm8Effect 0x1085fa 4 11 0x1)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR8Imm8Effect_footprint 0x1085fa 4 11 0x1).toInstrSpec (xor_r8_imm8_rex_effect_step 0x1085fa 0x41 0xf3 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x1085fe [0x4C, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x1085fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1085fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085fe 14 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1085fe 14 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1085fe 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f84 : InstrSpec 0x108603 [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x108603) (movR64R64Effect 0x108603 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x108603 13 14).toInstrSpec (mov_r64_r64_effect_step 0x108603 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x108606 [0x49, 0xF7, 0xDD] (fun s => s.RIP = 0x108606) (negR64Effect 0x108606 13)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (negR64Effect_footprint 0x108606 13).toInstrSpec (neg_r64_effect_step 0x108606 0x49 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x108609 [0xBD, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108609) (movR32Imm32Effect 0x108609 5 5 0x0)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x108609 5 5 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x108609 0xbd (by decide) 0x0) pre_rip
  have f87 : InstrSpec 0x10860e [0x4C, 0x19, 0xFD] (fun s => s.RIP = 0x10860e) (atFlags StatusFlags.CF (sbbR64R64Effect 0x10860e 5 15))
      [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x10860e 5 15).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x10860e 0x4c 0xfd c (by decide) (by decide))) pre_rip
  have f88 : InstrSpec 0x108611 [0x41, 0xB8, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108611) (movR32Imm32Effect 0x108611 6 8 0x0)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x108611 6 8 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x108611 0x41 0xb8 (by decide) (by decide) 0x0) pre_rip
  have f89 : InstrSpec 0x108617 [0x49, 0x19, 0xF0] (fun s => s.RIP = 0x108617) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108617 8 6))
      [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x108617 8 6).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x108617 0x49 0xf0 c (by decide) (by decide))) pre_rip
  have f90 : InstrSpec 0x10861a [0xBA, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10861a) (movR32Imm32Effect 0x10861a 5 2 0x0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10861a 5 2 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x10861a 0xba (by decide) 0x0) pre_rip
  have f91 : InstrSpec 0x10861f [0x48, 0x19, 0xC2] (fun s => s.RIP = 0x10861f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x10861f 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x10861f 2 0).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x10861f 0x48 0xc2 c (by decide) (by decide))) pre_rip
  have f92 : InstrSpec 0x108622 [0x0F, 0x93, 0x04, 0x24] (StorePre 0x108622 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108622 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x108622 4 (.sib 4 none 0 .none)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x108622 4 (.sib 4 none 0 .none) 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x108622 3 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f93 : InstrSpec 0x108626 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x108626) (movR64R64Effect 0x108626 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108626 6 4).toInstrSpec (mov_r64_r64_effect_step 0x108626 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x108629 [0x0F, 0xB6, 0x34, 0x24] (LoadPre 0x108629 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108629 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108629 4 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x108629 4 6 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x108629 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f95 : InstrSpec 0x10862d [0x48, 0x89, 0x74, 0x24, 0x38] (StorePre 0x10862d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10862d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10862d 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10862d 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10862d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x108632 [0x44, 0x88, 0x1C, 0x24] (StorePre 0x108632 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108632 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108632 4 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108632 4 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x108632 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f97 : InstrSpec 0x108636 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x108636) (movR64R64Effect 0x108636 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108636 6 4).toInstrSpec (mov_r64_r64_effect_step 0x108636 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x108639 [0x4D, 0x31, 0xF5] (fun s => s.RIP = 0x108639) (xorR64R64Effect 0x108639 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108639 13 14).toInstrSpec (xor_r64_r64_effect_step 0x108639 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x10863c [0x0F, 0xB6, 0x34, 0x24] (LoadPre 0x10863c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10863c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10863c 4 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10863c 4 6 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x10863c 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f80 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 214), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085f5) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.exec (n := 216) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 214), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085fa) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f82 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 217), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085fe) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f83 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 217), (12, 150), (13, 145), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108603) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f84 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 217), (12, 150), (13, 221), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108606) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f85 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 224) f85 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 225) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 224), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108609) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f86 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 226), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 224), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10860e) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f87 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 229) f87 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x10860e 5 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 230) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 228), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 229), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108611) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f88 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 228), (6, 198), (7, 7), (8, 231), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 229), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108617) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f89 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 234) f89 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x108617 8 6 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 235) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 228), (6, 198), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 234), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10861a) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f90 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 201), (1, 156), (2, 236), (3, 153), (4, 65), (5, 228), (6, 198), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 234), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10861f) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f91 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 239) f91 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x10861f 2 0 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 240) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 198), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108622) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.exec (n := 241) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 198), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108626) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 242) (RestInside.exec (n := 242) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108629) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f94 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 243), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10862d) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.exec (n := 245) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 243), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108632) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 246) (RestInside.exec (n := 246) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 243), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108636) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 247) (RestInside.exec (n := 247) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 223), (14, 219), (15, 192), (16, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108639) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f98 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10863c) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f99 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 201), (1, 156), (2, 238), (3, 153), (4, 65), (5, 228), (6, 250), (7, 7), (8, 233), (9, 147), (10, 102), (11, 217), (12, 150), (13, 248), (14, 219), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108640) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_5 code

theorem rest_l1084e0_3 [Bindings] (code : CodeMap) :
    Rest (n := 173) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 167), (1, 156), (2, 168), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]
      217 0x1085a1 bytes_l1084e0_3 b_l1084e0_3 := by
  have f60 : InstrSpec 0x1085a1 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1085a1) (movR64R64Effect 0x1085a1 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1085a1 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1085a1 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x1085a4 [0x49, 0xF7, 0x63, 0x10] (LoadPre 0x1085a4 (fun s => AddrMode.addr (.base 11 (.d8 0x10)) s (0x1085a4 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1085a4 4 (.base 11 (.d8 0x10)))
      [.gpr 0, .gpr 11] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x1085a4 4 (.base 11 (.d8 0x10))).toInstrSpec (mul_m64_effect_step 0x1085a4 0x49 (by decide) (.base 11 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x1085a8 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x1085a8) (movR64R64Effect 0x1085a8 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1085a8 14 0).toInstrSpec (mov_r64_r64_effect_step 0x1085a8 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x1085ab [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x1085ab) (movR64R64Effect 0x1085ab 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1085ab 5 2).toInstrSpec (mov_r64_r64_effect_step 0x1085ab 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x1085ae [0x4C, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1085ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1085ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085ae 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1085ae 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1085ae 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f65 : InstrSpec 0x1085b3 [0x44, 0x32, 0x46, 0x20] (LoadPre 0x1085b3 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1085b3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1085b3 4 8 (.base 6 (.d8 0x20)))
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1085b3 4 8 (.base 6 (.d8 0x20))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1085b3 0x44 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x1085b7 [0x4C, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1085b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1085b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085b7 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085b7 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1085b7 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x1085bc [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1085bc) (movR64R64Effect 0x1085bc 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1085bc 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1085bc 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x1085bf [0x49, 0xF7, 0x63, 0x18] (LoadPre 0x1085bf (fun s => AddrMode.addr (.base 11 (.d8 0x18)) s (0x1085bf + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1085bf 4 (.base 11 (.d8 0x18)))
      [.gpr 0, .gpr 11] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x1085bf 4 (.base 11 (.d8 0x18))).toInstrSpec (mul_m64_effect_step 0x1085bf 0x49 (by decide) (.base 11 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f69 : InstrSpec 0x1085c3 [0x4C, 0x03, 0x7C, 0x24, 0x10] (LoadPre 0x1085c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1085c3 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1085c3 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (addR64M64Effect_footprint 0x1085c3 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (add_r64_m64_effect_step 0x1085c3 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f70 : InstrSpec 0x1085c8 [0x4C, 0x13, 0x74, 0x24, 0x08] (LoadPre 0x1085c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1085c8 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1085c8 14 (.sib 4 none 0 (.d8 0x8))))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x1085c8 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x1085c8 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x1085cd [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1085cd) (movR64R64Effect 0x1085cd 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1085cd 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1085cd 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x1085d0 [0x4C, 0x89, 0x74, 0x24, 0x30] (StorePre 0x1085d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1085d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085d0 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085d0 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1085d0 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x1085d5 [0x48, 0x11, 0xE8] (fun s => s.RIP = 0x1085d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1085d5 0 5))
      [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1085d5 0 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1085d5 0x48 0xe8 c (by decide) (by decide))) pre_rip
  have f74 : InstrSpec 0x1085d8 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x1085d8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1085d8 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1085d8 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1085d8 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f75 : InstrSpec 0x1085dc [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x1085dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1085dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085dc 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085dc 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1085dc 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x1085e1 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x1085e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1085e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085e1 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1085e1 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1085e1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f77 : InstrSpec 0x1085e6 [0x41, 0x32, 0x53, 0x20] (LoadPre 0x1085e6 (fun s => AddrMode.addr (.base 11 (.d8 0x20)) s (0x1085e6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1085e6 4 2 (.base 11 (.d8 0x20)))
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1085e6 4 2 (.base 11 (.d8 0x20))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1085e6 0x41 (by decide) 2 (.base 11 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f78 : InstrSpec 0x1085ea [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x1085ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1085ea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085ea 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1085ea 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1085ea 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f79 : InstrSpec 0x1085ef [0x41, 0x89, 0xD3] (fun s => s.RIP = 0x1085ef) (movR32R32Effect 0x1085ef 3 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1085ef 3 11 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x1085ef 0x41 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 173), (1, 156), (2, 168), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085a4) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f61 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 176) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 177) (ρ' := [(0, 175), (1, 156), (2, 176), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085a8) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f62 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 175), (1, 156), (2, 176), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 178), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085ab) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f63 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 175), (1, 156), (2, 176), (3, 153), (4, 65), (5, 180), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 178), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085ae) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f64 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 175), (1, 156), (2, 176), (3, 153), (4, 65), (5, 180), (6, 6), (7, 7), (8, 182), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 178), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085b3) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f65 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 175), (1, 156), (2, 176), (3, 153), (4, 65), (5, 180), (6, 6), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 178), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085b7) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 175), (1, 156), (2, 176), (3, 153), (4, 65), (5, 180), (6, 6), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 178), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085bc) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 187), (1, 156), (2, 176), (3, 153), (4, 65), (5, 180), (6, 6), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 178), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085bf) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f68 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 190) f68 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 191) (ρ' := [(0, 189), (1, 156), (2, 190), (3, 153), (4, 65), (5, 180), (6, 6), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 178), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085c3) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f69 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 193) f69 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 194) (ρ' := [(0, 189), (1, 156), (2, 190), (3, 153), (4, 65), (5, 180), (6, 6), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 178), (15, 192), (16, 193), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085c8) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f70 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 196) f70 .CF (fun _ => rfl) (adcR64M64Effect_fresh 0x1085c8 14 (.sib 4 none 0 (.d8 0x8)) _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 197) (ρ' := [(0, 189), (1, 156), (2, 190), (3, 153), (4, 65), (5, 180), (6, 6), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (16, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085cd) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f71 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 189), (1, 156), (2, 190), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (16, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085d0) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.exec (n := 200) (ρ' := [(0, 189), (1, 156), (2, 190), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (16, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085d5) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f73 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 202) f73 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1085d5 0 5 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 203) (ρ' := [(0, 201), (1, 156), (2, 190), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (16, 202), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085d8) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f74 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 201), (1, 156), (2, 204), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085dc) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.exec (n := 206) (ρ' := [(0, 201), (1, 156), (2, 204), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085e1) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 201), (1, 156), (2, 207), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085e6) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f77 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085ea) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.exec (n := 211) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085ef) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f79 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 201), (1, 156), (2, 209), (3, 153), (4, 65), (5, 180), (6, 198), (7, 7), (8, 184), (9, 147), (10, 102), (11, 212), (12, 150), (13, 145), (14, 195), (15, 192), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085f2) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_4 code

theorem rest_l1084e0_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 125), (1, 121), (2, 126), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 119), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]
      237 0x10855c bytes_l1084e0_2 b_l1084e0_2 := by
  have f40 : InstrSpec 0x10855c [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x10855c) (movR64R64Effect 0x10855c 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10855c 5 2).toInstrSpec (mov_r64_r64_effect_step 0x10855c 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10855f [0x49, 0xF7, 0xDD] (fun s => s.RIP = 0x10855f) (negR64Effect 0x10855f 13)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (negR64Effect_footprint 0x10855f 13).toInstrSpec (neg_r64_effect_step 0x10855f 0x49 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x108562 [0x49, 0x21, 0xCD] (fun s => s.RIP = 0x108562) (andR64R64Effect 0x108562 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108562 13 1).toInstrSpec (and_r64_r64_effect_step 0x108562 0x49 0xcd (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x108565 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x108565) (movR64R64Effect 0x108565 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108565 0 3).toInstrSpec (mov_r64_r64_effect_step 0x108565 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x108568 [0x48, 0xF7, 0x66, 0x18] (LoadPre 0x108568 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108568 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108568 4 (.base 6 (.d8 0x18)))
      [.gpr 0, .gpr 6] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x108568 4 (.base 6 (.d8 0x18))).toInstrSpec (mul_m64_effect_step 0x108568 0x48 (by decide) (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x10856c [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x10856c) (movR64R64Effect 0x10856c 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10856c 3 0).toInstrSpec (mov_r64_r64_effect_step 0x10856c 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10856f [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10856f) (movR64R64Effect 0x10856f 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10856f 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10856f 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x108572 [0x4D, 0x31, 0xC5] (fun s => s.RIP = 0x108572) (xorR64R64Effect 0x108572 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108572 13 8).toInstrSpec (xor_r64_r64_effect_step 0x108572 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x108575 [0x4D, 0x01, 0xF1] (fun s => s.RIP = 0x108575) (addR64R64Effect 0x108575 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108575 9 14).toInstrSpec (add_r64_r64_effect_step 0x108575 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x108578 [0x4D, 0x11, 0xFC] (fun s => s.RIP = 0x108578) (atFlags StatusFlags.CF (adcR64R64Effect 0x108578 12 15))
      [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x108578 12 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x108578 0x4d 0xfc c (by decide) (by decide))) pre_rip
  have f50 : InstrSpec 0x10857b [0x48, 0x11, 0xEB] (fun s => s.RIP = 0x10857b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10857b 3 5))
      [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10857b 3 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10857b 0x48 0xeb c (by decide) (by decide))) pre_rip
  have f51 : InstrSpec 0x10857e [0x48, 0x83, 0xD1, 0x00] (fun s => s.RIP = 0x10857e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10857e 1 0x0))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10857e 1 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10857e 0x48 0xd1 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f52 : InstrSpec 0x108582 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x108582) (movR64R64Effect 0x108582 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108582 0 13).toInstrSpec (mov_r64_r64_effect_step 0x108582 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x108585 [0x49, 0xF7, 0x23] (LoadPre 0x108585 (fun s => AddrMode.addr (.base 11 .none) s (0x108585 + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x108585 3 (.base 11 .none))
      [.gpr 0, .gpr 11] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x108585 3 (.base 11 .none)).toInstrSpec (mul_m64_effect_step 0x108585 0x49 (by decide) (.base 11 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x108588 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x108588 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108588 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108588 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108588 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108588 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x10858d [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x10858d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10858d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10858d 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10858d 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10858d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x108592 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x108592) (movR64R64Effect 0x108592 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108592 0 13).toInstrSpec (mov_r64_r64_effect_step 0x108592 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x108595 [0x49, 0xF7, 0x63, 0x08] (LoadPre 0x108595 (fun s => AddrMode.addr (.base 11 (.d8 0x8)) s (0x108595 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108595 4 (.base 11 (.d8 0x8)))
      [.gpr 0, .gpr 11] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x108595 4 (.base 11 (.d8 0x8))).toInstrSpec (mul_m64_effect_step 0x108595 0x49 (by decide) (.base 11 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x108599 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x108599 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108599 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108599 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108599 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108599 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x10859e [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x10859e) (movR64R64Effect 0x10859e 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10859e 15 0).toInstrSpec (mov_r64_r64_effect_step 0x10859e 0x49 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 125), (1, 121), (2, 126), (3, 88), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 119), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10855f) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 125), (1, 121), (2, 126), (3, 88), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 132), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108562) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 125), (1, 121), (2, 126), (3, 88), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 134), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108565) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 136), (1, 121), (2, 126), (3, 88), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 134), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108568) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 139) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 140) (ρ' := [(0, 138), (1, 121), (2, 139), (3, 88), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 134), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10856c) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f45 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 138), (1, 121), (2, 139), (3, 141), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 134), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10856f) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 138), (1, 143), (2, 139), (3, 141), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 134), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108572) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f47 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 138), (1, 143), (2, 139), (3, 141), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108575) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f48 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 148) f48 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 149) (ρ' := [(0, 138), (1, 143), (2, 139), (3, 141), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 128), (13, 145), (14, 104), (15, 117), (16, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108578) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f49 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 151) f49 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x108578 12 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 152) (ρ' := [(0, 138), (1, 143), (2, 139), (3, 141), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (16, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10857b) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f50 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 154) f50 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x10857b 3 5 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 155) (ρ' := [(0, 138), (1, 143), (2, 139), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (16, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10857e) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 138), (1, 156), (2, 139), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108582) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 158), (1, 156), (2, 139), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108585) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 161) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 162) (ρ' := [(0, 160), (1, 156), (2, 161), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108588) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.exec (n := 163) (ρ' := [(0, 160), (1, 156), (2, 161), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10858d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 164) (RestInside.exec (n := 164) (ρ' := [(0, 160), (1, 156), (2, 161), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108592) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f56 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 165), (1, 156), (2, 161), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108595) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f57 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 168) f57 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 169) (ρ' := [(0, 167), (1, 156), (2, 168), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108599) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.exec (n := 170) (ρ' := [(0, 167), (1, 156), (2, 168), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10859e) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f59 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 167), (1, 156), (2, 168), (3, 153), (4, 65), (5, 130), (6, 6), (7, 7), (8, 8), (9, 147), (10, 102), (11, 67), (12, 150), (13, 145), (14, 104), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1085a1) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_3 code

theorem rest_l1084e0_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x1084e0 bytes_l1084e0) [(0, 82), (1, 1), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      257 0x108519 bytes_l1084e0_1 b_l1084e0_1 := by
  have f20 : InstrSpec 0x108519 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x108519) (movR64R64Effect 0x108519 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108519 0 8).toInstrSpec (mov_r64_r64_effect_step 0x108519 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10851c [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x10851c) (shrR64Effect 0x10851c 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10851c 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x10851c 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x108520 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x108520 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108520 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108520 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108520 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x108520 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x108525 [0x88, 0x04, 0x24] (StorePre 0x108525 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108525 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108525 3 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108525 3 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x108525 0 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x108528 [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x108528) (movR64R64Effect 0x108528 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108528 0 4).toInstrSpec (mov_r64_r64_effect_step 0x108528 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10852b [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10852b) (movR64R64Effect 0x10852b 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10852b 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10852b 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10852e [0x48, 0xF7, 0x26] (LoadPre 0x10852e (fun s => AddrMode.addr (.base 6 .none) s (0x10852e + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x10852e 3 (.base 6 .none))
      [.gpr 0, .gpr 6] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10852e 3 (.base 6 .none)).toInstrSpec (mul_m64_effect_step 0x10852e 0x48 (by decide) (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x108531 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x108531) (movR64R64Effect 0x108531 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x108531 10 0).toInstrSpec (mov_r64_r64_effect_step 0x108531 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x108534 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x108534) (movR64R64Effect 0x108534 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x108534 14 2).toInstrSpec (mov_r64_r64_effect_step 0x108534 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x108537 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x108537) (movR64R64Effect 0x108537 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x108537 1 8).toInstrSpec (mov_r64_r64_effect_step 0x108537 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10853a [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x10853a) (negR64Effect 0x10853a 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x10853a 1).toInstrSpec (neg_r64_effect_step 0x10853a 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10853d [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10853d) (movR64R64Effect 0x10853d 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10853d 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10853d 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x108540 [0x48, 0xF7, 0x66, 0x08] (LoadPre 0x108540 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108540 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108540 4 (.base 6 (.d8 0x8)))
      [.gpr 0, .gpr 6] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x108540 4 (.base 6 (.d8 0x8))).toInstrSpec (mul_m64_effect_step 0x108540 0x48 (by decide) (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x108544 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x108544) (movR64R64Effect 0x108544 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x108544 9 0).toInstrSpec (mov_r64_r64_effect_step 0x108544 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x108547 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x108547) (movR64R64Effect 0x108547 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x108547 15 2).toInstrSpec (mov_r64_r64_effect_step 0x108547 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10854a [0x44, 0x0F, 0xB6, 0x2C, 0x24] (LoadPre 0x10854a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10854a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10854a 5 13 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x10854a 5 13 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10854a 0x44 (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x10854f [0x4C, 0x31, 0xC1] (fun s => s.RIP = 0x10854f) (xorR64R64Effect 0x10854f 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10854f 1 8).toInstrSpec (xor_r64_r64_effect_step 0x10854f 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x108552 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x108552) (movR64R64Effect 0x108552 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108552 0 3).toInstrSpec (mov_r64_r64_effect_step 0x108552 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x108555 [0x48, 0xF7, 0x66, 0x10] (LoadPre 0x108555 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108555 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108555 4 (.base 6 (.d8 0x10)))
      [.gpr 0, .gpr 6] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x108555 4 (.base 6 (.d8 0x10))).toInstrSpec (mul_m64_effect_step 0x108555 0x48 (by decide) (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x108559 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x108559) (movR64R64Effect 0x108559 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x108559 12 0).toInstrSpec (mov_r64_r64_effect_step 0x108559 0x49 0xc4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 1), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10851c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 1), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108520) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 92), (1, 1), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108525) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 92), (1, 1), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108528) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(1, 1), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10852b) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 97), (1, 1), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10852e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 99), (1, 1), (2, 100), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108531) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f27 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 99), (1, 1), (2, 100), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (10, 102), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108534) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f28 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 99), (1, 1), (2, 100), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (10, 102), (11, 67), (12, 12), (13, 13), (14, 104), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108537) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 99), (1, 106), (2, 100), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (10, 102), (11, 67), (12, 12), (13, 13), (14, 104), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10853a) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 99), (1, 108), (2, 100), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (10, 102), (11, 67), (12, 12), (13, 13), (14, 104), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10853d) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 110), (1, 108), (2, 100), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (10, 102), (11, 67), (12, 12), (13, 13), (14, 104), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108540) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f32 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 113) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 114) (ρ' := [(0, 112), (1, 108), (2, 113), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (10, 102), (11, 67), (12, 12), (13, 13), (14, 104), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108544) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 112), (1, 108), (2, 113), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 12), (13, 13), (14, 104), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108547) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 112), (1, 108), (2, 113), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 12), (13, 13), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10854a) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 112), (1, 108), (2, 113), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 12), (13, 119), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10854f) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 112), (1, 121), (2, 113), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 12), (13, 119), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108552) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 123), (1, 121), (2, 113), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 12), (13, 119), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108555) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 126) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 127) (ρ' := [(0, 125), (1, 121), (2, 126), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 12), (13, 119), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108559) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 125), (1, 121), (2, 126), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 115), (10, 102), (11, 67), (12, 128), (13, 119), (14, 104), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10855c) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_2 code

theorem rest_l1084e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1084e0 bytes_l1084e0) (entryMap (live .l1084e0))
      277 0x1084e0 bytes_l1084e0 b_l1084e0 := by
  have f0 : InstrSpec 0x1084e0 [0x55] (PushPre 0x1084e0 1) (pushR64Effect 0x1084e0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e0 1 5).toInstrSpec (push_r64_effect_step 0x1084e0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1084e1 [0x41, 0x57] (PushPre 0x1084e1 2) (pushR64Effect 0x1084e1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1084e1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1084e3 [0x41, 0x56] (PushPre 0x1084e3 2) (pushR64Effect 0x1084e3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1084e3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1084e5 [0x41, 0x55] (PushPre 0x1084e5 2) (pushR64Effect 0x1084e5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1084e5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1084e7 [0x41, 0x54] (PushPre 0x1084e7 2) (pushR64Effect 0x1084e7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1084e7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1084e9 [0x53] (PushPre 0x1084e9 1) (pushR64Effect 0x1084e9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1084e9 1 3).toInstrSpec (push_r64_effect_step 0x1084e9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1084ea [0x48, 0x83, 0xEC, 0x40] (fun s => s.RIP = 0x1084ea) (subR64Imm8Effect 0x1084ea 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1084ea 4 0x40).toInstrSpec (sub_r64_imm8_effect_step 0x1084ea 0x48 0xec 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1084ee [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x1084ee) (movR64R64Effect 0x1084ee 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1084ee 11 2).toInstrSpec (mov_r64_r64_effect_step 0x1084ee 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1084f1 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x1084f1) (movR64R64Effect 0x1084f1 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1084f1 2 1).toInstrSpec (mov_r64_r64_effect_step 0x1084f1 0x48 0xca (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1084f4 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x1084f4) (shrR64Effect 0x1084f4 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x1084f4 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x1084f4 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1084f8 [0x48, 0x89, 0x54, 0x24, 0x20] (StorePre 0x1084f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1084f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1084f8 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1084f8 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1084f8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1084fd [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1084fd) (movR64R64Effect 0x1084fd 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1084fd 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1084fd 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x108500 [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x108500) (negR64Effect 0x108500 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x108500 0).toInstrSpec (neg_r64_effect_step 0x108500 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x108503 [0x88, 0x14, 0x24] (StorePre 0x108503 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108503 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108503 3 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108503 3 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x108503 2 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x108506 [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x108506) (movR64R64Effect 0x108506 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108506 2 4).toInstrSpec (mov_r64_r64_effect_step 0x108506 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x108509 [0x0F, 0xB6, 0x1C, 0x24] (LoadPre 0x108509 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108509 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108509 4 3 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x108509 4 3 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x108509 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10850d [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x10850d) (xorR64R64Effect 0x10850d 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10850d 0 1).toInstrSpec (xor_r64_r64_effect_step 0x10850d 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x108510 [0x48, 0xF7, 0xDB] (fun s => s.RIP = 0x108510) (negR64Effect 0x108510 3)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (negR64Effect_footprint 0x108510 3).toInstrSpec (neg_r64_effect_step 0x108510 0x48 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x108513 [0x48, 0x21, 0xC3] (fun s => s.RIP = 0x108513) (andR64R64Effect 0x108513 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108513 3 0).toInstrSpec (and_r64_r64_effect_step 0x108513 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x108516 [0x48, 0x31, 0xCB] (fun s => s.RIP = 0x108516) (xorR64R64Effect 0x108516 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108516 3 1).toInstrSpec (xor_r64_r64_effect_step 0x108516 0x48 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084ea) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084ee) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084f1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084f4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084f8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084fd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108500) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108503) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108506) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 76), (1, 1), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108509) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 76), (1, 1), (3, 80), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10850d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 1), (3, 80), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108510) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 82), (1, 1), (3, 84), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108513) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 82), (1, 1), (3, 86), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108516) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 82), (1, 1), (3, 88), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108519) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1084e0_1 code

theorem block_l1084e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1084e0 :=
  Rest.liftedBlock (rest_l1084e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1084e0 x hx)

end K256.Proofs.Signing.LIR
