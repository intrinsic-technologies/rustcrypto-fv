import K256.Proofs.Signing.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

theorem rest_l1099c0_7 [Bindings] (code : CodeMap) :
    Rest (n := 366) code lifted (codeRange 0x1099c0 bytes_l1099c0) [(0, 345), (1, 364), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 361), (12, 318), (13, 341), (14, 348), (15, 358), (16, 362), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x109b94 bytes_l1099c0_7 b_l1099c0_7 := by
  have f140 : InstrSpec 0x109b94 [0x49, 0x01, 0xC3] (fun s => s.RIP = 0x109b94) (addR64R64Effect 0x109b94 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109b94 11 0).toInstrSpec (add_r64_r64_effect_step 0x109b94 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x109b97 [0x0F, 0xB6, 0xC1] (fun s => s.RIP = 0x109b97) (movzxR32R8Effect 0x109b97 3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x109b97 3 0 1).toInstrSpec (movzx_r32_r8_effect_step 0x109b97 0xc1 (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x109b9a [0x48, 0x11, 0xD0] (fun s => s.RIP = 0x109b9a) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b9a 0 2))
      [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b9a 0 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b9a 0x48 0xd0 c (by decide) (by decide))) pre_rip
  have f143 : InstrSpec 0x109b9d [0x48, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x109b9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109b9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b9d 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109b9d 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x109b9d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f144 : InstrSpec 0x109ba2 [0x48, 0x89, 0x4C, 0x24, 0x48] (StorePre 0x109ba2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109ba2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ba2 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ba2 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x109ba2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f145 : InstrSpec 0x109ba7 [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x109ba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109ba7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109ba7 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109ba7 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x109ba7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f146 : InstrSpec 0x109bac [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x109bac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109bac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bac 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109bac 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x109bac 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f147 : InstrSpec 0x109bb1 [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x109bb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109bb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109bb1 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109bb1 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x109bb1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f148 : InstrSpec 0x109bb6 [0x48, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x109bb6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x109bb6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bb6 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109bb6 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x109bb6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f149 : InstrSpec 0x109bbb [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x109bbb (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109bbb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109bbb 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109bbb 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109bbb 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f150 : InstrSpec 0x109bbf [0x48, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x109bbf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109bbf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bbf 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109bbf 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x109bbf 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f151 : InstrSpec 0x109bc4 [0x4C, 0x89, 0x44, 0x24, 0x68] (StorePre 0x109bc4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109bc4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bc4 8 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109bc4 8 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x109bc4 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f152 : InstrSpec 0x109bc9 [0x4C, 0x89, 0x7C, 0x24, 0x70] (StorePre 0x109bc9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x109bc9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bc9 15 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109bc9 15 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x109bc9 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f153 : InstrSpec 0x109bce [0x4C, 0x89, 0x5C, 0x24, 0x78] (StorePre 0x109bce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109bce + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bce 11 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109bce 11 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x109bce 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f154 : InstrSpec 0x109bd3 [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x109bd3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109bd3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109bd3 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109bd3 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x109bd3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f155 : InstrSpec 0x109bdb [0x48, 0x8D, 0x74, 0x24, 0x48] (fun s => s.RIP = 0x109bdb) (leaR64Effect 0x109bdb 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x109bdb 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x109bdb 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x109be0 [0x31, 0xD2] (fun s => s.RIP = 0x109be0) (xorR32R32Effect 0x109be0 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109be0 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x109be0 0xd2 (by decide)) pre_rip
  have f157 : InstrSpec 0x109be2 [0xE8, 0x29, 0x19, 0x01, 0x00] (PushPre 0x109be2 5) (callEffect (fun _ => 0x11b510) 0x109be7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109be2 0x11b510 0x109be7).toInstrSpec (call_rel32_effect_step 0x109be2 0x11929 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 366) (RestInside.out (n := 366) f140 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 367) f140 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 368) (ρ' := [(0, 345), (1, 364), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (16, 367), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b97) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f141 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 370) (ρ' := [(0, 369), (1, 364), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (16, 367), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b9a) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f142 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 371), (1, 364), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b9d) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f143 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 371), (1, 373), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ba2) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.exec (n := 375) (ρ' := [(0, 371), (1, 373), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ba7) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f145 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 371), (1, 376), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bac) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.exec (n := 378) (ρ' := [(0, 371), (1, 376), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bb1) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 379) (RestInside.out (n := 379) f147 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 380) (ρ' := [(0, 371), (1, 379), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bb6) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 381) (RestInside.exec (n := 381) (ρ' := [(0, 371), (1, 379), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bbb) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f149 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 371), (1, 382), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bbf) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.exec (n := 384) (ρ' := [(0, 371), (1, 382), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bc4) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 385) (RestInside.exec (n := 385) (ρ' := [(0, 371), (1, 382), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bc9) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 386) (RestInside.exec (n := 386) (ρ' := [(0, 371), (1, 382), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bce) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 387) (RestInside.exec (n := 387) (ρ' := [(0, 371), (1, 382), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bd3) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 388) (RestInside.exec (n := 388) (ρ' := [(0, 371), (1, 382), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bdb) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f155 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 371), (1, 382), (2, 356), (3, 199), (4, 65), (5, 323), (6, 389), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109be0) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f156 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 371), (1, 382), (2, 391), (3, 199), (4, 65), (5, 323), (6, 389), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109be2) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 393) (RestInside.out (n := 393) f157 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 394) (ρ' := [(0, 371), (1, 382), (2, 391), (3, 199), (4, 393), (5, 323), (6, 389), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b510) f157 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 395) (by decide) (by decide) rfl rfl

theorem rest_l1099c0_6 [Bindings] (code : CodeMap) :
    Rest (n := 318) code lifted (codeRange 0x1099c0 bytes_l1099c0) [(0, 308), (1, 299), (2, 309), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 301), (12, 311), (13, 296), (14, 231), (15, 282), (16, 316), (22, 22), (39, 39), (50, 50), (51, 51)]
      38 0x109b56 bytes_l1099c0_6 b_l1099c0_6 := by
  have f120 : InstrSpec 0x109b56 [0x4D, 0x11, 0xDC] (fun s => s.RIP = 0x109b56) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b56 12 11))
      [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b56 12 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b56 0x4d 0xdc c (by decide) (by decide))) pre_rip
  have f121 : InstrSpec 0x109b59 [0x41, 0x0F, 0xB6, 0xE9] (fun s => s.RIP = 0x109b59) (movzxR32R8Effect 0x109b59 4 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movzxR32R8Effect_footprint 0x109b59 4 5 9).toInstrSpec (movzx_r32_r8_rex_effect_step 0x109b59 0x41 (by decide) 0xe9 (by decide)) pre_rip
  have f122 : InstrSpec 0x109b5d [0x48, 0x11, 0xCD] (fun s => s.RIP = 0x109b5d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b5d 5 1))
      [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b5d 5 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b5d 0x48 0xcd c (by decide) (by decide))) pre_rip
  have f123 : InstrSpec 0x109b60 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x109b60) (movR64R64Effect 0x109b60 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109b60 0 6).toInstrSpec (mov_r64_r64_effect_step 0x109b60 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x109b63 [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x109b63) (mulR64Effect 0x109b63 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109b63 14).toInstrSpec (mul_r64_effect_step 0x109b63 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x109b66 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x109b66) (movR64R64Effect 0x109b66 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x109b66 11 2).toInstrSpec (mov_r64_r64_effect_step 0x109b66 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x109b69 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x109b69) (movR64R64Effect 0x109b69 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x109b69 15 0).toInstrSpec (mov_r64_r64_effect_step 0x109b69 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x109b6c [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x109b6c) (movR64R64Effect 0x109b6c 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109b6c 0 3).toInstrSpec (mov_r64_r64_effect_step 0x109b6c 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x109b6f [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x109b6f) (mulR64Effect 0x109b6f 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109b6f 10).toInstrSpec (mul_r64_effect_step 0x109b6f 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x109b72 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x109b72) (movR64R64Effect 0x109b72 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x109b72 9 2).toInstrSpec (mov_r64_r64_effect_step 0x109b72 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x109b75 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x109b75) (movR64R64Effect 0x109b75 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109b75 13 0).toInstrSpec (mov_r64_r64_effect_step 0x109b75 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x109b78 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x109b78) (movR64R64Effect 0x109b78 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109b78 0 6).toInstrSpec (mov_r64_r64_effect_step 0x109b78 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x109b7b [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x109b7b) (mulR64Effect 0x109b7b 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109b7b 10).toInstrSpec (mul_r64_effect_step 0x109b7b 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x109b7e [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x109b7e) (movR64R64Effect 0x109b7e 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x109b7e 14 7).toInstrSpec (mov_r64_r64_effect_step 0x109b7e 0x49 0xfe (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x109b81 [0x4D, 0x01, 0xE7] (fun s => s.RIP = 0x109b81) (addR64R64Effect 0x109b81 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109b81 15 12).toInstrSpec (add_r64_r64_effect_step 0x109b81 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x109b84 [0x49, 0x11, 0xEB] (fun s => s.RIP = 0x109b84) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b84 11 5))
      [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b84 11 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b84 0x49 0xeb c (by decide) (by decide))) pre_rip
  have f136 : InstrSpec 0x109b87 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x109b87) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109b87 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x109b87 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x109b87 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f137 : InstrSpec 0x109b8b [0x4D, 0x01, 0xEF] (fun s => s.RIP = 0x109b8b) (addR64R64Effect 0x109b8b 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109b8b 15 13).toInstrSpec (add_r64_r64_effect_step 0x109b8b 0x4d 0xef (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x109b8e [0x4D, 0x11, 0xCB] (fun s => s.RIP = 0x109b8e) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b8e 11 9))
      [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b8e 11 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b8e 0x4d 0xcb c (by decide) (by decide))) pre_rip
  have f139 : InstrSpec 0x109b91 [0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x109b91) (atFlags (condHolds 2) (setccR8Effect 0x109b91 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x109b91 3 1 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x109b91 2 0xc1 (by decide) (by decide) c)) pre_rip
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f120 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 319) f120 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109b56 12 11 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 320) (ρ' := [(0, 308), (1, 299), (2, 309), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 301), (12, 318), (13, 296), (14, 231), (15, 282), (16, 319), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b59) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 321) (RestInside.out (n := 321) f121 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 322) (ρ' := [(0, 308), (1, 299), (2, 309), (3, 199), (4, 65), (5, 321), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 301), (12, 318), (13, 296), (14, 231), (15, 282), (16, 319), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b5d) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f122 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 324) (ρ' := [(0, 308), (1, 299), (2, 309), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 301), (12, 318), (13, 296), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b60) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 325) (RestInside.out (n := 325) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 326) (ρ' := [(0, 325), (1, 299), (2, 309), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 301), (12, 318), (13, 296), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b63) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 327) (RestInside.out (n := 327) f124 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 328) f124 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 329) (ρ' := [(0, 327), (1, 299), (2, 328), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 301), (12, 318), (13, 296), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b66) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f125 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 327), (1, 299), (2, 328), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 330), (12, 318), (13, 296), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b69) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f126 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 327), (1, 299), (2, 328), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 330), (12, 318), (13, 296), (14, 231), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b6c) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f127 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 334), (1, 299), (2, 328), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 330), (12, 318), (13, 296), (14, 231), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b6f) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f128 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 337) f128 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 338) (ρ' := [(0, 336), (1, 299), (2, 337), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 330), (12, 318), (13, 296), (14, 231), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b72) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f129 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 340) (ρ' := [(0, 336), (1, 299), (2, 337), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 330), (12, 318), (13, 296), (14, 231), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b75) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f130 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 336), (1, 299), (2, 337), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 330), (12, 318), (13, 341), (14, 231), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b78) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f131 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 343), (1, 299), (2, 337), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 330), (12, 318), (13, 341), (14, 231), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b7b) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f132 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 346) f132 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 347) (ρ' := [(0, 345), (1, 299), (2, 346), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 330), (12, 318), (13, 341), (14, 231), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b7e) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f133 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 345), (1, 299), (2, 346), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 330), (12, 318), (13, 341), (14, 348), (15, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b81) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f134 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 351) f134 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 352) (ρ' := [(0, 345), (1, 299), (2, 346), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 330), (12, 318), (13, 341), (14, 348), (15, 350), (16, 351), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b84) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f135 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 354) f135 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109b84 11 5 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 355) (ρ' := [(0, 345), (1, 299), (2, 346), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 353), (12, 318), (13, 341), (14, 348), (15, 350), (16, 354), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b87) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 356) (RestInside.out (n := 356) f136 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 357) (ρ' := [(0, 345), (1, 299), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 353), (12, 318), (13, 341), (14, 348), (15, 350), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b8b) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 358) (RestInside.out (n := 358) f137 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 359) f137 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 360) (ρ' := [(0, 345), (1, 299), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 353), (12, 318), (13, 341), (14, 348), (15, 358), (16, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b8e) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f138 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 362) f138 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109b8e 11 9 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 363) (ρ' := [(0, 345), (1, 299), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 361), (12, 318), (13, 341), (14, 348), (15, 358), (16, 362), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b91) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 364) (RestInside.out (n := 364) f139 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 365) (ρ' := [(0, 345), (1, 364), (2, 356), (3, 199), (4, 65), (5, 323), (6, 184), (7, 7), (8, 315), (9, 339), (10, 245), (11, 361), (12, 318), (13, 341), (14, 348), (15, 358), (16, 362), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b94) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1099c0_7 code

theorem rest_l1099c0_5 [Bindings] (code : CodeMap) :
    Rest (n := 270) code lifted (codeRange 0x1099c0 bytes_l1099c0) [(0, 259), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 214), (13, 247), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]
      58 0x109b15 bytes_l1099c0_5 b_l1099c0_5 := by
  have f100 : InstrSpec 0x109b15 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x109b15) (movR64R64Effect 0x109b15 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109b15 0 6).toInstrSpec (mov_r64_r64_effect_step 0x109b15 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x109b18 [0x48, 0xF7, 0x64, 0x24, 0x18] (LoadPre 0x109b18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109b18 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x109b18 5 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x109b18 5 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mul_m64_effect_step 0x109b18 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f102 : InstrSpec 0x109b1d [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x109b1d) (movR64R64Effect 0x109b1d 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x109b1d 15 2).toInstrSpec (mov_r64_r64_effect_step 0x109b1d 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x109b20 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x109b20) (movR64R64Effect 0x109b20 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x109b20 12 0).toInstrSpec (mov_r64_r64_effect_step 0x109b20 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x109b23 [0x4D, 0x01, 0xDC] (fun s => s.RIP = 0x109b23) (addR64R64Effect 0x109b23 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109b23 12 11).toInstrSpec (add_r64_r64_effect_step 0x109b23 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x109b26 [0x4D, 0x11, 0xCF] (fun s => s.RIP = 0x109b26) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b26 15 9))
      [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b26 15 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b26 0x4d 0xcf c (by decide) (by decide))) pre_rip
  have f106 : InstrSpec 0x109b29 [0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x109b29) (atFlags (condHolds 2) (setccR8Effect 0x109b29 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x109b29 3 1 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x109b29 2 0xc1 (by decide) (by decide) c)) pre_rip
  have f107 : InstrSpec 0x109b2c [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x109b2c) (movR64R64Effect 0x109b2c 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109b2c 0 3).toInstrSpec (mov_r64_r64_effect_step 0x109b2c 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x109b2f [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x109b2f) (mulR64Effect 0x109b2f 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109b2f 14).toInstrSpec (mul_r64_effect_step 0x109b2f 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x109b32 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x109b32) (movR64R64Effect 0x109b32 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x109b32 11 2).toInstrSpec (mov_r64_r64_effect_step 0x109b32 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x109b35 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x109b35) (movR64R64Effect 0x109b35 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109b35 13 0).toInstrSpec (mov_r64_r64_effect_step 0x109b35 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x109b38 [0x4D, 0x01, 0xE5] (fun s => s.RIP = 0x109b38) (addR64R64Effect 0x109b38 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109b38 13 12).toInstrSpec (add_r64_r64_effect_step 0x109b38 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x109b3b [0x0F, 0xB6, 0xC9] (fun s => s.RIP = 0x109b3b) (movzxR32R8Effect 0x109b3b 3 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x109b3b 3 1 1).toInstrSpec (movzx_r32_r8_effect_step 0x109b3b 0xc9 (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x109b3e [0x4D, 0x11, 0xFB] (fun s => s.RIP = 0x109b3e) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b3e 11 15))
      [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b3e 11 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b3e 0x4d 0xfb c (by decide) (by decide))) pre_rip
  have f114 : InstrSpec 0x109b41 [0x41, 0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x109b41) (atFlags (condHolds 2) (setccR8Effect 0x109b41 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x109b41 4 9 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x109b41 2 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f115 : InstrSpec 0x109b45 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x109b45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109b45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b45 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109b45 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x109b45 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f116 : InstrSpec 0x109b4a [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x109b4a) (mulR64Effect 0x109b4a 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109b4a 10).toInstrSpec (mul_r64_effect_step 0x109b4a 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x109b4d [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x109b4d) (movR64R64Effect 0x109b4d 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x109b4d 12 2).toInstrSpec (mov_r64_r64_effect_step 0x109b4d 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x109b50 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x109b50) (movR64R64Effect 0x109b50 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x109b50 8 0).toInstrSpec (mov_r64_r64_effect_step 0x109b50 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x109b53 [0x4D, 0x01, 0xE8] (fun s => s.RIP = 0x109b53) (addR64R64Effect 0x109b53 8 13)
      [.gpr 8, .gpr 13] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109b53 8 13).toInstrSpec (add_r64_r64_effect_step 0x109b53 0x4d 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f100 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 270), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 214), (13, 247), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b18) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f101 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 273) f101 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 274) (ρ' := [(0, 272), (1, 146), (2, 273), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 214), (13, 247), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b1d) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f102 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 272), (1, 146), (2, 273), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 214), (13, 247), (14, 231), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b20) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f103 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 272), (1, 146), (2, 273), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 277), (13, 247), (14, 231), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b23) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f104 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 280) f104 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 281) (ρ' := [(0, 272), (1, 146), (2, 273), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 279), (13, 247), (14, 231), (15, 275), (16, 280), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b26) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f105 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 283) f105 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109b26 15 9 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 284) (ρ' := [(0, 272), (1, 146), (2, 273), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 279), (13, 247), (14, 231), (15, 282), (16, 283), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b29) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 272), (1, 285), (2, 273), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 279), (13, 247), (14, 231), (15, 282), (16, 283), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b2c) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f107 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 287), (1, 285), (2, 273), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 279), (13, 247), (14, 231), (15, 282), (16, 283), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b2f) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f108 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 290) f108 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 291) (ρ' := [(0, 289), (1, 285), (2, 290), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 279), (13, 247), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b32) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f109 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 289), (1, 285), (2, 290), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 292), (12, 279), (13, 247), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b35) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f110 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 289), (1, 285), (2, 290), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 292), (12, 279), (13, 294), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b38) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.out (n := 296) f111 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 297) f111 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 298) (ρ' := [(0, 289), (1, 285), (2, 290), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 292), (12, 279), (13, 296), (14, 231), (15, 282), (16, 297), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b3b) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f112 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 300) (ρ' := [(0, 289), (1, 299), (2, 290), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 292), (12, 279), (13, 296), (14, 231), (15, 282), (16, 297), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b3e) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 301) (RestInside.out (n := 301) f113 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 302) f113 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109b3e 11 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 303) (ρ' := [(0, 289), (1, 299), (2, 290), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 301), (12, 279), (13, 296), (14, 231), (15, 282), (16, 302), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b41) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f114 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 289), (1, 299), (2, 290), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 304), (10, 245), (11, 301), (12, 279), (13, 296), (14, 231), (15, 282), (16, 302), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b45) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f115 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 306), (1, 299), (2, 290), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 304), (10, 245), (11, 301), (12, 279), (13, 296), (14, 231), (15, 282), (16, 302), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b4a) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f116 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 309) f116 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 310) (ρ' := [(0, 308), (1, 299), (2, 309), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 304), (10, 245), (11, 301), (12, 279), (13, 296), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b4d) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f117 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 308), (1, 299), (2, 309), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 304), (10, 245), (11, 301), (12, 311), (13, 296), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b50) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f118 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 308), (1, 299), (2, 309), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 313), (9, 304), (10, 245), (11, 301), (12, 311), (13, 296), (14, 231), (15, 282), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b53) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 315) (RestInside.out (n := 315) f119 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 316) f119 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 317) (ρ' := [(0, 308), (1, 299), (2, 309), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 315), (9, 304), (10, 245), (11, 301), (12, 311), (13, 296), (14, 231), (15, 282), (16, 316), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b56) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1099c0_6 code

theorem rest_l1099c0_4 [Bindings] (code : CodeMap) :
    Rest (n := 224) code lifted (codeRange 0x1099c0 bytes_l1099c0) [(0, 220), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 222), (9, 212), (10, 188), (11, 95), (12, 214), (13, 157), (14, 67), (15, 217), (16, 218), (22, 22), (39, 39), (50, 50), (51, 51)]
      78 0x109ace bytes_l1099c0_4 b_l1099c0_4 := by
  have f80 : InstrSpec 0x109ace [0x41, 0x80, 0xC1, 0xFF] (fun s => s.RIP = 0x109ace) (addR8Imm8Effect 0x109ace 4 9 0xff)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR8Imm8Effect_footprint 0x109ace 4 9 0xff).toInstrSpec (add_r8_imm8_rex_effect_step 0x109ace 0x41 0xc1 0xff (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x109ad2 [0x49, 0x83, 0xD0, 0x00] (fun s => s.RIP = 0x109ad2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109ad2 8 0x0))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x109ad2 8 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x109ad2 0x49 0xd0 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f82 : InstrSpec 0x109ad6 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x109ad6) (movR64R64Effect 0x109ad6 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109ad6 0 1).toInstrSpec (mov_r64_r64_effect_step 0x109ad6 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x109ad9 [0x4C, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x109ad9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ad9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109ad9 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x109ad9 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109ad9 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f84 : InstrSpec 0x109ade [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x109ade) (mulR64Effect 0x109ade 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109ade 14).toInstrSpec (mul_r64_effect_step 0x109ade 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x109ae1 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x109ae1) (movR64R64Effect 0x109ae1 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109ae1 13 2).toInstrSpec (mov_r64_r64_effect_step 0x109ae1 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x109ae4 [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x109ae4) (movR64R64Effect 0x109ae4 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x109ae4 5 0).toInstrSpec (mov_r64_r64_effect_step 0x109ae4 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x109ae7 [0x4C, 0x01, 0xE5] (fun s => s.RIP = 0x109ae7) (addR64R64Effect 0x109ae7 5 12)
      [.gpr 5, .gpr 12] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109ae7 5 12).toInstrSpec (add_r64_r64_effect_step 0x109ae7 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x109aea [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x109aea (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109aea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aea 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109aea 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109aea 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f89 : InstrSpec 0x109aee [0x4C, 0x8B, 0x50, 0x18] (LoadPre 0x109aee (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x109aee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aee 10 (.base 0 (.d8 0x18)))
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x109aee 10 (.base 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109aee 0x4c (by decide) 2 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f90 : InstrSpec 0x109af2 [0x4D, 0x11, 0xFD] (fun s => s.RIP = 0x109af2) (atFlags StatusFlags.CF (adcR64R64Effect 0x109af2 13 15))
      [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109af2 13 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109af2 0x4d 0xfd c (by decide) (by decide))) pre_rip
  have f91 : InstrSpec 0x109af5 [0x41, 0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x109af5) (atFlags (condHolds 2) (setccR8Effect 0x109af5 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x109af5 4 9 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x109af5 2 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f92 : InstrSpec 0x109af9 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x109af9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109af9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109af9 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109af9 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x109af9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f93 : InstrSpec 0x109afe [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x109afe) (mulR64Effect 0x109afe 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109afe 10).toInstrSpec (mul_r64_effect_step 0x109afe 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x109b01 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x109b01) (movR64R64Effect 0x109b01 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x109b01 11 2).toInstrSpec (mov_r64_r64_effect_step 0x109b01 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x109b04 [0x48, 0x01, 0xE8] (fun s => s.RIP = 0x109b04) (addR64R64Effect 0x109b04 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109b04 0 5).toInstrSpec (add_r64_r64_effect_step 0x109b04 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x109b07 [0x48, 0x89, 0x04, 0x24] (StorePre 0x109b07 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109b07 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109b07 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b07 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x109b07 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f97 : InstrSpec 0x109b0b [0x4D, 0x11, 0xEB] (fun s => s.RIP = 0x109b0b) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b0b 11 13))
      [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b0b 11 13).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b0b 0x4d 0xeb c (by decide) (by decide))) pre_rip
  have f98 : InstrSpec 0x109b0e [0x45, 0x0F, 0xB6, 0xC9] (fun s => s.RIP = 0x109b0e) (movzxR32R8Effect 0x109b0e 4 9 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (movzxR32R8Effect_footprint 0x109b0e 4 9 9).toInstrSpec (movzx_r32_r8_rex_effect_step 0x109b0e 0x45 (by decide) 0xc9 (by decide)) pre_rip
  have f99 : InstrSpec 0x109b12 [0x4D, 0x11, 0xC1] (fun s => s.RIP = 0x109b12) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b12 9 8))
      [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109b12 9 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109b12 0x4d 0xc1 c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f80 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 225) f80 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 226) (ρ' := [(0, 220), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 222), (9, 224), (10, 188), (11, 95), (12, 214), (13, 157), (14, 67), (15, 217), (16, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ad2) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f81 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 220), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 227), (9, 224), (10, 188), (11, 95), (12, 214), (13, 157), (14, 67), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ad6) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f82 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 229), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 227), (9, 224), (10, 188), (11, 95), (12, 214), (13, 157), (14, 67), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ad9) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f83 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 229), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 227), (9, 224), (10, 188), (11, 95), (12, 214), (13, 157), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ade) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f84 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 234) f84 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 235) (ρ' := [(0, 233), (1, 146), (2, 234), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 227), (9, 224), (10, 188), (11, 95), (12, 214), (13, 157), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ae1) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f85 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 233), (1, 146), (2, 234), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 227), (9, 224), (10, 188), (11, 95), (12, 214), (13, 236), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ae4) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f86 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 233), (1, 146), (2, 234), (3, 199), (4, 65), (5, 238), (6, 184), (7, 7), (8, 227), (9, 224), (10, 188), (11, 95), (12, 214), (13, 236), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ae7) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f87 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 241) f87 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 242) (ρ' := [(0, 233), (1, 146), (2, 234), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 224), (10, 188), (11, 95), (12, 214), (13, 236), (14, 231), (15, 217), (16, 241), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aea) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f88 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 243), (1, 146), (2, 234), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 224), (10, 188), (11, 95), (12, 214), (13, 236), (14, 231), (15, 217), (16, 241), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aee) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f89 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 243), (1, 146), (2, 234), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 224), (10, 245), (11, 95), (12, 214), (13, 236), (14, 231), (15, 217), (16, 241), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109af2) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f90 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 248) f90 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109af2 13 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 249) (ρ' := [(0, 243), (1, 146), (2, 234), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 224), (10, 245), (11, 95), (12, 214), (13, 247), (14, 231), (15, 217), (16, 248), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109af5) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f91 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 243), (1, 146), (2, 234), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 250), (10, 245), (11, 95), (12, 214), (13, 247), (14, 231), (15, 217), (16, 248), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109af9) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f92 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 252), (1, 146), (2, 234), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 250), (10, 245), (11, 95), (12, 214), (13, 247), (14, 231), (15, 217), (16, 248), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109afe) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f93 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 255) f93 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 256) (ρ' := [(0, 254), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 250), (10, 245), (11, 95), (12, 214), (13, 247), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b01) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f94 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 254), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 250), (10, 245), (11, 257), (12, 214), (13, 247), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b04) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f95 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 260) f95 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 261) (ρ' := [(0, 259), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 250), (10, 245), (11, 257), (12, 214), (13, 247), (14, 231), (15, 217), (16, 260), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b07) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.exec (n := 262) (ρ' := [(0, 259), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 250), (10, 245), (11, 257), (12, 214), (13, 247), (14, 231), (15, 217), (16, 260), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b0b) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f97 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 264) f97 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109b0b 11 13 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 265) (ρ' := [(0, 259), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 250), (10, 245), (11, 263), (12, 214), (13, 247), (14, 231), (15, 217), (16, 264), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b0e) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f98 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 259), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 266), (10, 245), (11, 263), (12, 214), (13, 247), (14, 231), (15, 217), (16, 264), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b12) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f99 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 259), (1, 146), (2, 255), (3, 199), (4, 65), (5, 240), (6, 184), (7, 7), (8, 227), (9, 268), (10, 245), (11, 263), (12, 214), (13, 247), (14, 231), (15, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b15) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1099c0_5 code

theorem rest_l1099c0_3 [Bindings] (code : CodeMap) :
    Rest (n := 177) code lifted (codeRange 0x1099c0 bytes_l1099c0) [(0, 172), (1, 146), (2, 173), (3, 97), (4, 65), (5, 175), (6, 74), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]
      98 0x109a8a bytes_l1099c0_3 b_l1099c0_3 := by
  have f60 : InstrSpec 0x109a8a [0x4C, 0x01, 0xE8] (fun s => s.RIP = 0x109a8a) (addR64R64Effect 0x109a8a 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109a8a 0 13).toInstrSpec (add_r64_r64_effect_step 0x109a8a 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x109a8d [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x109a8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109a8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a8d 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a8d 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x109a8d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f62 : InstrSpec 0x109a92 [0x4C, 0x11, 0xE5] (fun s => s.RIP = 0x109a92) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a92 5 12))
      [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109a92 5 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109a92 0x4c 0xe5 c (by decide) (by decide))) pre_rip
  have f63 : InstrSpec 0x109a95 [0x49, 0x8B, 0x76, 0x18] (LoadPre 0x109a95 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x109a95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a95 6 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x109a95 6 (.base 14 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109a95 0x49 (by decide) 6 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f64 : InstrSpec 0x109a99 [0x45, 0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x109a99) (movzxR32R8Effect 0x109a99 4 10 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (movzxR32R8Effect_footprint 0x109a99 4 10 10).toInstrSpec (movzx_r32_r8_rex_effect_step 0x109a99 0x45 (by decide) 0xd2 (by decide)) pre_rip
  have f65 : InstrSpec 0x109a9d [0x4D, 0x11, 0xCA] (fun s => s.RIP = 0x109a9d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a9d 10 9))
      [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109a9d 10 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109a9d 0x4d 0xca c (by decide) (by decide))) pre_rip
  have f66 : InstrSpec 0x109aa0 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x109aa0) (movR64R64Effect 0x109aa0 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109aa0 0 6).toInstrSpec (mov_r64_r64_effect_step 0x109aa0 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x109aa3 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x109aa3) (mulR64Effect 0x109aa3 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109aa3 8).toInstrSpec (mul_r64_effect_step 0x109aa3 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x109aa6 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x109aa6) (movR64R64Effect 0x109aa6 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x109aa6 15 2).toInstrSpec (mov_r64_r64_effect_step 0x109aa6 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x109aa9 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x109aa9) (movR64R64Effect 0x109aa9 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x109aa9 12 0).toInstrSpec (mov_r64_r64_effect_step 0x109aa9 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x109aac [0x48, 0x8B, 0x5C, 0x24, 0x10] (LoadPre 0x109aac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109aac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109aac 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x109aac 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109aac 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x109ab1 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x109ab1) (movR64R64Effect 0x109ab1 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109ab1 0 3).toInstrSpec (mov_r64_r64_effect_step 0x109ab1 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x109ab4 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x109ab4) (mulR64Effect 0x109ab4 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109ab4 11).toInstrSpec (mul_r64_effect_step 0x109ab4 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x109ab7 [0x49, 0x01, 0xEC] (fun s => s.RIP = 0x109ab7) (addR64R64Effect 0x109ab7 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109ab7 12 5).toInstrSpec (add_r64_r64_effect_step 0x109ab7 0x49 0xec (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x109aba [0x4D, 0x11, 0xD7] (fun s => s.RIP = 0x109aba) (atFlags StatusFlags.CF (adcR64R64Effect 0x109aba 15 10))
      [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109aba 15 10).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109aba 0x4d 0xd7 c (by decide) (by decide))) pre_rip
  have f75 : InstrSpec 0x109abd [0x41, 0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x109abd) (atFlags (condHolds 2) (setccR8Effect 0x109abd 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x109abd 4 9 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x109abd 2 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f76 : InstrSpec 0x109ac1 [0x49, 0x01, 0xC4] (fun s => s.RIP = 0x109ac1) (addR64R64Effect 0x109ac1 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109ac1 12 0).toInstrSpec (add_r64_r64_effect_step 0x109ac1 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x109ac4 [0x49, 0x11, 0xD7] (fun s => s.RIP = 0x109ac4) (atFlags StatusFlags.CF (adcR64R64Effect 0x109ac4 15 2))
      [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109ac4 15 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109ac4 0x49 0xd7 c (by decide) (by decide))) pre_rip
  have f78 : InstrSpec 0x109ac7 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x109ac7) (atFlags (condHolds 2) (setccR8Effect 0x109ac7 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x109ac7 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x109ac7 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f79 : InstrSpec 0x109aca [0x44, 0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x109aca) (movzxR32R8Effect 0x109aca 4 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movzxR32R8Effect_footprint 0x109aca 4 8 0).toInstrSpec (movzx_r32_r8_rex_effect_step 0x109aca 0x44 (by decide) 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 178) f60 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 179) (ρ' := [(0, 177), (1, 146), (2, 173), (3, 97), (4, 65), (5, 175), (6, 74), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (16, 178), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a8d) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.exec (n := 180) (ρ' := [(0, 177), (1, 146), (2, 173), (3, 97), (4, 65), (5, 175), (6, 74), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (16, 178), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a92) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f62 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 182) f62 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109a92 5 12 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 183) (ρ' := [(0, 177), (1, 146), (2, 173), (3, 97), (4, 65), (5, 181), (6, 74), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (16, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a95) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f63 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 177), (1, 146), (2, 173), (3, 97), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (16, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a99) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f64 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 177), (1, 146), (2, 173), (3, 97), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 186), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (16, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a9d) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f65 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 177), (1, 146), (2, 173), (3, 97), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aa0) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 190), (1, 146), (2, 173), (3, 97), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aa3) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 193) f67 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 194) (ρ' := [(0, 192), (1, 146), (2, 193), (3, 97), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aa6) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f68 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 192), (1, 146), (2, 193), (3, 97), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 165), (13, 157), (14, 67), (15, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aa9) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f69 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 192), (1, 146), (2, 193), (3, 97), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 197), (13, 157), (14, 67), (15, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aac) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f70 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 192), (1, 146), (2, 193), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 197), (13, 157), (14, 67), (15, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ab1) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f71 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 201), (1, 146), (2, 193), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 197), (13, 157), (14, 67), (15, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ab4) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f72 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 204) f72 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 205) (ρ' := [(0, 203), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 197), (13, 157), (14, 67), (15, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ab7) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f73 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 207) f73 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 208) (ρ' := [(0, 203), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 206), (13, 157), (14, 67), (15, 195), (16, 207), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aba) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f74 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 210) f74 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109aba 15 10 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 211) (ρ' := [(0, 203), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 142), (10, 188), (11, 95), (12, 206), (13, 157), (14, 67), (15, 209), (16, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109abd) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f75 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 203), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 212), (10, 188), (11, 95), (12, 206), (13, 157), (14, 67), (15, 209), (16, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ac1) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f76 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 215) f76 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 216) (ρ' := [(0, 203), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 212), (10, 188), (11, 95), (12, 214), (13, 157), (14, 67), (15, 209), (16, 215), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ac4) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f77 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 218) f77 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109ac4 15 2 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 219) (ρ' := [(0, 203), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 212), (10, 188), (11, 95), (12, 214), (13, 157), (14, 67), (15, 217), (16, 218), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ac7) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 220), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 69), (9, 212), (10, 188), (11, 95), (12, 214), (13, 157), (14, 67), (15, 217), (16, 218), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aca) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f79 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 220), (1, 146), (2, 204), (3, 199), (4, 65), (5, 181), (6, 184), (7, 7), (8, 222), (9, 212), (10, 188), (11, 95), (12, 214), (13, 157), (14, 67), (15, 217), (16, 218), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ace) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1099c0_4 code

theorem rest_l1099c0_2 [Bindings] (code : CodeMap) :
    Rest (n := 136) code lifted (codeRange 0x1099c0 bytes_l1099c0) [(0, 131), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 122), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 129), (16, 134), (22, 22), (39, 39), (50, 50), (51, 51)]
      118 0x109a44 bytes_l1099c0_2 b_l1099c0_2 := by
  have f40 : InstrSpec 0x109a44 [0x49, 0x11, 0xC7] (fun s => s.RIP = 0x109a44) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a44 15 0))
      [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109a44 15 0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109a44 0x49 0xc7 c (by decide) (by decide))) pre_rip
  have f41 : InstrSpec 0x109a47 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x109a47) (xorR32R32Effect 0x109a47 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109a47 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x109a47 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x109a4a [0x49, 0x39, 0xC7] (fun s => s.RIP = 0x109a4a) (cmpR64R64Effect 0x109a4a 15 0)
      [.gpr 15, .gpr 0] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x109a4a 15 0).toInstrSpec (cmp_r64_r64_effect_step 0x109a4a 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x109a4d [0x41, 0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x109a4d) (atFlags (condHolds 2) (setccR8Effect 0x109a4d 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x109a4d 4 9 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x109a4d 2 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f44 : InstrSpec 0x109a51 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x109a51) (movR64R64Effect 0x109a51 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109a51 0 13).toInstrSpec (mov_r64_r64_effect_step 0x109a51 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x109a54 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x109a54) (movR64R64Effect 0x109a54 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109a54 1 13).toInstrSpec (mov_r64_r64_effect_step 0x109a54 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x109a57 [0x4C, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x109a57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109a57 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a57 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a57 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x109a57 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x109a5c [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x109a5c) (mulR64Effect 0x109a5c 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109a5c 11).toInstrSpec (mul_r64_effect_step 0x109a5c 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x109a5f [0x4C, 0x89, 0x5C, 0x24, 0x18] (StorePre 0x109a5f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109a5f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a5f 11 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a5f 11 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109a5f 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x109a64 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x109a64) (movR64R64Effect 0x109a64 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x109a64 12 2).toInstrSpec (mov_r64_r64_effect_step 0x109a64 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x109a67 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x109a67) (movR64R64Effect 0x109a67 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109a67 13 0).toInstrSpec (mov_r64_r64_effect_step 0x109a67 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x109a6a [0x4D, 0x01, 0xD5] (fun s => s.RIP = 0x109a6a) (addR64R64Effect 0x109a6a 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109a6a 13 10).toInstrSpec (add_r64_r64_effect_step 0x109a6a 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x109a6d [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x109a6d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109a6d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a6d 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109a6d 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109a6d 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x109a71 [0x48, 0x8B, 0x50, 0x10] (LoadPre 0x109a71 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x109a71 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a71 2 (.base 0 (.d8 0x10)))
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x109a71 2 (.base 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109a71 0x48 (by decide) 2 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x109a75 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109a75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109a75 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a75 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a75 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109a75 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x109a7a [0x4D, 0x11, 0xFC] (fun s => s.RIP = 0x109a7a) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a7a 12 15))
      [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109a7a 12 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109a7a 0x4d 0xfc c (by decide) (by decide))) pre_rip
  have f56 : InstrSpec 0x109a7d [0x41, 0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x109a7d) (atFlags (condHolds 2) (setccR8Effect 0x109a7d 4 10))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (setccR8Effect_footprint 0x109a7d 4 10 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x109a7d 2 0x41 (by decide) 0xc2 (by decide) c)) pre_rip
  have f57 : InstrSpec 0x109a81 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x109a81) (movR64R64Effect 0x109a81 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109a81 0 6).toInstrSpec (mov_r64_r64_effect_step 0x109a81 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x109a84 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x109a84) (mulR64Effect 0x109a84 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109a84 2).toInstrSpec (mul_r64_effect_step 0x109a84 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x109a87 [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x109a87) (movR64R64Effect 0x109a87 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x109a87 5 2).toInstrSpec (mov_r64_r64_effect_step 0x109a87 0x48 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f40 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 131), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 122), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a47) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f41 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 131), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 138), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a4a) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f42 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 131), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 138), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (16, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a4d) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f43 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 131), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (16, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a51) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 144), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (16, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a54) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 144), (1, 146), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (16, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a57) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 144), (1, 146), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (16, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a5c) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f47 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 150) f47 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 151) (ρ' := [(0, 149), (1, 146), (2, 150), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a5f) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.exec (n := 152) (ρ' := [(0, 149), (1, 146), (2, 150), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a64) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f49 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 149), (1, 146), (2, 150), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 153), (13, 76), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a67) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f50 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 149), (1, 146), (2, 150), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 153), (13, 155), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a6a) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f51 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 158) f51 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 159) (ρ' := [(0, 149), (1, 146), (2, 150), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 153), (13, 157), (14, 67), (15, 136), (16, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a6d) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 160), (1, 146), (2, 150), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 153), (13, 157), (14, 67), (15, 136), (16, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a71) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 160), (1, 146), (2, 162), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 153), (13, 157), (14, 67), (15, 136), (16, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a75) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.exec (n := 164) (ρ' := [(0, 160), (1, 146), (2, 162), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 153), (13, 157), (14, 67), (15, 136), (16, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a7a) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f55 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 166) f55 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109a7a 12 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 167) (ρ' := [(0, 160), (1, 146), (2, 162), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 133), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (16, 166), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a7d) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f56 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 160), (1, 146), (2, 162), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (16, 166), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a81) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f57 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 170), (1, 146), (2, 162), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (16, 166), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a84) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 173) f58 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 174) (ρ' := [(0, 172), (1, 146), (2, 173), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a87) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f59 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 172), (1, 146), (2, 173), (3, 97), (4, 65), (5, 175), (6, 74), (7, 7), (8, 69), (9, 142), (10, 168), (11, 95), (12, 165), (13, 157), (14, 67), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a8a) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1099c0_3 code

theorem rest_l1099c0_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x1099c0 bytes_l1099c0) [(0, 88), (2, 89), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      138 0x1099fc bytes_l1099c0_1 b_l1099c0_1 := by
  have f20 : InstrSpec 0x1099fc [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x1099fc) (movR64R64Effect 0x1099fc 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1099fc 15 2).toInstrSpec (mov_r64_r64_effect_step 0x1099fc 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1099ff [0x4D, 0x8B, 0x5B, 0x08] (LoadPre 0x1099ff (fun s => AddrMode.addr (.base 11 (.d8 0x8)) s (0x1099ff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1099ff 11 (.base 11 (.d8 0x8)))
      [.gpr 11] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1099ff 11 (.base 11 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1099ff 0x4d (by decide) 3 (.base 11 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x109a03 [0x49, 0x8D, 0x1C, 0x01] (fun s => s.RIP = 0x109a03) (leaR64Effect 0x109a03 3 (.sib 9 (some 0) 0 .none))
      [.gpr 9, .gpr 0] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x109a03 3 (.sib 9 (some 0) 0 .none)).toInstrSpec (lea_r64_effect_step 0x109a03 0x49 (by decide) 3 (.sib 9 (some 0) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x109a07 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x109a07) (movR64R64Effect 0x109a07 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109a07 0 6).toInstrSpec (mov_r64_r64_effect_step 0x109a07 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x109a0a [0x48, 0x89, 0x74, 0x24, 0x28] (StorePre 0x109a0a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109a0a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a0a 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a0a 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x109a0a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x109a0f [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x109a0f) (mulR64Effect 0x109a0f 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109a0f 11).toInstrSpec (mul_r64_effect_step 0x109a0f 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x109a12 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x109a12) (movR64R64Effect 0x109a12 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x109a12 12 2).toInstrSpec (mov_r64_r64_effect_step 0x109a12 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x109a15 [0x48, 0x01, 0xD8] (fun s => s.RIP = 0x109a15) (addR64R64Effect 0x109a15 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109a15 0 3).toInstrSpec (add_r64_r64_effect_step 0x109a15 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x109a18 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x109a18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109a18 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a18 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a18 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x109a18 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x109a1d [0x49, 0x83, 0xD4, 0x00] (fun s => s.RIP = 0x109a1d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109a1d 12 0x0))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x109a1d 12 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x109a1d 0x49 0xd4 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f30 : InstrSpec 0x109a21 [0x4D, 0x01, 0xD1] (fun s => s.RIP = 0x109a21) (addR64R64Effect 0x109a21 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109a21 9 10).toInstrSpec (add_r64_r64_effect_step 0x109a21 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x109a24 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x109a24 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x109a24 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a24 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109a24 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109a24 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x109a28 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x109a28 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109a28 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a28 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a28 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109a28 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x109a2d [0x4D, 0x11, 0xFC] (fun s => s.RIP = 0x109a2d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a2d 12 15))
      [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x109a2d 12 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x109a2d 0x4d 0xfc c (by decide) (by decide))) pre_rip
  have f34 : InstrSpec 0x109a30 [0x41, 0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x109a30) (atFlags (condHolds 2) (setccR8Effect 0x109a30 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x109a30 4 9 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x109a30 2 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f35 : InstrSpec 0x109a34 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x109a34) (mulR64Effect 0x109a34 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x109a34 8).toInstrSpec (mul_r64_effect_step 0x109a34 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x109a37 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x109a37) (movR64R64Effect 0x109a37 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x109a37 10 0).toInstrSpec (mov_r64_r64_effect_step 0x109a37 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x109a3a [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x109a3a) (movR64R64Effect 0x109a3a 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x109a3a 15 2).toInstrSpec (mov_r64_r64_effect_step 0x109a3a 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x109a3d [0x41, 0x0F, 0xB6, 0xC1] (fun s => s.RIP = 0x109a3d) (movzxR32R8Effect 0x109a3d 4 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x109a3d 4 0 9).toInstrSpec (movzx_r32_r8_rex_effect_step 0x109a3d 0x41 (by decide) 0xc1 (by decide)) pre_rip
  have f39 : InstrSpec 0x109a41 [0x4D, 0x01, 0xE2] (fun s => s.RIP = 0x109a41) (addR64R64Effect 0x109a41 10 12)
      [.gpr 10, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109a41 10 12).toInstrSpec (add_r64_r64_effect_step 0x109a41 0x4d 0xe2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 88), (2, 89), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 71), (12, 12), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099ff) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 88), (2, 89), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 12), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a03) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 88), (2, 89), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 12), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a07) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 99), (2, 89), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 12), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a0a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 99), (2, 89), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 12), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a0f) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 102), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 12), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a12) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 102), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 105), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a15) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 108) f27 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 109) (ρ' := [(0, 107), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 105), (13, 76), (14, 67), (15, 93), (16, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a18) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 107), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 105), (13, 76), (14, 67), (15, 93), (16, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a1d) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 107), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 95), (12, 111), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a21) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 114) f30 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 115) (ρ' := [(0, 107), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 113), (10, 91), (11, 95), (12, 111), (13, 76), (14, 67), (15, 93), (16, 114), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a24) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 116), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 113), (10, 91), (11, 95), (12, 111), (13, 76), (14, 67), (15, 93), (16, 114), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a28) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.exec (n := 118) (ρ' := [(0, 116), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 113), (10, 91), (11, 95), (12, 111), (13, 76), (14, 67), (15, 93), (16, 114), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a2d) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 120) f33 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x109a2d 12 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 121) (ρ' := [(0, 116), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 113), (10, 91), (11, 95), (12, 119), (13, 76), (14, 67), (15, 93), (16, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a30) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f34 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 116), (2, 103), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 122), (10, 91), (11, 95), (12, 119), (13, 76), (14, 67), (15, 93), (16, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a34) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 124), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 122), (10, 91), (11, 95), (12, 119), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a37) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f36 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 124), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 122), (10, 127), (11, 95), (12, 119), (13, 76), (14, 67), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a3a) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f37 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 124), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 122), (10, 127), (11, 95), (12, 119), (13, 76), (14, 67), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a3d) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 131), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 122), (10, 127), (11, 95), (12, 119), (13, 76), (14, 67), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a41) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f39 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 134) f39 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 135) (ρ' := [(0, 131), (2, 125), (3, 97), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 122), (10, 133), (11, 95), (12, 119), (13, 76), (14, 67), (15, 129), (16, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a44) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1099c0_2 code

theorem rest_l1099c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1099c0 bytes_l1099c0) (entryMap (live .l1099c0))
      158 0x1099c0 bytes_l1099c0 b_l1099c0 := by
  have f0 : InstrSpec 0x1099c0 [0x55] (PushPre 0x1099c0 1) (pushR64Effect 0x1099c0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1099c0 1 5).toInstrSpec (push_r64_effect_step 0x1099c0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1099c1 [0x41, 0x57] (PushPre 0x1099c1 2) (pushR64Effect 0x1099c1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1099c1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1099c1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1099c3 [0x41, 0x56] (PushPre 0x1099c3 2) (pushR64Effect 0x1099c3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1099c3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1099c3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1099c5 [0x41, 0x55] (PushPre 0x1099c5 2) (pushR64Effect 0x1099c5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1099c5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1099c5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1099c7 [0x41, 0x54] (PushPre 0x1099c7 2) (pushR64Effect 0x1099c7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1099c7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1099c7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1099c9 [0x53] (PushPre 0x1099c9 1) (pushR64Effect 0x1099c9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1099c9 1 3).toInstrSpec (push_r64_effect_step 0x1099c9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1099ca [0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1099ca) (subR64Imm32Effect 0x1099ca 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1099ca 4 0x88).toInstrSpec (sub_r64_imm32_effect_step 0x1099ca 0x48 0xec 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1099d1 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x1099d1) (movR64R64Effect 0x1099d1 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1099d1 14 2).toInstrSpec (mov_r64_r64_effect_step 0x1099d1 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1099d4 [0x4C, 0x8B, 0x06] (LoadPre 0x1099d4 (fun s => AddrMode.addr (.base 6 .none) s (0x1099d4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1099d4 8 (.base 6 .none))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1099d4 8 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1099d4 0x4c (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1099d7 [0x49, 0x89, 0xF3] (fun s => s.RIP = 0x1099d7) (movR64R64Effect 0x1099d7 11 6)
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1099d7 11 6).toInstrSpec (mov_r64_r64_effect_step 0x1099d7 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1099da [0x48, 0x89, 0x34, 0x24] (StorePre 0x1099da 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1099da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1099da 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1099da 6 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1099da 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1099de [0x48, 0x8B, 0x32] (LoadPre 0x1099de (fun s => AddrMode.addr (.base 2 .none) s (0x1099de + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1099de 6 (.base 2 .none))
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1099de 6 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1099de 0x48 (by decide) 6 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1099e1 [0x4C, 0x8B, 0x6A, 0x08] (LoadPre 0x1099e1 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1099e1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1099e1 13 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1099e1 13 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1099e1 0x4c (by decide) 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1099e5 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x1099e5) (movR64R64Effect 0x1099e5 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1099e5 0 6).toInstrSpec (mov_r64_r64_effect_step 0x1099e5 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1099e8 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x1099e8) (mulR64Effect 0x1099e8 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1099e8 8).toInstrSpec (mul_r64_effect_step 0x1099e8 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1099eb [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x1099eb) (movR64R64Effect 0x1099eb 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1099eb 9 2).toInstrSpec (mov_r64_r64_effect_step 0x1099eb 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1099ee [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x1099ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1099ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1099ee 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1099ee 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1099ee 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1099f3 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1099f3) (movR64R64Effect 0x1099f3 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1099f3 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1099f3 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1099f6 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x1099f6) (mulR64Effect 0x1099f6 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1099f6 8).toInstrSpec (mul_r64_effect_step 0x1099f6 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1099f9 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x1099f9) (movR64R64Effect 0x1099f9 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1099f9 10 0).toInstrSpec (mov_r64_r64_effect_step 0x1099f9 0x49 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099d1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099d4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099d7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (11, 71), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099da) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 69), (11, 71), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099de) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (11, 71), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099e1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099e5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (2, 2), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099e8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 81) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 80), (2, 81), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099eb) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 80), (2, 81), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099ee) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 80), (2, 81), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099f3) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (2, 81), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099f6) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 89) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 88), (2, 89), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099f9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 88), (2, 89), (3, 3), (4, 65), (5, 5), (6, 74), (7, 7), (8, 69), (9, 83), (10, 91), (11, 71), (12, 12), (13, 76), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099fc) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1099c0_1 code

theorem block_l1099c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1099c0 :=
  Rest.liftedBlock (rest_l1099c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1099c0 x hx)

theorem rest_l109be7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109be7 bytes_l109be7) (entryMap (live .l109be7))
      9 0x109be7 bytes_l109be7 b_l109be7 := by
  have f0 : InstrSpec 0x109be7 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x109be7) (movR64R64Effect 0x109be7 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109be7 0 14).toInstrSpec (mov_r64_r64_effect_step 0x109be7 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109bea [0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109bea) (addR64Imm32Effect 0x109bea 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x109bea 4 0x88).toInstrSpec (add_r64_imm32_effect_step 0x109bea 0x48 0xc4 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109bf1 [0x5B] (PopPre 0x109bf1) (popR64Effect 0x109bf1 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109bf1 1 3).toInstrSpec (pop_r64_effect_step 0x109bf1 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109bf2 [0x41, 0x5C] (PopPre 0x109bf2) (popR64Effect 0x109bf2 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109bf2 2 12).toInstrSpec (pop_r64_rex_effect_step 0x109bf2 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109bf4 [0x41, 0x5D] (PopPre 0x109bf4) (popR64Effect 0x109bf4 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109bf4 2 13).toInstrSpec (pop_r64_rex_effect_step 0x109bf4 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109bf6 [0x41, 0x5E] (PopPre 0x109bf6) (popR64Effect 0x109bf6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109bf6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x109bf6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x109bf8 [0x41, 0x5F] (PopPre 0x109bf8) (popR64Effect 0x109bf8 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109bf8 2 15).toInstrSpec (pop_r64_rex_effect_step 0x109bf8 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x109bfa [0x5D] (PopPre 0x109bfa) (popR64Effect 0x109bfa 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109bfa 1 5).toInstrSpec (pop_r64_effect_step 0x109bfa 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x109bfb [0xC3] (RetPre 0x109bfb) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109bfb).toInstrSpec (ret_effect_step 0x109bfb) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bf1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bf2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bf4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bf6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bf8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bfa) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bfb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l109be7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109be7 :=
  Rest.liftedBlock (rest_l109be7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109be7 x hx)

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

theorem_by block_l1099c0_eval :
    program.runBlock (dialect code) ⟨.l1099c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109be7_eval :
    program.runBlock (dialect code) ⟨.l109be7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
