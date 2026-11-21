import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l100000_8 [Bindings] (code : CodeMap) :
    Rest (n := 363) code lifted (codeRange 0x100000 bytes_l100000) [(0, 361), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]
      19 0x100261 bytes_l100000_8 b_l100000_8 := by
  have f160 : InstrSpec 0x100261 [0x66, 0x89, 0x47, 0x0C] (StorePre 0x100261 4 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x100261 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100261 4 0 (.base 7 (.d8 0xc)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM16R16Effect_footprint 0x100261 4 0 (.base 7 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x100261 0 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f161 : InstrSpec 0x100265 [0x44, 0x89, 0xD8] (fun s => s.RIP = 0x100265) (movR32R32Effect 0x100265 3 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x100265 3 0 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x100265 0x44 0xd8 (by decide) (by decide)) pre_rip
  have f162 : InstrSpec 0x100268 [0x66, 0xC1, 0xC0, 0x06] (fun s => s.RIP = 0x100268) (rolR16Effect 0x100268 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x100268 4 0 6).toInstrSpec (rol_r16_imm8_effect_step 0x100268 0xc0 0x6 (by decide) (by decide)) pre_rip
  have f163 : InstrSpec 0x10026c [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10026c) (andEaxImm32Effect 0x10026c 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10026c 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x10026c 0x3333) pre_rip
  have f164 : InstrSpec 0x100271 [0x66, 0x41, 0xC1, 0xC3, 0x0A] (fun s => s.RIP = 0x100271) (rolR16Effect 0x100271 5 11 10)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR16Effect_footprint 0x100271 5 11 10).toInstrSpec (rol_r16_imm8_rex_effect_step 0x100271 0x41 0xc3 0xa (by decide) (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x100276 [0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x100276) (andR32Imm32Effect 0x100276 7 11 0xffffcccc)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100276 7 11 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x100276 0x41 0xe3 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f166 : InstrSpec 0x10027d [0x41, 0x09, 0xC3] (fun s => s.RIP = 0x10027d) (orR32R32Effect 0x10027d 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10027d 3 11 0).toInstrSpec (or_r32_r32_rex_effect_step 0x10027d 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x100280 [0x89, 0xD0] (fun s => s.RIP = 0x100280) (movR32R32Effect 0x100280 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x100280 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x100280 0xd0 (by decide)) pre_rip
  have f168 : InstrSpec 0x100282 [0x31, 0xE8] (fun s => s.RIP = 0x100282) (xorR32R32Effect 0x100282 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100282 2 0 5).toInstrSpec (xor_r32_r32_effect_step 0x100282 0xe8 (by decide)) pre_rip
  have f169 : InstrSpec 0x100284 [0x44, 0x31, 0xD8] (fun s => s.RIP = 0x100284) (xorR32R32Effect 0x100284 3 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100284 3 0 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100284 0x44 0xd8 (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x100287 [0x66, 0x89, 0x47, 0x0E] (StorePre 0x100287 4 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x100287 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100287 4 0 (.base 7 (.d8 0xe)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM16R16Effect_footprint 0x100287 4 0 (.base 7 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x100287 0 (.base 7 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f171 : InstrSpec 0x10028b [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x10028b) (addR64Imm8Effect 0x10028b 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10028b 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10028b 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f172 : InstrSpec 0x10028f [0x5B] (PopPre 0x10028f) (popR64Effect 0x10028f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10028f 1 3).toInstrSpec (pop_r64_effect_step 0x10028f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f173 : InstrSpec 0x100290 [0x41, 0x5C] (PopPre 0x100290) (popR64Effect 0x100290 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100290 2 12).toInstrSpec (pop_r64_rex_effect_step 0x100290 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f174 : InstrSpec 0x100292 [0x41, 0x5D] (PopPre 0x100292) (popR64Effect 0x100292 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100292 2 13).toInstrSpec (pop_r64_rex_effect_step 0x100292 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f175 : InstrSpec 0x100294 [0x41, 0x5E] (PopPre 0x100294) (popR64Effect 0x100294 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100294 2 14).toInstrSpec (pop_r64_rex_effect_step 0x100294 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f176 : InstrSpec 0x100296 [0x41, 0x5F] (PopPre 0x100296) (popR64Effect 0x100296 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100296 2 15).toInstrSpec (pop_r64_rex_effect_step 0x100296 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f177 : InstrSpec 0x100298 [0x5D] (PopPre 0x100298) (popR64Effect 0x100298 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100298 1 5).toInstrSpec (pop_r64_effect_step 0x100298 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f178 : InstrSpec 0x100299 [0xC3] (RetPre 0x100299) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x100299).toInstrSpec (ret_effect_step 0x100299) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 363) (RestInside.exec (n := 363) (ρ' := [(0, 361), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100265) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 364) (RestInside.out (n := 364) f161 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 365) (ρ' := [(0, 364), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100268) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 366) (RestInside.out (n := 366) f162 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 367) (ρ' := [(0, 366), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10026c) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 368) (RestInside.out (n := 368) f163 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 369) (ρ' := [(0, 368), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100271) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 370) (RestInside.out (n := 370) f164 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 371) (ρ' := [(0, 368), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 370), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100276) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.out (n := 372) f165 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 373) (ρ' := [(0, 368), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 372), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10027d) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 374) (RestInside.out (n := 374) f166 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 375) (ρ' := [(0, 368), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100280) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f167 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 376), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100282) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f168 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 378), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100284) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f169 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100287) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.exec (n := 382) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10028b) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 383) (RestInside.out (n := 383) f171 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 384) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 213), (4, 383), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10028f) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 385) (RestInside.out (n := 385) f172 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 386) f172 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 387) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 385), (4, 386), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100290) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.out (n := 388) f173 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 389) f173 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 390) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 385), (4, 389), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 388), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100292) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f174 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 392) f174 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 393) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 385), (4, 392), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 388), (13, 391), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100294) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.out (n := 394) f175 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 395) f175 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 396) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 385), (4, 395), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 388), (13, 391), (14, 394), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100296) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 397) (RestInside.out (n := 397) f176 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 398) f176 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 399) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 385), (4, 398), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 388), (13, 391), (14, 394), (15, 397), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100298) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.out (n := 400) f177 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 401) f177 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 402) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 385), (4, 401), (5, 400), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 388), (13, 391), (14, 394), (15, 397), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100299) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.out (n := 403) f178 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 404) f178 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 405) (ρ' := [(0, 380), (1, 355), (2, 338), (3, 385), (4, 404), (5, 400), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 374), (12, 388), (13, 391), (14, 394), (15, 397), (22, 22), (39, 39), (50, 50), (51, 51)]) f178 (by decide) rfl rfl rfl (by decide)

theorem rest_l100000_7 [Bindings] (code : CodeMap) :
    Rest (n := 324) code lifted (codeRange 0x100000 bytes_l100000) [(0, 318), (1, 320), (2, 307), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]
      39 0x10021d bytes_l100000_7 b_l100000_7 := by
  have f140 : InstrSpec 0x10021d [0x66, 0xC1, 0xC1, 0x0A] (fun s => s.RIP = 0x10021d) (rolR16Effect 0x10021d 4 1 10)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x10021d 4 1 10).toInstrSpec (rol_r16_imm8_effect_step 0x10021d 0xc1 0xa (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x100221 [0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x100221) (andR32Imm32Effect 0x100221 6 1 0xffffcccc)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100221 6 1 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x100221 0xe1 0xffffcccc (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x100227 [0x09, 0xC1] (fun s => s.RIP = 0x100227) (orR32R32Effect 0x100227 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x100227 2 1 0).toInstrSpec (or_r32_r32_effect_step 0x100227 0xc1 (by decide)) pre_rip
  have f143 : InstrSpec 0x100229 [0x44, 0x89, 0xC0] (fun s => s.RIP = 0x100229) (movR32R32Effect 0x100229 3 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x100229 3 0 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100229 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x10022c [0x44, 0x31, 0xF0] (fun s => s.RIP = 0x10022c) (xorR32R32Effect 0x10022c 3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10022c 3 0 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x10022c 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x10022f [0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x10022f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10022f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10022f 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x10022f 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x10022f 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f146 : InstrSpec 0x100233 [0x44, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x100233 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100233 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100233 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x100233 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x100233 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f147 : InstrSpec 0x100238 [0x44, 0x31, 0xC2] (fun s => s.RIP = 0x100238) (xorR32R32Effect 0x100238 3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100238 3 2 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100238 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x10023b [0x31, 0xC8] (fun s => s.RIP = 0x10023b) (xorR32R32Effect 0x10023b 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10023b 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10023b 0xc8 (by decide)) pre_rip
  have f149 : InstrSpec 0x10023d [0x66, 0x89, 0x47, 0x0A] (StorePre 0x10023d 4 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x10023d + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10023d 4 0 (.base 7 (.d8 0xa)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM16R16Effect_footprint 0x10023d 4 0 (.base 7 (.d8 0xa))).toInstrSpec (mov_m16_r16_effect_step 0x10023d 0 (.base 7 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f150 : InstrSpec 0x100241 [0x89, 0xD0] (fun s => s.RIP = 0x100241) (movR32R32Effect 0x100241 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x100241 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x100241 0xd0 (by decide)) pre_rip
  have f151 : InstrSpec 0x100243 [0x66, 0xC1, 0xC0, 0x06] (fun s => s.RIP = 0x100243) (rolR16Effect 0x100243 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x100243 4 0 6).toInstrSpec (rol_r16_imm8_effect_step 0x100243 0xc0 0x6 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x100247 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x100247) (andEaxImm32Effect 0x100247 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x100247 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x100247 0x3333) pre_rip
  have f153 : InstrSpec 0x10024c [0x89, 0xD1] (fun s => s.RIP = 0x10024c) (movR32R32Effect 0x10024c 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10024c 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x10024c 0xd1 (by decide)) pre_rip
  have f154 : InstrSpec 0x10024e [0x66, 0xC1, 0xC1, 0x0A] (fun s => s.RIP = 0x10024e) (rolR16Effect 0x10024e 4 1 10)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x10024e 4 1 10).toInstrSpec (rol_r16_imm8_effect_step 0x10024e 0xc1 0xa (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x100252 [0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x100252) (andR32Imm32Effect 0x100252 6 1 0xffffcccc)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100252 6 1 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x100252 0xe1 0xffffcccc (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x100258 [0x09, 0xC1] (fun s => s.RIP = 0x100258) (orR32R32Effect 0x100258 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x100258 2 1 0).toInstrSpec (or_r32_r32_effect_step 0x100258 0xc1 (by decide)) pre_rip
  have f157 : InstrSpec 0x10025a [0x89, 0xF0] (fun s => s.RIP = 0x10025a) (movR32R32Effect 0x10025a 2 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10025a 2 0 6).toInstrSpec (mov_r32_r32_effect_step 0x10025a 0xf0 (by decide)) pre_rip
  have f158 : InstrSpec 0x10025c [0x44, 0x31, 0xC0] (fun s => s.RIP = 0x10025c) (xorR32R32Effect 0x10025c 3 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10025c 3 0 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x10025c 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x10025f [0x31, 0xC8] (fun s => s.RIP = 0x10025f) (xorR32R32Effect 0x10025f 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10025f 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10025f 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f140 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 318), (1, 324), (2, 307), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100221) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f141 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 318), (1, 326), (2, 307), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100227) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f142 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 329) (ρ' := [(0, 318), (1, 328), (2, 307), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100229) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f143 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 330), (1, 328), (2, 307), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10022c) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f144 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 332), (1, 328), (2, 307), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10022f) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f145 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 332), (1, 328), (2, 334), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100233) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f146 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 332), (1, 328), (2, 334), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100238) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f147 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 339) (ρ' := [(0, 332), (1, 328), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10023b) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 340) (RestInside.out (n := 340) f148 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 341) (ρ' := [(0, 340), (1, 328), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10023d) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.exec (n := 342) (ρ' := [(0, 340), (1, 328), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100241) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f150 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 343), (1, 328), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100243) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f151 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 346) (ρ' := [(0, 345), (1, 328), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100247) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f152 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 347), (1, 328), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10024c) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f153 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 347), (1, 349), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10024e) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f154 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 347), (1, 351), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100252) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f155 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 347), (1, 353), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100258) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f156 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 347), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10025a) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f157 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 357), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10025c) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f158 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 359), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10025f) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f159 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 361), (1, 355), (2, 338), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 336), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100261) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_8 code

theorem rest_l100000_6 [Bindings] (code : CodeMap) :
    Rest (n := 286) code lifted (codeRange 0x100000 bytes_l100000) [(0, 266), (1, 274), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 284), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]
      59 0x1001da bytes_l100000_6 b_l100000_6 := by
  have f120 : InstrSpec 0x1001da [0x89, 0xD0] (fun s => s.RIP = 0x1001da) (movR32R32Effect 0x1001da 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1001da 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x1001da 0xd0 (by decide)) pre_rip
  have f121 : InstrSpec 0x1001dc [0x66, 0xC1, 0xC0, 0x06] (fun s => s.RIP = 0x1001dc) (rolR16Effect 0x1001dc 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1001dc 4 0 6).toInstrSpec (rol_r16_imm8_effect_step 0x1001dc 0xc0 0x6 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x1001e0 [0x66, 0x44, 0x89, 0x47, 0x06] (StorePre 0x1001e0 5 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x1001e0 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1001e0 5 8 (.base 7 (.d8 0x6)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM16R16Effect_footprint 0x1001e0 5 8 (.base 7 (.d8 0x6))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1001e0 0x44 (by decide) 0 (.base 7 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f123 : InstrSpec 0x1001e5 [0x89, 0xD1] (fun s => s.RIP = 0x1001e5) (movR32R32Effect 0x1001e5 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1001e5 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1001e5 0xd1 (by decide)) pre_rip
  have f124 : InstrSpec 0x1001e7 [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x1001e7) (movR32R32Effect 0x1001e7 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x1001e7 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x1001e7 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x1001ea [0x66, 0xC1, 0xC1, 0x0A] (fun s => s.RIP = 0x1001ea) (rolR16Effect 0x1001ea 4 1 10)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x1001ea 4 1 10).toInstrSpec (rol_r16_imm8_effect_step 0x1001ea 0xc1 0xa (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x1001ee [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x1001ee) (andEaxImm32Effect 0x1001ee 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1001ee 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x1001ee 0x3333) pre_rip
  have f127 : InstrSpec 0x1001f3 [0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x1001f3) (andR32Imm32Effect 0x1001f3 6 1 0xffffcccc)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1001f3 6 1 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x1001f3 0xe1 0xffffcccc (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x1001f9 [0x09, 0xC1] (fun s => s.RIP = 0x1001f9) (orR32R32Effect 0x1001f9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1001f9 2 1 0).toInstrSpec (or_r32_r32_effect_step 0x1001f9 0xc1 (by decide)) pre_rip
  have f129 : InstrSpec 0x1001fb [0x44, 0x31, 0xFE] (fun s => s.RIP = 0x1001fb) (xorR32R32Effect 0x1001fb 3 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1001fb 3 6 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x1001fb 0x44 0xfe (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x1001fe [0x8B, 0x54, 0x24, 0x04] (LoadPre 0x1001fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1001fe + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1001fe 2 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1001fe 2 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x1001fe 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f131 : InstrSpec 0x100202 [0x44, 0x31, 0xF2] (fun s => s.RIP = 0x100202) (xorR32R32Effect 0x100202 3 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100202 3 2 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x100202 0x44 0xf2 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x100205 [0x44, 0x31, 0xDE] (fun s => s.RIP = 0x100205) (xorR32R32Effect 0x100205 3 6 11)
      [.gpr 6, .gpr 11] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100205 3 6 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100205 0x44 0xde (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x100208 [0x31, 0xCE] (fun s => s.RIP = 0x100208) (xorR32R32Effect 0x100208 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100208 2 6 1).toInstrSpec (xor_r32_r32_effect_step 0x100208 0xce (by decide)) pre_rip
  have f134 : InstrSpec 0x10020a [0x66, 0x89, 0x77, 0x08] (StorePre 0x10020a 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10020a + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10020a 4 6 (.base 7 (.d8 0x8)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM16R16Effect_footprint 0x10020a 4 6 (.base 7 (.d8 0x8))).toInstrSpec (mov_m16_r16_effect_step 0x10020a 6 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f135 : InstrSpec 0x10020e [0x89, 0xD0] (fun s => s.RIP = 0x10020e) (movR32R32Effect 0x10020e 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10020e 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x10020e 0xd0 (by decide)) pre_rip
  have f136 : InstrSpec 0x100210 [0x66, 0xC1, 0xC0, 0x06] (fun s => s.RIP = 0x100210) (rolR16Effect 0x100210 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x100210 4 0 6).toInstrSpec (rol_r16_imm8_effect_step 0x100210 0xc0 0x6 (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x100214 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x100214) (andEaxImm32Effect 0x100214 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x100214 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x100214 0x3333) pre_rip
  have f138 : InstrSpec 0x100219 [0x89, 0xD1] (fun s => s.RIP = 0x100219) (movR32R32Effect 0x100219 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x100219 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x100219 0xd1 (by decide)) pre_rip
  have f139 : InstrSpec 0x10021b [0x89, 0xD6] (fun s => s.RIP = 0x10021b) (movR32R32Effect 0x10021b 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10021b 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x10021b 0xd6 (by decide)) pre_rip
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f120 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 286), (1, 274), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 284), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001dc) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f121 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 288), (1, 274), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 284), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001e0) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.exec (n := 290) (ρ' := [(0, 288), (1, 274), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 284), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001e5) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f123 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 288), (1, 291), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 284), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001e7) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f124 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 288), (1, 291), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001ea) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f125 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 288), (1, 295), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001ee) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f126 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 297), (1, 295), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001f3) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f127 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 300) (ρ' := [(0, 297), (1, 299), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001f9) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 301) (RestInside.out (n := 301) f128 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 302) (ρ' := [(0, 297), (1, 301), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001fb) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 303) (RestInside.out (n := 303) f129 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 304) (ρ' := [(0, 297), (1, 301), (2, 280), (3, 213), (4, 65), (5, 191), (6, 303), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001fe) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 305) (RestInside.out (n := 305) f130 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 306) (ρ' := [(0, 297), (1, 301), (2, 305), (3, 213), (4, 65), (5, 191), (6, 303), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100202) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f131 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 308) (ρ' := [(0, 297), (1, 301), (2, 307), (3, 213), (4, 65), (5, 191), (6, 303), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100205) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f132 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 297), (1, 301), (2, 307), (3, 213), (4, 65), (5, 191), (6, 309), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100208) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f133 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 297), (1, 301), (2, 307), (3, 213), (4, 65), (5, 191), (6, 311), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10020a) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.exec (n := 313) (ρ' := [(0, 297), (1, 301), (2, 307), (3, 213), (4, 65), (5, 191), (6, 311), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10020e) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f135 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 314), (1, 301), (2, 307), (3, 213), (4, 65), (5, 191), (6, 311), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100210) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f136 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 316), (1, 301), (2, 307), (3, 213), (4, 65), (5, 191), (6, 311), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100214) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f137 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 318), (1, 301), (2, 307), (3, 213), (4, 65), (5, 191), (6, 311), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100219) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f138 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 318), (1, 320), (2, 307), (3, 213), (4, 65), (5, 191), (6, 311), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10021b) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f139 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 318), (1, 320), (2, 307), (3, 213), (4, 65), (5, 191), (6, 322), (7, 7), (8, 293), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10021d) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_7 code

theorem rest_l100000_5 [Bindings] (code : CodeMap) :
    Rest (n := 247) code lifted (codeRange 0x100000 bytes_l100000) [(0, 245), (1, 236), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]
      79 0x100197 bytes_l100000_5 b_l100000_5 := by
  have f100 : InstrSpec 0x100197 [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x100197) (movR32R32Effect 0x100197 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x100197 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100197 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x10019a [0x66, 0xC1, 0xC1, 0x0A] (fun s => s.RIP = 0x10019a) (rolR16Effect 0x10019a 4 1 10)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x10019a 4 1 10).toInstrSpec (rol_r16_imm8_effect_step 0x10019a 0xc1 0xa (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x10019e [0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x10019e) (andR32Imm32Effect 0x10019e 6 1 0xffffcccc)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10019e 6 1 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x10019e 0xe1 0xffffcccc (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x1001a4 [0x09, 0xC1] (fun s => s.RIP = 0x1001a4) (orR32R32Effect 0x1001a4 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1001a4 2 1 0).toInstrSpec (or_r32_r32_effect_step 0x1001a4 0xc1 (by decide)) pre_rip
  have f104 : InstrSpec 0x1001a6 [0x44, 0x31, 0xEA] (fun s => s.RIP = 0x1001a6) (xorR32R32Effect 0x1001a6 3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1001a6 3 2 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1001a6 0x44 0xea (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x1001a9 [0x44, 0x31, 0xE6] (fun s => s.RIP = 0x1001a9) (xorR32R32Effect 0x1001a9 3 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1001a9 3 6 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x1001a9 0x44 0xe6 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x1001ac [0x31, 0xCA] (fun s => s.RIP = 0x1001ac) (xorR32R32Effect 0x1001ac 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1001ac 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1001ac 0xca (by decide)) pre_rip
  have f107 : InstrSpec 0x1001ae [0x66, 0x89, 0x57, 0x04] (StorePre 0x1001ae 4 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x1001ae + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1001ae 4 2 (.base 7 (.d8 0x4)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM16R16Effect_footprint 0x1001ae 4 2 (.base 7 (.d8 0x4))).toInstrSpec (mov_m16_r16_effect_step 0x1001ae 2 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f108 : InstrSpec 0x1001b2 [0x89, 0xF0] (fun s => s.RIP = 0x1001b2) (movR32R32Effect 0x1001b2 2 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1001b2 2 0 6).toInstrSpec (mov_r32_r32_effect_step 0x1001b2 0xf0 (by decide)) pre_rip
  have f109 : InstrSpec 0x1001b4 [0x66, 0xC1, 0xC0, 0x06] (fun s => s.RIP = 0x1001b4) (rolR16Effect 0x1001b4 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1001b4 4 0 6).toInstrSpec (rol_r16_imm8_effect_step 0x1001b4 0xc0 0x6 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x1001b8 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x1001b8) (andEaxImm32Effect 0x1001b8 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1001b8 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x1001b8 0x3333) pre_rip
  have f111 : InstrSpec 0x1001bd [0x89, 0xF1] (fun s => s.RIP = 0x1001bd) (movR32R32Effect 0x1001bd 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1001bd 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x1001bd 0xf1 (by decide)) pre_rip
  have f112 : InstrSpec 0x1001bf [0x66, 0xC1, 0xC1, 0x0A] (fun s => s.RIP = 0x1001bf) (rolR16Effect 0x1001bf 4 1 10)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x1001bf 4 1 10).toInstrSpec (rol_r16_imm8_effect_step 0x1001bf 0xc1 0xa (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x1001c3 [0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x1001c3) (andR32Imm32Effect 0x1001c3 6 1 0xffffcccc)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1001c3 6 1 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x1001c3 0xe1 0xffffcccc (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x1001c9 [0x09, 0xC1] (fun s => s.RIP = 0x1001c9) (orR32R32Effect 0x1001c9 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1001c9 2 1 0).toInstrSpec (or_r32_r32_effect_step 0x1001c9 0xc1 (by decide)) pre_rip
  have f115 : InstrSpec 0x1001cb [0x45, 0x31, 0xE0] (fun s => s.RIP = 0x1001cb) (xorR32R32Effect 0x1001cb 3 8 12)
      [.gpr 8, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1001cb 3 8 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x1001cb 0x45 0xe0 (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x1001ce [0x8B, 0x14, 0x24] (LoadPre 0x1001ce (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1001ce + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1001ce 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1001ce 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x1001ce 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f117 : InstrSpec 0x1001d1 [0x44, 0x31, 0xFA] (fun s => s.RIP = 0x1001d1) (xorR32R32Effect 0x1001d1 3 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1001d1 3 2 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x1001d1 0x44 0xfa (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x1001d4 [0x45, 0x31, 0xD8] (fun s => s.RIP = 0x1001d4) (xorR32R32Effect 0x1001d4 3 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1001d4 3 8 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1001d4 0x45 0xd8 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x1001d7 [0x41, 0x31, 0xC8] (fun s => s.RIP = 0x1001d7) (xorR32R32Effect 0x1001d7 3 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1001d7 3 8 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x1001d7 0x41 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 245), (1, 247), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10019a) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f101 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 245), (1, 249), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10019e) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f102 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 245), (1, 251), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001a4) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f103 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 245), (1, 253), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001a6) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f104 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 245), (1, 253), (2, 255), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001a9) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f105 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 245), (1, 253), (2, 255), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001ac) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f106 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 245), (1, 253), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001ae) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.exec (n := 261) (ρ' := [(0, 245), (1, 253), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001b2) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f108 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 262), (1, 253), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001b4) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f109 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 264), (1, 253), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001b8) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f110 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 266), (1, 253), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001bd) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f111 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 266), (1, 268), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001bf) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f112 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 266), (1, 270), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001c3) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f113 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 266), (1, 272), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001c9) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f114 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 266), (1, 274), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001cb) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f115 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 266), (1, 274), (2, 259), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 276), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001ce) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f116 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 266), (1, 274), (2, 278), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 276), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001d1) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f117 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 266), (1, 274), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 276), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001d4) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f118 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 266), (1, 274), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 282), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001d7) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f119 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 266), (1, 274), (2, 280), (3, 213), (4, 65), (5, 191), (6, 257), (7, 7), (8, 284), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1001da) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_6 code

theorem rest_l100000_4 [Bindings] (code : CodeMap) :
    Rest (n := 209) code lifted (codeRange 0x100000 bytes_l100000) [(0, 207), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]
      99 0x100150 bytes_l100000_4 b_l100000_4 := by
  have f80 : InstrSpec 0x100150 [0x41, 0x31, 0xEB] (fun s => s.RIP = 0x100150) (xorR32R32Effect 0x100150 3 11 5)
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100150 3 11 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x100150 0x41 0xeb (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x100153 [0x44, 0x31, 0xDB] (fun s => s.RIP = 0x100153) (xorR32R32Effect 0x100153 3 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100153 3 3 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100153 0x44 0xdb (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x100156 [0x31, 0xC3] (fun s => s.RIP = 0x100156) (xorR32R32Effect 0x100156 2 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100156 2 3 0).toInstrSpec (xor_r32_r32_effect_step 0x100156 0xc3 (by decide)) pre_rip
  have f83 : InstrSpec 0x100158 [0x66, 0x89, 0x1F] (StorePre 0x100158 3 (fun s => AddrMode.addr (.base 7 .none) s (0x100158 + BitVec.ofNat 64 3)) 2) (movM16R16Effect 0x100158 3 3 (.base 7 .none))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM16R16Effect_footprint 0x100158 3 3 (.base 7 .none)).toInstrSpec (mov_m16_r16_effect_step 0x100158 3 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f84 : InstrSpec 0x10015b [0x44, 0x31, 0xCA] (fun s => s.RIP = 0x10015b) (xorR32R32Effect 0x10015b 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10015b 3 2 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10015b 0x44 0xca (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x10015e [0x89, 0xD0] (fun s => s.RIP = 0x10015e) (movR32R32Effect 0x10015e 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10015e 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x10015e 0xd0 (by decide)) pre_rip
  have f86 : InstrSpec 0x100160 [0x66, 0xC1, 0xC0, 0x06] (fun s => s.RIP = 0x100160) (rolR16Effect 0x100160 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x100160 4 0 6).toInstrSpec (rol_r16_imm8_effect_step 0x100160 0xc0 0x6 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x100164 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x100164) (andEaxImm32Effect 0x100164 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x100164 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x100164 0x3333) pre_rip
  have f88 : InstrSpec 0x100169 [0x41, 0x89, 0xD2] (fun s => s.RIP = 0x100169) (movR32R32Effect 0x100169 3 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100169 3 10 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x100169 0x41 0xd2 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x10016c [0x66, 0x41, 0xC1, 0xC2, 0x0A] (fun s => s.RIP = 0x10016c) (rolR16Effect 0x10016c 5 10 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x10016c 5 10 10).toInstrSpec (rol_r16_imm8_rex_effect_step 0x10016c 0x41 0xc2 0xa (by decide) (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x100171 [0x41, 0x81, 0xE2, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x100171) (andR32Imm32Effect 0x100171 7 10 0xffffcccc)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100171 7 10 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x100171 0x41 0xe2 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x100178 [0x41, 0x09, 0xC2] (fun s => s.RIP = 0x100178) (orR32R32Effect 0x100178 3 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (orR32R32Effect_footprint 0x100178 3 10 0).toInstrSpec (or_r32_r32_rex_effect_step 0x100178 0x41 0xc2 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x10017b [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x10017b) (xorR32R32Effect 0x10017b 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10017b 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10017b 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x10017e [0x44, 0x31, 0xD9] (fun s => s.RIP = 0x10017e) (xorR32R32Effect 0x10017e 3 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10017e 3 1 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10017e 0x44 0xd9 (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x100181 [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x100181) (xorR32R32Effect 0x100181 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100181 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x100181 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x100184 [0x45, 0x31, 0xE8] (fun s => s.RIP = 0x100184) (xorR32R32Effect 0x100184 3 8 13)
      [.gpr 8, .gpr 13] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100184 3 8 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100184 0x45 0xe8 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x100187 [0x66, 0x89, 0x4F, 0x02] (StorePre 0x100187 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x100187 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100187 4 1 (.base 7 (.d8 0x2)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM16R16Effect_footprint 0x100187 4 1 (.base 7 (.d8 0x2))).toInstrSpec (mov_m16_r16_effect_step 0x100187 1 (.base 7 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f97 : InstrSpec 0x10018b [0x44, 0x89, 0xC0] (fun s => s.RIP = 0x10018b) (movR32R32Effect 0x10018b 3 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10018b 3 0 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x10018b 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x10018e [0x66, 0xC1, 0xC0, 0x06] (fun s => s.RIP = 0x10018e) (rolR16Effect 0x10018e 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x10018e 4 0 6).toInstrSpec (rol_r16_imm8_effect_step 0x10018e 0xc0 0x6 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x100192 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x100192) (andEaxImm32Effect 0x100192 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x100192 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x100192 0x3333) pre_rip
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f80 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 207), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100153) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f81 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 207), (1, 193), (2, 69), (3, 211), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100156) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f82 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 207), (1, 193), (2, 69), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100158) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.exec (n := 215) (ρ' := [(0, 207), (1, 193), (2, 69), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10015b) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f84 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 207), (1, 193), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10015e) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f85 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 218), (1, 193), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100160) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f86 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 220), (1, 193), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100164) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f87 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 222), (1, 193), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100169) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f88 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 222), (1, 193), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 224), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10016c) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f89 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 222), (1, 193), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 226), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100171) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f90 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 229) (ρ' := [(0, 222), (1, 193), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 228), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100178) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f91 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 222), (1, 193), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10017b) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f92 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 222), (1, 232), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10017e) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 222), (1, 234), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100181) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f94 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 222), (1, 236), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100184) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f95 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 222), (1, 236), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100187) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.exec (n := 240) (ρ' := [(0, 222), (1, 236), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10018b) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f97 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 241), (1, 236), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10018e) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f98 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 243), (1, 236), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100192) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 245), (1, 236), (2, 216), (3, 213), (4, 65), (5, 191), (6, 73), (7, 7), (8, 238), (9, 107), (10, 230), (11, 209), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100197) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_5 code

theorem rest_l100000_3 [Bindings] (code : CodeMap) :
    Rest (n := 170) code lifted (codeRange 0x100000 bytes_l100000) [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 168), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]
      119 0x1000ff bytes_l100000_3 b_l100000_3 := by
  have f60 : InstrSpec 0x1000ff [0x66, 0xD1, 0xC8] (fun s => s.RIP = 0x1000ff) (rorR16Effect 0x1000ff 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rorR16Effect_footprint 0x1000ff 3 0 1).toInstrSpec (ror_r16_one_effect_step 0x1000ff 0xc8 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x100102 [0x25, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x100102) (andEaxImm32Effect 0x100102 0xffff8888)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x100102 0xffff8888).toInstrSpec (and_eax_imm32_effect_step 0x100102 0xffff8888) pre_rip
  have f62 : InstrSpec 0x100107 [0x44, 0x09, 0xD0] (fun s => s.RIP = 0x100107) (orR32R32Effect 0x100107 3 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR32R32Effect_footprint 0x100107 3 0 10).toInstrSpec (or_r32_r32_rex_effect_step 0x100107 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x10010a [0x89, 0x44, 0x24, 0x08] (StorePre 0x10010a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10010a + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10010a 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10010a 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x10010a 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f64 : InstrSpec 0x10010e [0x44, 0x0F, 0xB7, 0x5F, 0x0E] (LoadPre 0x10010e (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x10010e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10010e 5 11 (.base 7 (.d8 0xe)))
      [.gpr 7] [] [.reg 11, .rip] :=
    (movzxR32M16Effect_footprint 0x10010e 5 11 (.base 7 (.d8 0xe))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10010e 0x44 (by decide) 3 (.base 7 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f65 : InstrSpec 0x100113 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x100113) (movR32R32Effect 0x100113 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100113 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x100113 0x45 0xda (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x100116 [0x66, 0x41, 0xC1, 0xC2, 0x0B] (fun s => s.RIP = 0x100116) (rolR16Effect 0x100116 5 10 11)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x100116 5 10 11).toInstrSpec (rol_r16_imm8_rex_effect_step 0x100116 0x41 0xc2 0xb (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x10011b [0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00] (fun s => s.RIP = 0x10011b) (andR32Imm32Effect 0x10011b 7 10 0x7777)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10011b 7 10 0x7777).toInstrSpec (and_r32_imm32_rex_effect_step 0x10011b 0x41 0xe2 0x7777 (by decide) (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x100122 [0x44, 0x89, 0xDD] (fun s => s.RIP = 0x100122) (movR32R32Effect 0x100122 3 5 11)
      [.gpr 11] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x100122 3 5 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x100122 0x44 0xdd (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x100125 [0x66, 0xD1, 0xCD] (fun s => s.RIP = 0x100125) (rorR16Effect 0x100125 3 5 1)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rorR16Effect_footprint 0x100125 3 5 1).toInstrSpec (ror_r16_one_effect_step 0x100125 0xcd (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x100128 [0x81, 0xE5, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x100128) (andR32Imm32Effect 0x100128 6 5 0xffff8888)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100128 6 5 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x100128 0xe5 0xffff8888 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x10012e [0x44, 0x09, 0xD5] (fun s => s.RIP = 0x10012e) (orR32R32Effect 0x10012e 3 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10012e 3 5 10).toInstrSpec (or_r32_r32_rex_effect_step 0x10012e 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x100131 [0x31, 0xD9] (fun s => s.RIP = 0x100131) (xorR32R32Effect 0x100131 2 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100131 2 1 3).toInstrSpec (xor_r32_r32_effect_step 0x100131 0xd9 (by decide)) pre_rip
  have f73 : InstrSpec 0x100133 [0x41, 0x89, 0xCA] (fun s => s.RIP = 0x100133) (movR32R32Effect 0x100133 3 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100133 3 10 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x100133 0x41 0xca (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x100136 [0x66, 0x41, 0xC1, 0xC2, 0x06] (fun s => s.RIP = 0x100136) (rolR16Effect 0x100136 5 10 6)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x100136 5 10 6).toInstrSpec (rol_r16_imm8_rex_effect_step 0x100136 0x41 0xc2 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x10013b [0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10013b) (andR32Imm32Effect 0x10013b 7 10 0x3333)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10013b 7 10 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x10013b 0x41 0xe2 0x3333 (by decide) (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x100142 [0x89, 0xC8] (fun s => s.RIP = 0x100142) (movR32R32Effect 0x100142 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x100142 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x100142 0xc8 (by decide)) pre_rip
  have f77 : InstrSpec 0x100144 [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x100144) (rolR16Effect 0x100144 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x100144 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x100144 0xc0 0xa (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x100148 [0x25, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x100148) (andEaxImm32Effect 0x100148 0xffffcccc)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x100148 0xffffcccc).toInstrSpec (and_eax_imm32_effect_step 0x100148 0xffffcccc) pre_rip
  have f79 : InstrSpec 0x10014d [0x44, 0x09, 0xD0] (fun s => s.RIP = 0x10014d) (orR32R32Effect 0x10014d 3 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10014d 3 0 10).toInstrSpec (or_r32_r32_rex_effect_step 0x10014d 0x44 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 170), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 168), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100102) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f61 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 172), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 168), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100107) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f62 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 168), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10010a) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.exec (n := 176) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 168), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10010e) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 168), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100113) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f65 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 179), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100116) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 181), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10011b) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 183), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100122) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 185), (6, 73), (7, 7), (8, 71), (9, 107), (10, 183), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100125) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 187), (6, 73), (7, 7), (8, 71), (9, 107), (10, 183), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100128) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 189), (6, 73), (7, 7), (8, 71), (9, 107), (10, 183), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10012e) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 174), (1, 67), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 183), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100131) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 174), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 183), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100133) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 174), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 195), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100136) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 174), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 197), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10013b) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f75 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 174), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100142) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f76 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 201), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100144) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f77 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 203), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100148) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 205), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10014d) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f79 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 207), (1, 193), (2, 69), (3, 97), (4, 65), (5, 191), (6, 73), (7, 7), (8, 71), (9, 107), (10, 199), (11, 177), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100150) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_4 code

theorem rest_l100000_2 [Bindings] (code : CodeMap) :
    Rest (n := 133) code lifted (codeRange 0x100000 bytes_l100000) [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 127), (12, 131), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]
      139 0x10009f bytes_l100000_2 b_l100000_2 := by
  have f40 : InstrSpec 0x10009f [0x41, 0x81, 0xE4, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x10009f) (andR32Imm32Effect 0x10009f 7 12 0xffff8888)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10009f 7 12 0xffff8888).toInstrSpec (and_r32_imm32_rex_effect_step 0x10009f 0x41 0xe4 0xffff8888 (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x1000a6 [0x45, 0x09, 0xD4] (fun s => s.RIP = 0x1000a6) (orR32R32Effect 0x1000a6 3 12 10)
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1000a6 3 12 10).toInstrSpec (or_r32_r32_rex_effect_step 0x1000a6 0x45 0xd4 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x1000a9 [0x44, 0x89, 0x3C, 0x24] (StorePre 0x1000a9 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1000a9 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1000a9 15 (.sib 4 none 0 .none))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1000a9 15 (.sib 4 none 0 .none)).toInstrSpec (mov_m32_r32_effect_step 0x1000a9 0x44 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x1000ad [0x45, 0x89, 0xFA] (fun s => s.RIP = 0x1000ad) (movR32R32Effect 0x1000ad 3 10 15)
      [.gpr 15] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1000ad 3 10 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1000ad 0x45 0xfa (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1000b0 [0x66, 0x41, 0xC1, 0xC2, 0x0B] (fun s => s.RIP = 0x1000b0) (rolR16Effect 0x1000b0 5 10 11)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x1000b0 5 10 11).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1000b0 0x41 0xc2 0xb (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1000b5 [0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00] (fun s => s.RIP = 0x1000b5) (andR32Imm32Effect 0x1000b5 7 10 0x7777)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1000b5 7 10 0x7777).toInstrSpec (and_r32_imm32_rex_effect_step 0x1000b5 0x41 0xe2 0x7777 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x1000bc [0x66, 0x41, 0xD1, 0xCF] (fun s => s.RIP = 0x1000bc) (rorR16Effect 0x1000bc 4 15 1)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rorR16Effect_footprint 0x1000bc 4 15 1).toInstrSpec (ror_r16_one_rex_effect_step 0x1000bc 0x41 0xcf (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x1000c0 [0x41, 0x81, 0xE7, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x1000c0) (andR32Imm32Effect 0x1000c0 7 15 0xffff8888)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1000c0 7 15 0xffff8888).toInstrSpec (and_r32_imm32_rex_effect_step 0x1000c0 0x41 0xe7 0xffff8888 (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x1000c7 [0x44, 0x89, 0x74, 0x24, 0x04] (StorePre 0x1000c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1000c7 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1000c7 14 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1000c7 14 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x1000c7 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x1000cc [0x45, 0x89, 0xF3] (fun s => s.RIP = 0x1000cc) (movR32R32Effect 0x1000cc 3 11 14)
      [.gpr 14] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1000cc 3 11 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x1000cc 0x45 0xf3 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x1000cf [0x66, 0x41, 0xC1, 0xC3, 0x0B] (fun s => s.RIP = 0x1000cf) (rolR16Effect 0x1000cf 5 11 11)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR16Effect_footprint 0x1000cf 5 11 11).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1000cf 0x41 0xc3 0xb (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x1000d4 [0x45, 0x09, 0xD7] (fun s => s.RIP = 0x1000d4) (orR32R32Effect 0x1000d4 3 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1000d4 3 15 10).toInstrSpec (or_r32_r32_rex_effect_step 0x1000d4 0x45 0xd7 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x1000d7 [0x66, 0x41, 0xD1, 0xCE] (fun s => s.RIP = 0x1000d7) (rorR16Effect 0x1000d7 4 14 1)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rorR16Effect_footprint 0x1000d7 4 14 1).toInstrSpec (ror_r16_one_rex_effect_step 0x1000d7 0x41 0xce (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x1000db [0x41, 0x81, 0xE3, 0x77, 0x77, 0x00, 0x00] (fun s => s.RIP = 0x1000db) (andR32Imm32Effect 0x1000db 7 11 0x7777)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1000db 7 11 0x7777).toInstrSpec (and_r32_imm32_rex_effect_step 0x1000db 0x41 0xe3 0x7777 (by decide) (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x1000e2 [0x41, 0x81, 0xE6, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x1000e2) (andR32Imm32Effect 0x1000e2 7 14 0xffff8888)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1000e2 7 14 0xffff8888).toInstrSpec (and_r32_imm32_rex_effect_step 0x1000e2 0x41 0xe6 0xffff8888 (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x1000e9 [0x45, 0x09, 0xDE] (fun s => s.RIP = 0x1000e9) (orR32R32Effect 0x1000e9 3 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1000e9 3 14 11).toInstrSpec (or_r32_r32_rex_effect_step 0x1000e9 0x45 0xde (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x1000ec [0x89, 0x44, 0x24, 0x0C] (StorePre 0x1000ec 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1000ec + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1000ec 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1000ec 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x1000ec 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x1000f0 [0x41, 0x89, 0xC2] (fun s => s.RIP = 0x1000f0) (movR32R32Effect 0x1000f0 3 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1000f0 3 10 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x1000f0 0x41 0xc2 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x1000f3 [0x66, 0x41, 0xC1, 0xC2, 0x0B] (fun s => s.RIP = 0x1000f3) (rolR16Effect 0x1000f3 5 10 11)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x1000f3 5 10 11).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1000f3 0x41 0xc2 0xb (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x1000f8 [0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00] (fun s => s.RIP = 0x1000f8) (andR32Imm32Effect 0x1000f8 7 10 0x7777)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1000f8 7 10 0x7777).toInstrSpec (and_r32_imm32_rex_effect_step 0x1000f8 0x41 0xe2 0x7777 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f40 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 127), (12, 133), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000a6) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f41 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 127), (12, 135), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000a9) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 127), (12, 135), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000ad) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f43 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 138), (12, 135), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000b0) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f44 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 140), (12, 135), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000b5) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f45 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (12, 135), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000bc) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f46 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (12, 135), (13, 121), (14, 77), (15, 144), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000c0) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f47 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (12, 135), (13, 121), (14, 77), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000c7) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (12, 135), (13, 121), (14, 77), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000cc) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f49 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (11, 149), (12, 135), (13, 121), (14, 77), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000cf) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f50 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (11, 151), (12, 135), (13, 121), (14, 77), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000d4) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f51 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (11, 151), (12, 135), (13, 121), (14, 77), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000d7) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f52 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (11, 151), (12, 135), (13, 121), (14, 155), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000db) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f53 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (11, 157), (12, 135), (13, 121), (14, 155), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000e2) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f54 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (11, 157), (12, 135), (13, 121), (14, 159), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000e9) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f55 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000ec) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.exec (n := 163) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 142), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000f0) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f57 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 164), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000f3) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f58 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 166), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000f8) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f59 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 168), (11, 157), (12, 135), (13, 121), (14, 161), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1000ff) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_3 code

theorem rest_l100000_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x100000 bytes_l100000) [(0, 79), (1, 67), (2, 69), (3, 91), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 85), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]
      159 0x100046 bytes_l100000_1 b_l100000_1 := by
  have f20 : InstrSpec 0x100046 [0x41, 0x89, 0xD2] (fun s => s.RIP = 0x100046) (movR32R32Effect 0x100046 3 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100046 3 10 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x100046 0x41 0xd2 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x100049 [0x66, 0x41, 0xC1, 0xC2, 0x0B] (fun s => s.RIP = 0x100049) (rolR16Effect 0x100049 5 10 11)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x100049 5 10 11).toInstrSpec (rol_r16_imm8_rex_effect_step 0x100049 0x41 0xc2 0xb (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10004e [0x44, 0x09, 0xCB] (fun s => s.RIP = 0x10004e) (orR32R32Effect 0x10004e 3 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10004e 3 3 9).toInstrSpec (or_r32_r32_rex_effect_step 0x10004e 0x44 0xcb (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x100051 [0x41, 0x89, 0xD1] (fun s => s.RIP = 0x100051) (movR32R32Effect 0x100051 3 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x100051 3 9 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x100051 0x41 0xd1 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x100054 [0x66, 0x41, 0xD1, 0xC9] (fun s => s.RIP = 0x100054) (rorR16Effect 0x100054 4 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rorR16Effect_footprint 0x100054 4 9 1).toInstrSpec (ror_r16_one_rex_effect_step 0x100054 0x41 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x100058 [0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00] (fun s => s.RIP = 0x100058) (andR32Imm32Effect 0x100058 7 10 0x7777)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100058 7 10 0x7777).toInstrSpec (and_r32_imm32_rex_effect_step 0x100058 0x41 0xe2 0x7777 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10005f [0x41, 0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x10005f) (andR32Imm32Effect 0x10005f 7 9 0xffff8888)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10005f 7 9 0xffff8888).toInstrSpec (and_r32_imm32_rex_effect_step 0x10005f 0x41 0xe1 0xffff8888 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x100066 [0x45, 0x09, 0xD1] (fun s => s.RIP = 0x100066) (orR32R32Effect 0x100066 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (orR32R32Effect_footprint 0x100066 3 9 10).toInstrSpec (or_r32_r32_rex_effect_step 0x100066 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x100069 [0x45, 0x89, 0xC2] (fun s => s.RIP = 0x100069) (movR32R32Effect 0x100069 3 10 8)
      [.gpr 8] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100069 3 10 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100069 0x45 0xc2 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10006c [0x66, 0x41, 0xC1, 0xC2, 0x0B] (fun s => s.RIP = 0x10006c) (rolR16Effect 0x10006c 5 10 11)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x10006c 5 10 11).toInstrSpec (rol_r16_imm8_rex_effect_step 0x10006c 0x41 0xc2 0xb (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x100071 [0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00] (fun s => s.RIP = 0x100071) (andR32Imm32Effect 0x100071 7 10 0x7777)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100071 7 10 0x7777).toInstrSpec (and_r32_imm32_rex_effect_step 0x100071 0x41 0xe2 0x7777 (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x100078 [0x45, 0x89, 0xC5] (fun s => s.RIP = 0x100078) (movR32R32Effect 0x100078 3 13 8)
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x100078 3 13 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100078 0x45 0xc5 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10007b [0x66, 0x41, 0xD1, 0xCD] (fun s => s.RIP = 0x10007b) (rorR16Effect 0x10007b 4 13 1)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rorR16Effect_footprint 0x10007b 4 13 1).toInstrSpec (ror_r16_one_rex_effect_step 0x10007b 0x41 0xcd (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10007f [0x41, 0x81, 0xE5, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x10007f) (andR32Imm32Effect 0x10007f 7 13 0xffff8888)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10007f 7 13 0xffff8888).toInstrSpec (and_r32_imm32_rex_effect_step 0x10007f 0x41 0xe5 0xffff8888 (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x100086 [0x45, 0x09, 0xD5] (fun s => s.RIP = 0x100086) (orR32R32Effect 0x100086 3 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (orR32R32Effect_footprint 0x100086 3 13 10).toInstrSpec (or_r32_r32_rex_effect_step 0x100086 0x45 0xd5 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x100089 [0x41, 0x89, 0xF2] (fun s => s.RIP = 0x100089) (movR32R32Effect 0x100089 3 10 6)
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100089 3 10 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x100089 0x41 0xf2 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10008c [0x66, 0x41, 0xC1, 0xC2, 0x0B] (fun s => s.RIP = 0x10008c) (rolR16Effect 0x10008c 5 10 11)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x10008c 5 10 11).toInstrSpec (rol_r16_imm8_rex_effect_step 0x10008c 0x41 0xc2 0xb (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x100091 [0x41, 0x81, 0xE2, 0x77, 0x77, 0x00, 0x00] (fun s => s.RIP = 0x100091) (andR32Imm32Effect 0x100091 7 10 0x7777)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100091 7 10 0x7777).toInstrSpec (and_r32_imm32_rex_effect_step 0x100091 0x41 0xe2 0x7777 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x100098 [0x41, 0x89, 0xF4] (fun s => s.RIP = 0x100098) (movR32R32Effect 0x100098 3 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x100098 3 12 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x100098 0x41 0xf4 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10009b [0x66, 0x41, 0xD1, 0xCC] (fun s => s.RIP = 0x10009b) (rorR16Effect 0x10009b 4 12 1)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (rorR16Effect_footprint 0x10009b 4 12 1).toInstrSpec (ror_r16_one_rex_effect_step 0x10009b 0x41 0xcc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 91), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 85), (10, 93), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100049) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 91), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 85), (10, 95), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10004e) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 85), (10, 95), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100051) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 99), (10, 95), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100054) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 101), (10, 95), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100058) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 101), (10, 103), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10005f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 105), (10, 103), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100066) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 103), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100069) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 109), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10006c) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 111), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100071) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 113), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100078) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 113), (12, 12), (13, 115), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10007b) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 113), (12, 12), (13, 117), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10007f) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 113), (12, 12), (13, 119), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100086) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 113), (12, 12), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100089) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 123), (12, 12), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10008c) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 125), (12, 12), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100091) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 127), (12, 12), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100098) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f38 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 127), (12, 129), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10009b) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f39 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 97), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 107), (10, 127), (12, 131), (13, 121), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10009f) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_2 code

theorem rest_l100000 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100000 bytes_l100000) (entryMap (live .l100000))
      179 0x100000 bytes_l100000 b_l100000 := by
  have f0 : InstrSpec 0x100000 [0x55] (PushPre 0x100000 1) (pushR64Effect 0x100000 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100000 1 5).toInstrSpec (push_r64_effect_step 0x100000 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x100001 [0x41, 0x57] (PushPre 0x100001 2) (pushR64Effect 0x100001 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100001 2 15).toInstrSpec (push_r64_rex_effect_step 0x100001 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100003 [0x41, 0x56] (PushPre 0x100003 2) (pushR64Effect 0x100003 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100003 2 14).toInstrSpec (push_r64_rex_effect_step 0x100003 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100005 [0x41, 0x55] (PushPre 0x100005 2) (pushR64Effect 0x100005 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100005 2 13).toInstrSpec (push_r64_rex_effect_step 0x100005 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100007 [0x41, 0x54] (PushPre 0x100007 2) (pushR64Effect 0x100007 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100007 2 12).toInstrSpec (push_r64_rex_effect_step 0x100007 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100009 [0x53] (PushPre 0x100009 1) (pushR64Effect 0x100009 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100009 1 3).toInstrSpec (push_r64_effect_step 0x100009 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10000a [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x10000a) (subR64Imm8Effect 0x10000a 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10000a 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x10000a 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10000e [0x0F, 0xB7, 0x0F] (LoadPre 0x10000e (fun s => AddrMode.addr (.base 7 .none) s (0x10000e + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x10000e 3 1 (.base 7 .none))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x10000e 3 1 (.base 7 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x10000e 1 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100011 [0x0F, 0xB7, 0x57, 0x02] (LoadPre 0x100011 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x100011 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100011 4 2 (.base 7 (.d8 0x2)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x100011 4 2 (.base 7 (.d8 0x2))).toInstrSpec (movzx_r32_m16_effect_step 0x100011 2 (.base 7 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100015 [0x44, 0x0F, 0xB7, 0x47, 0x04] (LoadPre 0x100015 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x100015 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x100015 5 8 (.base 7 (.d8 0x4)))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x100015 5 8 (.base 7 (.d8 0x4))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x100015 0x44 (by decide) 0 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10001a [0x0F, 0xB7, 0x77, 0x06] (LoadPre 0x10001a (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x10001a + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10001a 4 6 (.base 7 (.d8 0x6)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x10001a 4 6 (.base 7 (.d8 0x6))).toInstrSpec (movzx_r32_m16_effect_step 0x10001a 6 (.base 7 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10001e [0x44, 0x0F, 0xB7, 0x7F, 0x08] (LoadPre 0x10001e (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10001e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10001e 5 15 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 15, .rip] :=
    (movzxR32M16Effect_footprint 0x10001e 5 15 (.base 7 (.d8 0x8))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10001e 0x44 (by decide) 7 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x100023 [0x44, 0x0F, 0xB7, 0x77, 0x0A] (LoadPre 0x100023 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x100023 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x100023 5 14 (.base 7 (.d8 0xa)))
      [.gpr 7] [] [.reg 14, .rip] :=
    (movzxR32M16Effect_footprint 0x100023 5 14 (.base 7 (.d8 0xa))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x100023 0x44 (by decide) 6 (.base 7 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x100028 [0x0F, 0xB7, 0x47, 0x0C] (LoadPre 0x100028 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x100028 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100028 4 0 (.base 7 (.d8 0xc)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x100028 4 0 (.base 7 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x100028 0 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10002c [0x41, 0x89, 0xC9] (fun s => s.RIP = 0x10002c) (movR32R32Effect 0x10002c 3 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10002c 3 9 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x10002c 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10002f [0x66, 0x41, 0xC1, 0xC1, 0x0B] (fun s => s.RIP = 0x10002f) (rolR16Effect 0x10002f 5 9 11)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR16Effect_footprint 0x10002f 5 9 11).toInstrSpec (rol_r16_imm8_rex_effect_step 0x10002f 0x41 0xc1 0xb (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x100034 [0x41, 0x81, 0xE1, 0x77, 0x77, 0x00, 0x00] (fun s => s.RIP = 0x100034) (andR32Imm32Effect 0x100034 7 9 0x7777)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100034 7 9 0x7777).toInstrSpec (and_r32_imm32_rex_effect_step 0x100034 0x41 0xe1 0x7777 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10003b [0x89, 0xCB] (fun s => s.RIP = 0x10003b) (movR32R32Effect 0x10003b 2 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x10003b 2 3 1).toInstrSpec (mov_r32_r32_effect_step 0x10003b 0xcb (by decide)) pre_rip
  have f18 : InstrSpec 0x10003d [0x66, 0xD1, 0xCB] (fun s => s.RIP = 0x10003d) (rorR16Effect 0x10003d 3 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (rorR16Effect_footprint 0x10003d 3 3 1).toInstrSpec (ror_r16_one_effect_step 0x10003d 0xcb (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x100040 [0x81, 0xE3, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x100040) (andR32Imm32Effect 0x100040 6 3 0xffff8888)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x100040 6 3 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x100040 0xe3 0xffff8888 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100001) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100003) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100005) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100007) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100009) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10000a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10000e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (3, 3), (4, 65), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100011) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100015) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 7), (8, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10001a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10001e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (12, 12), (13, 13), (14, 14), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100023) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100028) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10002c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 81), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10002f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 83), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100034) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 85), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10003b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 87), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 85), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10003d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 89), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 85), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100040) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 79), (1, 67), (2, 69), (3, 91), (4, 65), (5, 5), (6, 73), (7, 7), (8, 71), (9, 85), (12, 12), (13, 13), (14, 77), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100046) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100000_1 code

theorem block_l100000 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100000 :=
  Rest.liftedBlock (rest_l100000 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100000 x hx)

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

theorem_by block_l100000_eval :
    program.runBlock (dialect code) ⟨.l100000, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
