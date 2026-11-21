import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l109c00_5 [Bindings] (code : CodeMap) :
    Rest (n := 243) code lifted (codeRange 0x109c00 bytes_l109c00) [(0, 71), (1, 212), (2, 241), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x109d52 bytes_l109c00_5 b_l109c00_5 := by
  have f100 : InstrSpec 0x109d52 [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x109d52) (andR64R64Effect 0x109d52 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109d52 2 15).toInstrSpec (and_r64_r64_effect_step 0x109d52 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x109d55 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x109d55) (xorR64R64Effect 0x109d55 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109d55 2 0).toInstrSpec (xor_r64_r64_effect_step 0x109d55 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x109d58 [0x48, 0x89, 0x0F] (StorePre 0x109d58 3 (fun s => AddrMode.addr (.base 7 .none) s (0x109d58 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109d58 1 (.base 7 .none))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x109d58 1 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x109d58 0x48 (by decide) 1 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f103 : InstrSpec 0x109d5b [0x4C, 0x89, 0x57, 0x08] (StorePre 0x109d5b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x109d5b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d5b 10 (.base 7 (.d8 0x8)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x109d5b 10 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109d5b 0x4c (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f104 : InstrSpec 0x109d5f [0x48, 0x89, 0x77, 0x10] (StorePre 0x109d5f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x109d5f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d5f 6 (.base 7 (.d8 0x10)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x109d5f 6 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109d5f 0x48 (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f105 : InstrSpec 0x109d63 [0x48, 0x89, 0x57, 0x18] (StorePre 0x109d63 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x109d63 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d63 2 (.base 7 (.d8 0x18)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x109d63 2 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109d63 0x48 (by decide) 2 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f106 : InstrSpec 0x109d67 [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x109d67) (addR64Imm8Effect 0x109d67 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109d67 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x109d67 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x109d6b [0x5B] (PopPre 0x109d6b) (popR64Effect 0x109d6b 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109d6b 1 3).toInstrSpec (pop_r64_effect_step 0x109d6b 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f108 : InstrSpec 0x109d6c [0x41, 0x5C] (PopPre 0x109d6c) (popR64Effect 0x109d6c 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109d6c 2 12).toInstrSpec (pop_r64_rex_effect_step 0x109d6c 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f109 : InstrSpec 0x109d6e [0x41, 0x5D] (PopPre 0x109d6e) (popR64Effect 0x109d6e 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109d6e 2 13).toInstrSpec (pop_r64_rex_effect_step 0x109d6e 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f110 : InstrSpec 0x109d70 [0x41, 0x5E] (PopPre 0x109d70) (popR64Effect 0x109d70 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109d70 2 14).toInstrSpec (pop_r64_rex_effect_step 0x109d70 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f111 : InstrSpec 0x109d72 [0x41, 0x5F] (PopPre 0x109d72) (popR64Effect 0x109d72 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109d72 2 15).toInstrSpec (pop_r64_rex_effect_step 0x109d72 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f112 : InstrSpec 0x109d74 [0xC3] (RetPre 0x109d74) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109d74).toInstrSpec (ret_effect_step 0x109d74) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f100 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 71), (1, 212), (2, 243), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d55) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f101 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d58) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.exec (n := 247) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d5b) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 248) (RestInside.exec (n := 248) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d5f) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 249) (RestInside.exec (n := 249) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d63) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 250) (RestInside.exec (n := 250) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d67) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f106 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 228), (4, 251), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d6b) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f107 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 254) f107 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 255) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 253), (4, 254), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d6c) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f108 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 257) f108 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 258) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 253), (4, 257), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (12, 256), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d6e) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f109 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 260) f109 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 261) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 253), (4, 260), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (12, 256), (13, 259), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d70) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f110 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 263) f110 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 264) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 253), (4, 263), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (12, 256), (13, 259), (14, 262), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d72) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f111 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 266) f111 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 267) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 253), (4, 266), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (12, 256), (13, 259), (14, 262), (15, 265), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d74) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f112 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 269) f112 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 270) (ρ' := [(0, 71), (1, 212), (2, 245), (3, 253), (4, 269), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (12, 256), (13, 259), (14, 262), (15, 265), (22, 22), (39, 39), (50, 50), (51, 51)]) f112 (by decide) rfl rfl rfl (by decide)

theorem rest_l109c00_4 [Bindings] (code : CodeMap) :
    Rest (n := 206) code lifted (codeRange 0x109c00 bytes_l109c00) [(0, 71), (1, 204), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (15, 171), (19, 196), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x109d0c bytes_l109c00_4 b_l109c00_4 := by
  have f80 : InstrSpec 0x109d0c [0x4D, 0x31, 0xD3] (fun s => s.RIP = 0x109d0c) (xorR64R64Effect 0x109d0c 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109d0c 11 10).toInstrSpec (xor_r64_r64_effect_step 0x109d0c 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x109d0f [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x109d0f) (negR64Effect 0x109d0f 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x109d0f 1).toInstrSpec (neg_r64_effect_step 0x109d0f 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x109d12 [0x4C, 0x21, 0xD9] (fun s => s.RIP = 0x109d12) (andR64R64Effect 0x109d12 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109d12 1 11).toInstrSpec (and_r64_r64_effect_step 0x109d12 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x109d15 [0x4C, 0x31, 0xD1] (fun s => s.RIP = 0x109d15) (xorR64R64Effect 0x109d15 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109d15 1 10).toInstrSpec (xor_r64_r64_effect_step 0x109d15 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x109d18 [0x88, 0x54, 0x24, 0x07] (StorePre 0x109d18 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d18 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d18 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d18 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109d18 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f85 : InstrSpec 0x109d1c [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x109d1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d1c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109d1c 6 10 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x109d1c 6 10 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x109d1c 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f86 : InstrSpec 0x109d22 [0x4C, 0x31, 0xCE] (fun s => s.RIP = 0x109d22) (xorR64R64Effect 0x109d22 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109d22 6 9).toInstrSpec (xor_r64_r64_effect_step 0x109d22 0x4c 0xce (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x109d25 [0x49, 0xF7, 0xDA] (fun s => s.RIP = 0x109d25) (negR64Effect 0x109d25 10)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (negR64Effect_footprint 0x109d25 10).toInstrSpec (neg_r64_effect_step 0x109d25 0x49 0xda (by decide) (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x109d28 [0x49, 0x21, 0xF2] (fun s => s.RIP = 0x109d28) (andR64R64Effect 0x109d28 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109d28 10 6).toInstrSpec (and_r64_r64_effect_step 0x109d28 0x49 0xf2 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x109d2b [0x4D, 0x31, 0xCA] (fun s => s.RIP = 0x109d2b) (xorR64R64Effect 0x109d2b 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109d2b 10 9).toInstrSpec (xor_r64_r64_effect_step 0x109d2b 0x4d 0xca (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x109d2e [0x88, 0x54, 0x24, 0x07] (StorePre 0x109d2e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d2e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d2e 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d2e 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109d2e 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f91 : InstrSpec 0x109d32 [0x0F, 0xB6, 0x74, 0x24, 0x07] (LoadPre 0x109d32 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d32 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d32 5 6 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x109d32 5 6 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x109d32 6 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f92 : InstrSpec 0x109d37 [0x4C, 0x31, 0xC3] (fun s => s.RIP = 0x109d37) (xorR64R64Effect 0x109d37 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109d37 3 8).toInstrSpec (xor_r64_r64_effect_step 0x109d37 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x109d3a [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x109d3a) (negR64Effect 0x109d3a 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x109d3a 6).toInstrSpec (neg_r64_effect_step 0x109d3a 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x109d3d [0x48, 0x21, 0xDE] (fun s => s.RIP = 0x109d3d) (andR64R64Effect 0x109d3d 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109d3d 6 3).toInstrSpec (and_r64_r64_effect_step 0x109d3d 0x48 0xde (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x109d40 [0x4C, 0x31, 0xC6] (fun s => s.RIP = 0x109d40) (xorR64R64Effect 0x109d40 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109d40 6 8).toInstrSpec (xor_r64_r64_effect_step 0x109d40 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x109d43 [0x88, 0x54, 0x24, 0x07] (StorePre 0x109d43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d43 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d43 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109d43 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f97 : InstrSpec 0x109d47 [0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x109d47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d47 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d47 5 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x109d47 5 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x109d47 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f98 : InstrSpec 0x109d4c [0x49, 0x31, 0xC7] (fun s => s.RIP = 0x109d4c) (xorR64R64Effect 0x109d4c 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109d4c 15 0).toInstrSpec (xor_r64_r64_effect_step 0x109d4c 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x109d4f [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x109d4f) (negR64Effect 0x109d4f 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x109d4f 2).toInstrSpec (neg_r64_effect_step 0x109d4f 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f80 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 71), (1, 204), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d0f) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f81 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 71), (1, 208), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d12) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 71), (1, 210), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d15) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d18) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.exec (n := 214) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d1c) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f85 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 215), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d22) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f86 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 217), (7, 7), (8, 69), (9, 67), (10, 215), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d25) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f87 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 217), (7, 7), (8, 69), (9, 67), (10, 219), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d28) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f88 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 217), (7, 7), (8, 69), (9, 67), (10, 221), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d2b) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f89 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 217), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d2e) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.exec (n := 225) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 217), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d32) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f91 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 140), (4, 63), (5, 5), (6, 226), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d37) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f92 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 229) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 228), (4, 63), (5, 5), (6, 226), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d3a) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f93 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 228), (4, 63), (5, 5), (6, 230), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d3d) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f94 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 228), (4, 63), (5, 5), (6, 232), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d40) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f95 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d43) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.exec (n := 236) (ρ' := [(0, 71), (1, 212), (2, 200), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d47) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f97 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 71), (1, 212), (2, 237), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d4c) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f98 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 71), (1, 212), (2, 237), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d4f) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f99 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 71), (1, 212), (2, 241), (3, 228), (4, 63), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (13, 177), (15, 239), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d52) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109c00_5 code

theorem rest_l109c00_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x109c00 bytes_l109c00) [(0, 71), (1, 163), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 167), (14, 97), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]
      53 0x109cc6 bytes_l109c00_3 b_l109c00_3 := by
  have f60 : InstrSpec 0x109cc6 [0x49, 0xC1, 0xFF, 0x3F] (fun s => s.RIP = 0x109cc6) (sarR64Effect 0x109cc6 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (sarR64Effect_footprint 0x109cc6 4 15 63).toInstrSpec (sar_r64_imm8_effect_step 0x109cc6 0x49 0xff 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x109cca [0x4D, 0x01, 0xEF] (fun s => s.RIP = 0x109cca) (addR64R64Effect 0x109cca 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109cca 15 13).toInstrSpec (add_r64_r64_effect_step 0x109cca 0x4d 0xef (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x109ccd [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x109ccd) (notR64Effect 0x109ccd 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x109ccd 1).toInstrSpec (not_r64_effect_step 0x109ccd 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x109cd0 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x109cd0) (movR64R64Effect 0x109cd0 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109cd0 13 0).toInstrSpec (mov_r64_r64_effect_step 0x109cd0 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x109cd3 [0x49, 0x21, 0xCD] (fun s => s.RIP = 0x109cd3) (andR64R64Effect 0x109cd3 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109cd3 13 1).toInstrSpec (and_r64_r64_effect_step 0x109cd3 0x49 0xcd (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x109cd6 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x109cd6) (orR64R64Effect 0x109cd6 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109cd6 1 0).toInstrSpec (or_r64_r64_effect_step 0x109cd6 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x109cd9 [0x4C, 0x21, 0xF9] (fun s => s.RIP = 0x109cd9) (andR64R64Effect 0x109cd9 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109cd9 1 15).toInstrSpec (and_r64_r64_effect_step 0x109cd9 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x109cdc [0x4C, 0x09, 0xE9] (fun s => s.RIP = 0x109cdc) (orR64R64Effect 0x109cdc 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109cdc 1 13).toInstrSpec (or_r64_r64_effect_step 0x109cdc 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x109cdf [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x109cdf) (shrR64Effect 0x109cdf 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x109cdf 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x109cdf 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x109ce3 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x109ce3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ce3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ce3 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ce3 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109ce3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x109ce8 [0x4C, 0x89, 0xC9] (fun s => s.RIP = 0x109ce8) (movR64R64Effect 0x109ce8 1 9)
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109ce8 1 9).toInstrSpec (mov_r64_r64_effect_step 0x109ce8 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x109ceb [0x4C, 0x09, 0xD1] (fun s => s.RIP = 0x109ceb) (orR64R64Effect 0x109ceb 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109ceb 1 10).toInstrSpec (or_r64_r64_effect_step 0x109ceb 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x109cee [0x4C, 0x09, 0xC1] (fun s => s.RIP = 0x109cee) (orR64R64Effect 0x109cee 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109cee 1 8).toInstrSpec (or_r64_r64_effect_step 0x109cee 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x109cf1 [0x80, 0xE2, 0x01] (fun s => s.RIP = 0x109cf1) (andR8Imm8Effect 0x109cf1 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x109cf1 3 2 0x1).toInstrSpec (and_r8_imm8_effect_step 0x109cf1 0xe2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x109cf4 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x109cf4) (orR64R64Effect 0x109cf4 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109cf4 1 0).toInstrSpec (or_r64_r64_effect_step 0x109cf4 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x109cf7 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x109cf7) (movzxR32R8Effect 0x109cf7 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x109cf7 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x109cf7 0xd2 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x109cfa [0x41, 0x0F, 0x44, 0xD6] (fun s => s.RIP = 0x109cfa) (atFlags (condHolds 4) (cmovR32R32Effect 0x109cfa 4 2 14))
      [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR32R32Effect_footprint 0x109cfa 4 2 14 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x109cfa 4 0x41 (by decide) 0xd6 (by decide) c)) pre_rip
  have f77 : InstrSpec 0x109cfe [0x88, 0x54, 0x24, 0x07] (StorePre 0x109cfe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109cfe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cfe 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cfe 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109cfe 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x109d02 [0x4C, 0x8D, 0x74, 0x24, 0x07] (fun s => s.RIP = 0x109d02) (leaR64Effect 0x109d02 14 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x109d02 14 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x109d02 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x109d07 [0x0F, 0xB6, 0x4C, 0x24, 0x07] (LoadPre 0x109d07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d07 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d07 5 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109d07 5 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x109d07 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 71), (1, 163), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 167), (14, 97), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cca) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 71), (1, 163), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 167), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ccd) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 71), (1, 173), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 167), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cd0) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 71), (1, 173), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 175), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cd3) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 71), (1, 173), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cd6) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f65 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 71), (1, 179), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cd9) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 71), (1, 181), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cdc) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 71), (1, 183), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cdf) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 71), (1, 185), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ce3) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.exec (n := 187) (ρ' := [(0, 71), (1, 185), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ce8) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f70 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 71), (1, 188), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ceb) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f71 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 71), (1, 190), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cee) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f72 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 71), (1, 192), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cf1) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f73 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 71), (1, 192), (2, 194), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cf4) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f74 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 71), (2, 194), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (19, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cf7) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f75 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 71), (2, 198), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (19, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cfa) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 71), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (19, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cfe) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.exec (n := 202) (ρ' := [(0, 71), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (14, 97), (15, 171), (19, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d02) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 203) (RestInside.exec (n := 203) (ρ' := [(0, 71), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (15, 171), (19, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d07) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 71), (1, 204), (2, 200), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 177), (15, 171), (19, 196), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d0c) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109c00_4 code

theorem rest_l109c00_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x109c00 bytes_l109c00) [(0, 71), (1, 1), (2, 93), (3, 128), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]
      73 0x109c80 bytes_l109c00_2 b_l109c00_2 := by
  have f40 : InstrSpec 0x109c80 [0x48, 0x2B, 0x5C, 0x24, 0x08] (LoadPre 0x109c80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c80 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109c80 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109c80 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109c80 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x109c85 [0x4C, 0x8B, 0x79, 0x10] (LoadPre 0x109c85 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x109c85 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c85 15 (.base 1 (.d8 0x10)))
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x109c85 15 (.base 1 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109c85 0x4c (by decide) 7 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x109c89 [0x4D, 0x89, 0xFD] (fun s => s.RIP = 0x109c89) (movR64R64Effect 0x109c89 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109c89 13 15).toInstrSpec (mov_r64_r64_effect_step 0x109c89 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x109c8c [0x4D, 0x29, 0xC5] (fun s => s.RIP = 0x109c8c) (subR64R64Effect 0x109c8c 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x109c8c 13 8).toInstrSpec (sub_r64_r64_effect_step 0x109c8c 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x109c8f [0x48, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x109c8f) (sarR64Effect 0x109c8f 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (sarR64Effect_footprint 0x109c8f 4 3 63).toInstrSpec (sar_r64_imm8_effect_step 0x109c8f 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x109c93 [0x4C, 0x01, 0xEB] (fun s => s.RIP = 0x109c93) (addR64R64Effect 0x109c93 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109c93 3 13).toInstrSpec (add_r64_r64_effect_step 0x109c93 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x109c96 [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x109c96) (notR64Effect 0x109c96 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x109c96 15).toInstrSpec (not_r64_effect_step 0x109c96 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x109c99 [0x4D, 0x89, 0xC5] (fun s => s.RIP = 0x109c99) (movR64R64Effect 0x109c99 13 8)
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109c99 13 8).toInstrSpec (mov_r64_r64_effect_step 0x109c99 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x109c9c [0x4D, 0x21, 0xFD] (fun s => s.RIP = 0x109c9c) (andR64R64Effect 0x109c9c 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109c9c 13 15).toInstrSpec (and_r64_r64_effect_step 0x109c9c 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x109c9f [0x4D, 0x09, 0xC7] (fun s => s.RIP = 0x109c9f) (orR64R64Effect 0x109c9f 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109c9f 15 8).toInstrSpec (or_r64_r64_effect_step 0x109c9f 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x109ca2 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x109ca2) (andR64R64Effect 0x109ca2 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109ca2 15 3).toInstrSpec (and_r64_r64_effect_step 0x109ca2 0x49 0xdf (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x109ca5 [0x4D, 0x09, 0xEF] (fun s => s.RIP = 0x109ca5) (orR64R64Effect 0x109ca5 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109ca5 15 13).toInstrSpec (or_r64_r64_effect_step 0x109ca5 0x4d 0xef (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x109ca8 [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x109ca8) (shrR64Effect 0x109ca8 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x109ca8 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x109ca8 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x109cac [0x4C, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x109cac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109cac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109cac 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109cac 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109cac 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x109cb1 [0x4C, 0x8B, 0x6C, 0x24, 0x08] (LoadPre 0x109cb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109cb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109cb1 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x109cb1 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109cb1 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x109cb6 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x109cb6) (xorR32R32Effect 0x109cb6 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109cb6 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x109cb6 0x45 0xff (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x109cb9 [0x4D, 0x29, 0xEF] (fun s => s.RIP = 0x109cb9) (subR64R64Effect 0x109cb9 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x109cb9 15 13).toInstrSpec (sub_r64_r64_effect_step 0x109cb9 0x4d 0xef (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x109cbc [0x48, 0x8B, 0x49, 0x18] (LoadPre 0x109cbc (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x109cbc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109cbc 1 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109cbc 1 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109cbc 0x48 (by decide) 1 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x109cc0 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x109cc0) (movR64R64Effect 0x109cc0 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109cc0 13 1).toInstrSpec (mov_r64_r64_effect_step 0x109cc0 0x49 0xcd (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x109cc3 [0x49, 0x29, 0xC5] (fun s => s.RIP = 0x109cc3) (subR64R64Effect 0x109cc3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x109cc3 13 0).toInstrSpec (sub_r64_r64_effect_step 0x109cc3 0x49 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 130), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c85) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 130), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 132), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c89) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 130), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 134), (14, 97), (15, 132), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c8c) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 130), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 136), (14, 97), (15, 132), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c8f) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 138), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 136), (14, 97), (15, 132), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c93) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 136), (14, 97), (15, 132), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c96) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f46 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 136), (14, 97), (15, 142), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c99) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f47 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 144), (14, 97), (15, 142), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c9c) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f48 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 146), (14, 97), (15, 142), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c9f) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f49 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 146), (14, 97), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ca2) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 146), (14, 97), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ca5) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f51 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 146), (14, 97), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ca8) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 146), (14, 97), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cac) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 146), (14, 97), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cb1) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 157), (14, 97), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cb6) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 157), (14, 97), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cb9) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 157), (14, 97), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cbc) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 71), (1, 163), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 157), (14, 97), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cc0) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 71), (1, 163), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 165), (14, 97), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cc3) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 71), (1, 163), (2, 93), (3, 140), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 167), (14, 97), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cc6) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109c00_3 code

theorem rest_l109c00_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x109c00 bytes_l109c00) [(0, 71), (1, 1), (2, 2), (3, 91), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      93 0x109c3b bytes_l109c00_1 b_l109c00_1 := by
  have f20 : InstrSpec 0x109c3b [0x32, 0x56, 0x20] (LoadPre 0x109c3b (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x109c3b + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109c3b 3 2 (.base 6 (.d8 0x20)))
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x109c3b 3 2 (.base 6 (.d8 0x20))).toInstrSpec (xor_r8_m8_effect_step 0x109c3b 2 (by decide) (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x109c3e [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x109c3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109c3e 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109c3e 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109c3e 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x109c43 [0x4C, 0x8D, 0x64, 0x24, 0x08] (fun s => s.RIP = 0x109c43) (leaR64Effect 0x109c43 12 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x109c43 12 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x109c43 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x109c48 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x109c48) (xorR32R32Effect 0x109c48 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109c48 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x109c48 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x109c4b [0x31, 0xF6] (fun s => s.RIP = 0x109c4b) (xorR32R32Effect 0x109c4b 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109c4b 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x109c4b 0xf6 (by decide)) pre_rip
  have f25 : InstrSpec 0x109c4d [0x48, 0x2B, 0x74, 0x24, 0x08] (LoadPre 0x109c4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c4d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109c4d 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109c4d 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109c4d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x109c52 [0x48, 0x8B, 0x59, 0x08] (LoadPre 0x109c52 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x109c52 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c52 3 (.base 1 (.d8 0x8)))
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x109c52 3 (.base 1 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109c52 0x48 (by decide) 3 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x109c56 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x109c56) (movR64R64Effect 0x109c56 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x109c56 15 3).toInstrSpec (mov_r64_r64_effect_step 0x109c56 0x49 0xdf (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x109c59 [0x4D, 0x29, 0xCF] (fun s => s.RIP = 0x109c59) (subR64R64Effect 0x109c59 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x109c59 15 9).toInstrSpec (sub_r64_r64_effect_step 0x109c59 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x109c5c [0x48, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x109c5c) (sarR64Effect 0x109c5c 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR64Effect_footprint 0x109c5c 4 6 63).toInstrSpec (sar_r64_imm8_effect_step 0x109c5c 0x48 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x109c60 [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x109c60) (addR64R64Effect 0x109c60 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109c60 6 15).toInstrSpec (add_r64_r64_effect_step 0x109c60 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x109c63 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x109c63) (notR64Effect 0x109c63 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x109c63 3).toInstrSpec (not_r64_effect_step 0x109c63 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x109c66 [0x4D, 0x89, 0xCF] (fun s => s.RIP = 0x109c66) (movR64R64Effect 0x109c66 15 9)
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x109c66 15 9).toInstrSpec (mov_r64_r64_effect_step 0x109c66 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x109c69 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x109c69) (andR64R64Effect 0x109c69 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109c69 15 3).toInstrSpec (and_r64_r64_effect_step 0x109c69 0x49 0xdf (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x109c6c [0x4C, 0x09, 0xCB] (fun s => s.RIP = 0x109c6c) (orR64R64Effect 0x109c6c 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109c6c 3 9).toInstrSpec (or_r64_r64_effect_step 0x109c6c 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x109c6f [0x48, 0x21, 0xF3] (fun s => s.RIP = 0x109c6f) (andR64R64Effect 0x109c6f 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109c6f 3 6).toInstrSpec (and_r64_r64_effect_step 0x109c6f 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x109c72 [0x4C, 0x09, 0xFB] (fun s => s.RIP = 0x109c72) (orR64R64Effect 0x109c72 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109c72 3 15).toInstrSpec (or_r64_r64_effect_step 0x109c72 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x109c75 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x109c75) (shrR64Effect 0x109c75 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x109c75 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x109c75 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x109c79 [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x109c79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109c79 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109c79 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109c79 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x109c7e [0x31, 0xDB] (fun s => s.RIP = 0x109c7e) (xorR32R32Effect 0x109c7e 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109c7e 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x109c7e 0xdb (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 91), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c3e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 91), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c43) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 91), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c48) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 91), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c4b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 91), (4, 63), (5, 5), (6, 99), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c4d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 91), (4, 63), (5, 5), (6, 101), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c52) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 103), (4, 63), (5, 5), (6, 101), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c56) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 103), (4, 63), (5, 5), (6, 101), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c59) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 103), (4, 63), (5, 5), (6, 101), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c5c) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 103), (4, 63), (5, 5), (6, 109), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c60) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 103), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c63) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 113), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c66) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 113), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c69) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 113), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c6c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 119), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c6f) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 121), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c72) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f36 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 123), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c75) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f37 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 125), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c79) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 125), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c7e) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 71), (1, 1), (2, 93), (3, 128), (4, 63), (5, 5), (6, 111), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (13, 13), (14, 97), (15, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c80) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109c00_2 code

theorem rest_l109c00 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109c00 bytes_l109c00) (entryMap (live .l109c00))
      113 0x109c00 bytes_l109c00 b_l109c00 := by
  have f0 : InstrSpec 0x109c00 [0x41, 0x57] (PushPre 0x109c00 2) (pushR64Effect 0x109c00 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109c00 2 15).toInstrSpec (push_r64_rex_effect_step 0x109c00 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109c02 [0x41, 0x56] (PushPre 0x109c02 2) (pushR64Effect 0x109c02 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109c02 2 14).toInstrSpec (push_r64_rex_effect_step 0x109c02 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109c04 [0x41, 0x55] (PushPre 0x109c04 2) (pushR64Effect 0x109c04 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109c04 2 13).toInstrSpec (push_r64_rex_effect_step 0x109c04 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109c06 [0x41, 0x54] (PushPre 0x109c06 2) (pushR64Effect 0x109c06 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109c06 2 12).toInstrSpec (push_r64_rex_effect_step 0x109c06 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109c08 [0x53] (PushPre 0x109c08 1) (pushR64Effect 0x109c08 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109c08 1 3).toInstrSpec (push_r64_effect_step 0x109c08 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109c09 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x109c09) (subR64Imm8Effect 0x109c09 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x109c09 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x109c09 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109c0d [0x4C, 0x8B, 0x16] (LoadPre 0x109c0d (fun s => AddrMode.addr (.base 6 .none) s (0x109c0d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109c0d 10 (.base 6 .none))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x109c0d 10 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109c0d 0x4c (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x109c10 [0x4C, 0x8B, 0x4E, 0x08] (LoadPre 0x109c10 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109c10 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c10 9 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x109c10 9 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109c10 0x4c (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109c14 [0x4C, 0x8B, 0x46, 0x10] (LoadPre 0x109c14 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109c14 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c14 8 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x109c14 8 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109c14 0x4c (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x109c18 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x109c18 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109c18 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c18 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109c18 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109c18 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x109c1c [0x48, 0x8B, 0x19] (LoadPre 0x109c1c (fun s => AddrMode.addr (.base 1 .none) s (0x109c1c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109c1c 3 (.base 1 .none))
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x109c1c 3 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109c1c 0x48 (by decide) 3 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x109c1f [0x49, 0x89, 0xDB] (fun s => s.RIP = 0x109c1f) (movR64R64Effect 0x109c1f 11 3)
      [.gpr 3] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x109c1f 11 3).toInstrSpec (mov_r64_r64_effect_step 0x109c1f 0x49 0xdb (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x109c22 [0x4D, 0x29, 0xD3] (fun s => s.RIP = 0x109c22) (subR64R64Effect 0x109c22 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (subR64R64Effect_footprint 0x109c22 11 10).toInstrSpec (sub_r64_r64_effect_step 0x109c22 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x109c25 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x109c25) (notR64Effect 0x109c25 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x109c25 3).toInstrSpec (not_r64_effect_step 0x109c25 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x109c28 [0x4D, 0x89, 0xD6] (fun s => s.RIP = 0x109c28) (movR64R64Effect 0x109c28 14 10)
      [.gpr 10] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x109c28 14 10).toInstrSpec (mov_r64_r64_effect_step 0x109c28 0x4d 0xd6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x109c2b [0x49, 0x21, 0xDE] (fun s => s.RIP = 0x109c2b) (andR64R64Effect 0x109c2b 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109c2b 14 3).toInstrSpec (and_r64_r64_effect_step 0x109c2b 0x49 0xde (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x109c2e [0x4C, 0x09, 0xD3] (fun s => s.RIP = 0x109c2e) (orR64R64Effect 0x109c2e 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109c2e 3 10).toInstrSpec (or_r64_r64_effect_step 0x109c2e 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x109c31 [0x4C, 0x21, 0xDB] (fun s => s.RIP = 0x109c31) (andR64R64Effect 0x109c31 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109c31 3 11).toInstrSpec (and_r64_r64_effect_step 0x109c31 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x109c34 [0x4C, 0x09, 0xF3] (fun s => s.RIP = 0x109c34) (orR64R64Effect 0x109c34 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109c34 3 14).toInstrSpec (or_r64_r64_effect_step 0x109c34 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x109c37 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x109c37) (shrR64Effect 0x109c37 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x109c37 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x109c37 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c04) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c06) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c08) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c09) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c0d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (10, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c10) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 67), (10, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c14) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c18) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c1c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c1f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c22) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c25) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 79), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c28) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 79), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 81), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c2b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 79), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c2e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 85), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c31) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 87), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c34) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 89), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c37) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 91), (4, 63), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (10, 65), (11, 77), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c3b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109c00_1 code

theorem block_l109c00 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109c00 :=
  Rest.liftedBlock (rest_l109c00 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109c00 x hx)

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

theorem_by block_l109c00_eval :
    program.runBlock (dialect code) ⟨.l109c00, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
