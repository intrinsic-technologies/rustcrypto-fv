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

theorem rest_l110b80_4 [Bindings] (code : CodeMap) :
    Rest (n := 204) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x110c99 bytes_l110b80_4 b_l110b80_4 := by
  have f80 : InstrSpec 0x110c99 [0x49, 0xFF, 0xCA] (fun s => s.RIP = 0x110c99) (decR64Effect 0x110c99 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (decR64Effect_footprint 0x110c99 10).toInstrSpec (dec_r64_effect_step 0x110c99 0x49 0xca (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x110c9c [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x110c9c) (andR64R64Effect 0x110c9c 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c9c 10 8).toInstrSpec (and_r64_r64_effect_step 0x110c9c 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x110c9f [0x49, 0xFF, 0xCB] (fun s => s.RIP = 0x110c9f) (decR64Effect 0x110c9f 11)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (decR64Effect_footprint 0x110c9f 11).toInstrSpec (dec_r64_effect_step 0x110c9f 0x49 0xcb (by decide) (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x110ca2 [0x49, 0x21, 0xDB] (fun s => s.RIP = 0x110ca2) (andR64R64Effect 0x110ca2 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110ca2 11 3).toInstrSpec (and_r64_r64_effect_step 0x110ca2 0x49 0xdb (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x110ca5 [0x0F, 0xB6, 0x4C, 0x24, 0x07] (LoadPre 0x110ca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110ca5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x110ca5 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f85 : InstrSpec 0x110caa [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x110caa) (decR64Effect 0x110caa 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x110caa 1).toInstrSpec (dec_r64_effect_step 0x110caa 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x110cad [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x110cad) (andR64R64Effect 0x110cad 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110cad 1 6).toInstrSpec (and_r64_r64_effect_step 0x110cad 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x110cb0 [0x48, 0x89, 0x17] (StorePre 0x110cb0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x110cb0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110cb0 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb0 2 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110cb0 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f88 : InstrSpec 0x110cb3 [0x4C, 0x89, 0x57, 0x08] (StorePre 0x110cb3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x110cb3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb3 10 (.base 7 (.d8 0x8)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb3 10 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110cb3 0x4c (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f89 : InstrSpec 0x110cb7 [0x4C, 0x89, 0x5F, 0x10] (StorePre 0x110cb7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x110cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb7 11 (.base 7 (.d8 0x10)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb7 11 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x110cb7 0x4c (by decide) 3 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x110cbb [0x48, 0x89, 0x4F, 0x18] (StorePre 0x110cbb 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x110cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cbb 1 (.base 7 (.d8 0x18)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cbb 1 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x110cbb 0x48 (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f91 : InstrSpec 0x110cbf [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x110cbf) (addR64Imm8Effect 0x110cbf 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x110cbf 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x110cbf 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x110cc3 [0x5B] (PopPre 0x110cc3) (popR64Effect 0x110cc3 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc3 1 3).toInstrSpec (pop_r64_effect_step 0x110cc3 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f93 : InstrSpec 0x110cc4 [0x41, 0x5C] (PopPre 0x110cc4) (popR64Effect 0x110cc4 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc4 2 12).toInstrSpec (pop_r64_rex_effect_step 0x110cc4 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f94 : InstrSpec 0x110cc6 [0x41, 0x5E] (PopPre 0x110cc6) (popR64Effect 0x110cc6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110cc6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f95 : InstrSpec 0x110cc8 [0x41, 0x5F] (PopPre 0x110cc8) (popR64Effect 0x110cc8 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc8 2 15).toInstrSpec (pop_r64_rex_effect_step 0x110cc8 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f96 : InstrSpec 0x110cca [0xC3] (RetPre 0x110cca) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x110cca).toInstrSpec (ret_effect_step 0x110cca) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f80 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 204), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c9c) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f81 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c9f) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f82 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 208), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ca2) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f83 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ca5) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 198), (1, 212), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110caa) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 198), (1, 214), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cad) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f86 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb0) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.exec (n := 218) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb3) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 219) (RestInside.exec (n := 219) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb7) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 220) (RestInside.exec (n := 220) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cbb) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 221) (RestInside.exec (n := 221) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cbf) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f91 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 222), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc3) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f92 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 225) f92 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 226) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 225), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc4) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f93 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 228) f93 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 229) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 228), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc6) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f94 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 231) f94 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 232) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 231), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc8) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f95 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 234) f95 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 235) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 234), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cca) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f96 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 237) f96 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 238) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 237), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) f96 (by decide) rfl rfl rfl (by decide)

theorem rest_l110b80_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 167), (22, 22), (39, 39), (50, 50), (51, 51)]
      37 0x110c48 bytes_l110b80_3 b_l110b80_3 := by
  have f60 : InstrSpec 0x110c48 [0x49, 0x21, 0xD7] (fun s => s.RIP = 0x110c48) (andR64R64Effect 0x110c48 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c48 15 2).toInstrSpec (and_r64_r64_effect_step 0x110c48 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x110c4b [0x4C, 0x09, 0xCA] (fun s => s.RIP = 0x110c4b) (orR64R64Effect 0x110c4b 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c4b 2 9).toInstrSpec (or_r64_r64_effect_step 0x110c4b 0x4c 0xca (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x110c4e [0x48, 0x21, 0xF2] (fun s => s.RIP = 0x110c4e) (andR64R64Effect 0x110c4e 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c4e 2 6).toInstrSpec (and_r64_r64_effect_step 0x110c4e 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x110c51 [0x4C, 0x09, 0xFA] (fun s => s.RIP = 0x110c51) (orR64R64Effect 0x110c51 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c51 2 15).toInstrSpec (or_r64_r64_effect_step 0x110c51 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x110c54 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x110c54) (shrR64Effect 0x110c54 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x110c54 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x110c54 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x110c58 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x110c58 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c58 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c58 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110c58 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110c58 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x110c5d [0x4C, 0x09, 0xD0] (fun s => s.RIP = 0x110c5d) (orR64R64Effect 0x110c5d 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c5d 0 10).toInstrSpec (or_r64_r64_effect_step 0x110c5d 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x110c60 [0x4C, 0x09, 0xD8] (fun s => s.RIP = 0x110c60) (orR64R64Effect 0x110c60 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c60 0 11).toInstrSpec (or_r64_r64_effect_step 0x110c60 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x110c63 [0x4C, 0x09, 0xC8] (fun s => s.RIP = 0x110c63) (orR64R64Effect 0x110c63 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c63 0 9).toInstrSpec (or_r64_r64_effect_step 0x110c63 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x110c66 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c66 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c66 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c66 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c66 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c66 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x110c6b [0x4C, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x110c6b) (leaR64Effect 0x110c6b 9 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x110c6b 9 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x110c6b 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x110c70 [0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x110c70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c70 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x110c70 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x110c75 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c75 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c75 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c75 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c75 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x110c7a [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x110c7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c7a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x110c7a 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x110c80 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c80 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c80 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c80 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c80 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x110c85 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x07] (LoadPre 0x110c85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c85 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x110c85 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x110c8b [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c8b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c8b + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c8b 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c8b 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c8b 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f77 : InstrSpec 0x110c90 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x110c90) (movR64R64Effect 0x110c90 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110c90 0 7).toInstrSpec (mov_r64_r64_effect_step 0x110c90 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x110c93 [0x48, 0xFF, 0xCA] (fun s => s.RIP = 0x110c93) (decR64Effect 0x110c93 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (decR64Effect_footprint 0x110c93 2).toInstrSpec (dec_r64_effect_step 0x110c93 0x48 0xca (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x110c96 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x110c96) (andR64R64Effect 0x110c96 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c96 2 1).toInstrSpec (and_r64_r64_effect_step 0x110c96 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c4b) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 65), (1, 75), (2, 171), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c4e) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 65), (1, 75), (2, 173), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c51) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 65), (1, 75), (2, 175), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c54) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 65), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c58) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.exec (n := 179) (ρ' := [(0, 65), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c5d) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 180), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c60) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 182), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c63) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f68 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c66) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c6b) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f70 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c70) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f71 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c75) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c7a) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f73 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c80) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.exec (n := 194) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c85) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f75 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c8b) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.exec (n := 197) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c90) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f77 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 198), (1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c93) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f78 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 198), (1, 75), (2, 200), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c96) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f79 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c99) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_4 code

theorem rest_l110b80_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]
      57 0x110c04 bytes_l110b80_2 b_l110b80_2 := by
  have f40 : InstrSpec 0x110c04 [0x4D, 0x89, 0xFC] (fun s => s.RIP = 0x110c04) (movR64R64Effect 0x110c04 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x110c04 12 15).toInstrSpec (mov_r64_r64_effect_step 0x110c04 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x110c07 [0x4D, 0x29, 0xDC] (fun s => s.RIP = 0x110c07) (subR64R64Effect 0x110c07 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110c07 12 11).toInstrSpec (sub_r64_r64_effect_step 0x110c07 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x110c0a [0x48, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x110c0a) (sarR64Effect 0x110c0a 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (sarR64Effect_footprint 0x110c0a 4 3 63).toInstrSpec (sar_r64_imm8_effect_step 0x110c0a 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x110c0e [0x4C, 0x01, 0xE3] (fun s => s.RIP = 0x110c0e) (addR64R64Effect 0x110c0e 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110c0e 3 12).toInstrSpec (add_r64_r64_effect_step 0x110c0e 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x110c11 [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x110c11) (notR64Effect 0x110c11 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x110c11 15).toInstrSpec (not_r64_effect_step 0x110c11 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x110c14 [0x4D, 0x89, 0xDC] (fun s => s.RIP = 0x110c14) (movR64R64Effect 0x110c14 12 11)
      [.gpr 11] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x110c14 12 11).toInstrSpec (mov_r64_r64_effect_step 0x110c14 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x110c17 [0x4D, 0x21, 0xFC] (fun s => s.RIP = 0x110c17) (andR64R64Effect 0x110c17 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c17 12 15).toInstrSpec (and_r64_r64_effect_step 0x110c17 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x110c1a [0x4D, 0x09, 0xDF] (fun s => s.RIP = 0x110c1a) (orR64R64Effect 0x110c1a 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c1a 15 11).toInstrSpec (or_r64_r64_effect_step 0x110c1a 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x110c1d [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x110c1d) (andR64R64Effect 0x110c1d 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c1d 15 3).toInstrSpec (and_r64_r64_effect_step 0x110c1d 0x49 0xdf (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x110c20 [0x4D, 0x09, 0xE7] (fun s => s.RIP = 0x110c20) (orR64R64Effect 0x110c20 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c20 15 12).toInstrSpec (or_r64_r64_effect_step 0x110c20 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x110c23 [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x110c23) (shrR64Effect 0x110c23 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x110c23 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x110c23 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x110c27 [0x4C, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x110c27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c27 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c27 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110c27 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110c27 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x110c2c [0x48, 0x2B, 0x74, 0x24, 0x08] (LoadPre 0x110c2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c2c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110c2c 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110c2c 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110c2c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x110c31 [0x48, 0x8B, 0x52, 0x18] (LoadPre 0x110c31 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x110c31 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c31 2 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x110c31 2 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110c31 0x48 (by decide) 2 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x110c35 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x110c35) (movR64R64Effect 0x110c35 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110c35 15 2).toInstrSpec (mov_r64_r64_effect_step 0x110c35 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x110c38 [0x4D, 0x29, 0xCF] (fun s => s.RIP = 0x110c38) (subR64R64Effect 0x110c38 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110c38 15 9).toInstrSpec (sub_r64_r64_effect_step 0x110c38 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x110c3b [0x48, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x110c3b) (sarR64Effect 0x110c3b 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR64Effect_footprint 0x110c3b 4 6 63).toInstrSpec (sar_r64_imm8_effect_step 0x110c3b 0x48 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x110c3f [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x110c3f) (addR64R64Effect 0x110c3f 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110c3f 6 15).toInstrSpec (add_r64_r64_effect_step 0x110c3f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x110c42 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x110c42) (notR64Effect 0x110c42 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x110c42 2).toInstrSpec (not_r64_effect_step 0x110c42 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x110c45 [0x4D, 0x89, 0xCF] (fun s => s.RIP = 0x110c45) (movR64R64Effect 0x110c45 15 9)
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110c45 15 9).toInstrSpec (mov_r64_r64_effect_step 0x110c45 0x4d 0xcf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 130), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c07) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c0a) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 134), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c0e) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c11) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c14) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 140), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c17) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f46 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c1a) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f47 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 144), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c1d) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f48 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c20) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f49 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c23) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c27) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.exec (n := 152) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c2c) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c31) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c35) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c38) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c3b) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 161), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c3f) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c42) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c45) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 167), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c48) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_3 code

theorem rest_l110b80_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      77 0x110bbe bytes_l110b80_1 b_l110b80_1 := by
  have f20 : InstrSpec 0x110bbe [0x4C, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x110bbe) (leaR64Effect 0x110bbe 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x110bbe 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x110bbe 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x110bc3 [0x31, 0xF6] (fun s => s.RIP = 0x110bc3) (xorR32R32Effect 0x110bc3 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bc3 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x110bc3 0xf6 (by decide)) pre_rip
  have f22 : InstrSpec 0x110bc5 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x110bc5) (xorR32R32Effect 0x110bc5 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bc5 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x110bc5 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x110bc8 [0x4C, 0x2B, 0x44, 0x24, 0x08] (LoadPre 0x110bc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bc8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bc8 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110bc8 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110bc8 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x110bcd [0x48, 0x8B, 0x5A, 0x08] (LoadPre 0x110bcd (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x110bcd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110bcd 3 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x110bcd 3 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110bcd 0x48 (by decide) 3 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x110bd1 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x110bd1) (movR64R64Effect 0x110bd1 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110bd1 15 3).toInstrSpec (mov_r64_r64_effect_step 0x110bd1 0x49 0xdf (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x110bd4 [0x49, 0x29, 0xC7] (fun s => s.RIP = 0x110bd4) (subR64R64Effect 0x110bd4 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110bd4 15 0).toInstrSpec (sub_r64_r64_effect_step 0x110bd4 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x110bd7 [0x49, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x110bd7) (sarR64Effect 0x110bd7 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (sarR64Effect_footprint 0x110bd7 4 8 63).toInstrSpec (sar_r64_imm8_effect_step 0x110bd7 0x49 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x110bdb [0x4D, 0x01, 0xF8] (fun s => s.RIP = 0x110bdb) (addR64R64Effect 0x110bdb 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110bdb 8 15).toInstrSpec (add_r64_r64_effect_step 0x110bdb 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x110bde [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x110bde) (notR64Effect 0x110bde 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x110bde 3).toInstrSpec (not_r64_effect_step 0x110bde 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x110be1 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x110be1) (movR64R64Effect 0x110be1 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110be1 15 0).toInstrSpec (mov_r64_r64_effect_step 0x110be1 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x110be4 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x110be4) (andR64R64Effect 0x110be4 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110be4 15 3).toInstrSpec (and_r64_r64_effect_step 0x110be4 0x49 0xdf (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x110be7 [0x48, 0x09, 0xC3] (fun s => s.RIP = 0x110be7) (orR64R64Effect 0x110be7 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110be7 3 0).toInstrSpec (or_r64_r64_effect_step 0x110be7 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x110bea [0x4C, 0x21, 0xC3] (fun s => s.RIP = 0x110bea) (andR64R64Effect 0x110bea 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110bea 3 8).toInstrSpec (and_r64_r64_effect_step 0x110bea 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x110bed [0x4C, 0x09, 0xFB] (fun s => s.RIP = 0x110bed) (orR64R64Effect 0x110bed 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bed 3 15).toInstrSpec (or_r64_r64_effect_step 0x110bed 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x110bf0 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x110bf0) (shrR64Effect 0x110bf0 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x110bf0 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x110bf0 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x110bf4 [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x110bf4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bf4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bf4 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110bf4 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110bf4 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x110bf9 [0x31, 0xDB] (fun s => s.RIP = 0x110bf9) (xorR32R32Effect 0x110bf9 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bf9 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x110bf9 0xdb (by decide)) pre_rip
  have f38 : InstrSpec 0x110bfb [0x48, 0x2B, 0x5C, 0x24, 0x08] (LoadPre 0x110bfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bfb + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bfb 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110bfb 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110bfb 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x110c00 [0x4C, 0x8B, 0x7A, 0x10] (LoadPre 0x110c00 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x110c00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c00 15 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x110c00 15 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110c00 0x4c (by decide) 7 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc3) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 95), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc8) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bcd) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd1) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd4) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd7) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 105), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bdb) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bde) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be4) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be7) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 115), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bea) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 117), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bed) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 119), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf0) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 121), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf4) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 121), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf9) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 124), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bfb) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c00) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c04) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_2 code

theorem rest_l110b80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110b80 bytes_l110b80) (entryMap (live .l110b80))
      97 0x110b80 bytes_l110b80 b_l110b80 := by
  have f0 : InstrSpec 0x110b80 [0x41, 0x57] (PushPre 0x110b80 2) (pushR64Effect 0x110b80 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b80 2 15).toInstrSpec (push_r64_rex_effect_step 0x110b80 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x110b82 [0x41, 0x56] (PushPre 0x110b82 2) (pushR64Effect 0x110b82 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b82 2 14).toInstrSpec (push_r64_rex_effect_step 0x110b82 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x110b84 [0x41, 0x54] (PushPre 0x110b84 2) (pushR64Effect 0x110b84 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b84 2 12).toInstrSpec (push_r64_rex_effect_step 0x110b84 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x110b86 [0x53] (PushPre 0x110b86 1) (pushR64Effect 0x110b86 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b86 1 3).toInstrSpec (push_r64_effect_step 0x110b86 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x110b87 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x110b87) (subR64Imm8Effect 0x110b87 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x110b87 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x110b87 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x110b8b [0x4C, 0x8B, 0x16] (LoadPre 0x110b8b (fun s => AddrMode.addr (.base 6 .none) s (0x110b8b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b8b 10 (.base 6 .none))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x110b8b 10 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110b8b 0x4c (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x110b8e [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x110b8e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x110b8e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b8e 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110b8e 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110b8e 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x110b92 [0x4C, 0x8B, 0x5E, 0x10] (LoadPre 0x110b92 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x110b92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b92 11 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x110b92 11 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110b92 0x4c (by decide) 3 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x110b96 [0x4C, 0x8B, 0x4E, 0x18] (LoadPre 0x110b96 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x110b96 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b96 9 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x110b96 9 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110b96 0x4c (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x110b9a [0x48, 0x8B, 0x32] (LoadPre 0x110b9a (fun s => AddrMode.addr (.base 2 .none) s (0x110b9a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b9a 6 (.base 2 .none))
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x110b9a 6 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110b9a 0x48 (by decide) 6 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x110b9d [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x110b9d) (movR64R64Effect 0x110b9d 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x110b9d 1 6).toInstrSpec (mov_r64_r64_effect_step 0x110b9d 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x110ba0 [0x4C, 0x29, 0xD1] (fun s => s.RIP = 0x110ba0) (subR64R64Effect 0x110ba0 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110ba0 1 10).toInstrSpec (sub_r64_r64_effect_step 0x110ba0 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x110ba3 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x110ba3) (notR64Effect 0x110ba3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x110ba3 6).toInstrSpec (not_r64_effect_step 0x110ba3 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x110ba6 [0x4D, 0x89, 0xD0] (fun s => s.RIP = 0x110ba6) (movR64R64Effect 0x110ba6 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x110ba6 8 10).toInstrSpec (mov_r64_r64_effect_step 0x110ba6 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x110ba9 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x110ba9) (andR64R64Effect 0x110ba9 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110ba9 8 6).toInstrSpec (and_r64_r64_effect_step 0x110ba9 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x110bac [0x4C, 0x09, 0xD6] (fun s => s.RIP = 0x110bac) (orR64R64Effect 0x110bac 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bac 6 10).toInstrSpec (or_r64_r64_effect_step 0x110bac 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x110baf [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x110baf) (andR64R64Effect 0x110baf 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110baf 6 1).toInstrSpec (and_r64_r64_effect_step 0x110baf 0x48 0xce (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x110bb2 [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x110bb2) (orR64R64Effect 0x110bb2 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bb2 6 8).toInstrSpec (or_r64_r64_effect_step 0x110bb2 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x110bb5 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x110bb5) (shrR64Effect 0x110bb5 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x110bb5 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x110bb5 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x110bb9 [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x110bb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bb9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bb9 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110bb9 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110bb9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b82) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b84) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b86) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b87) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b8b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b8e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b92) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b96) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b9a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b9d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 73), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (8, 79), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bac) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 83), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110baf) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 85), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 87), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bbe) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l110b80_1 code

theorem block_l110b80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110b80 :=
  Rest.liftedBlock (rest_l110b80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110b80 x hx)

theorem rest_l1148d0_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x1148d0 bytes_l1148d0) [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x114917 bytes_l1148d0_1 b_l1148d0_1 := by
  have f20 : InstrSpec 0x114917 [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x114917) (bswapR64Effect 0x114917 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x114917 3 6).toInstrSpec (bswap_r64_effect_step 0x114917 0x48 (by decide) 0xce (by decide)) pre_rip
  have f21 : InstrSpec 0x11491a [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11491a) (movR64R64Effect 0x11491a 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11491a 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11491a 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11491d [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x11491d) (bswapR64Effect 0x11491d 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x11491d 3 1).toInstrSpec (bswap_r64_effect_step 0x11491d 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f23 : InstrSpec 0x114920 [0x48, 0x89, 0x17] (StorePre 0x114920 3 (fun s => AddrMode.addr (.base 7 .none) s (0x114920 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x114920 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114920 2 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x114920 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x114923 [0x4C, 0x89, 0x57, 0x08] (StorePre 0x114923 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x114923 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114923 10 (.base 7 (.d8 0x8)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114923 10 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x114923 0x4c (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x114927 [0x48, 0x89, 0x77, 0x10] (StorePre 0x114927 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x114927 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114927 6 (.base 7 (.d8 0x10)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114927 6 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x114927 0x48 (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x11492b [0x48, 0x89, 0x4F, 0x18] (StorePre 0x11492b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x11492b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11492b 1 (.base 7 (.d8 0x18)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x11492b 1 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11492b 0x48 (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x11492f [0xC3] (RetPre 0x11492f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11492f).toInstrSpec (ret_effect_step 0x11492f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11491a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11491d) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114920) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114923) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114927) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11492b) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11492f) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 104) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 105) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 104), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f27 (by decide) rfl rfl rfl (by decide)

theorem rest_l1148d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1148d0 bytes_l1148d0) (entryMap (live .l1148d0))
      28 0x1148d0 bytes_l1148d0 b_l1148d0 := by
  have f0 : InstrSpec 0x1148d0 [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x1148d0 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1148d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d0 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1148d0 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1148d0 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1148d4 [0x4C, 0x8B, 0x46, 0x10] (LoadPre 0x1148d4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1148d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d4 8 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1148d4 8 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1148d4 0x4c (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1148d8 [0x4C, 0x8B, 0x4E, 0x18] (LoadPre 0x1148d8 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1148d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d8 9 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1148d8 9 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1148d8 0x4c (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1148dc [0x48, 0x8B, 0x56, 0x20] (LoadPre 0x1148dc (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1148dc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148dc 2 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1148dc 2 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1148dc 0x48 (by decide) 2 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1148e0 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1148e0) (movR64R64Effect 0x1148e0 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1148e0 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1148e0 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1148e3 [0x48, 0xC1, 0xE1, 0x34] (fun s => s.RIP = 0x1148e3) (shlR64Effect 0x1148e3 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148e3 4 1 52).toInstrSpec (shl_r64_imm8_effect_step 0x1148e3 0x48 0xe1 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1148e7 [0x48, 0x0B, 0x0E] (LoadPre 0x1148e7 (fun s => AddrMode.addr (.base 6 .none) s (0x1148e7 + BitVec.ofNat 64 3)) 8) (orR64M64Effect 0x1148e7 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64M64Effect_footprint 0x1148e7 1 (.base 6 .none)).toInstrSpec (or_r64_m64_effect_step 0x1148e7 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1148ea [0x48, 0xC1, 0xE8, 0x0C] (fun s => s.RIP = 0x1148ea) (shrR64Effect 0x1148ea 4 0 12)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1148ea 4 0 12).toInstrSpec (shr_r64_imm8_effect_step 0x1148ea 0x48 0xe8 0xc (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1148ee [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x1148ee) (movR64R64Effect 0x1148ee 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1148ee 6 8).toInstrSpec (mov_r64_r64_effect_step 0x1148ee 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1148f1 [0x48, 0xC1, 0xE6, 0x28] (fun s => s.RIP = 0x1148f1) (shlR64Effect 0x1148f1 4 6 40)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148f1 4 6 40).toInstrSpec (shl_r64_imm8_effect_step 0x1148f1 0x48 0xe6 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1148f5 [0x48, 0x09, 0xC6] (fun s => s.RIP = 0x1148f5) (orR64R64Effect 0x1148f5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1148f5 6 0).toInstrSpec (or_r64_r64_effect_step 0x1148f5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1148f8 [0x49, 0xC1, 0xE8, 0x18] (fun s => s.RIP = 0x1148f8) (shrR64Effect 0x1148f8 4 8 24)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1148f8 4 8 24).toInstrSpec (shr_r64_imm8_effect_step 0x1148f8 0x49 0xe8 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1148fc [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x1148fc) (movR64R64Effect 0x1148fc 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1148fc 10 9).toInstrSpec (mov_r64_r64_effect_step 0x1148fc 0x4d 0xca (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1148ff [0x49, 0xC1, 0xE2, 0x1C] (fun s => s.RIP = 0x1148ff) (shlR64Effect 0x1148ff 4 10 28)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148ff 4 10 28).toInstrSpec (shl_r64_imm8_effect_step 0x1148ff 0x49 0xe2 0x1c (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x114903 [0x4D, 0x09, 0xC2] (fun s => s.RIP = 0x114903) (orR64R64Effect 0x114903 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x114903 10 8).toInstrSpec (or_r64_r64_effect_step 0x114903 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x114906 [0x49, 0xC1, 0xE9, 0x24] (fun s => s.RIP = 0x114906) (shrR64Effect 0x114906 4 9 36)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x114906 4 9 36).toInstrSpec (shr_r64_imm8_effect_step 0x114906 0x49 0xe9 0x24 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11490a [0x48, 0xC1, 0xE2, 0x10] (fun s => s.RIP = 0x11490a) (shlR64Effect 0x11490a 4 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64Effect_footprint 0x11490a 4 2 16).toInstrSpec (shl_r64_imm8_effect_step 0x11490a 0x48 0xe2 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11490e [0x4C, 0x09, 0xCA] (fun s => s.RIP = 0x11490e) (orR64R64Effect 0x11490e 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11490e 2 9).toInstrSpec (or_r64_r64_effect_step 0x11490e 0x4c 0xca (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x114911 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x114911) (bswapR64Effect 0x114911 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x114911 3 2).toInstrSpec (bswap_r64_effect_step 0x114911 0x48 (by decide) 0xca (by decide)) pre_rip
  have f19 : InstrSpec 0x114914 [0x49, 0x0F, 0xCA] (fun s => s.RIP = 0x114914) (bswapR64Effect 0x114914 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR64Effect_footprint 0x114914 3 10).toInstrSpec (bswap_r64_effect_step 0x114914 0x49 (by decide) 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148dc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 63), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ea) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ee) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148fc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ff) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 79), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114903) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114906) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11490a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 67), (1, 65), (2, 85), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11490e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 67), (1, 65), (2, 87), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114911) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114914) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114917) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1148d0_1 code

theorem block_l1148d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1148d0 :=
  Rest.liftedBlock (rest_l1148d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1148d0 x hx)

theorem rest_l11c3c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c3c0 bytes_l11c3c0) (entryMap (live .l11c3c0))
      14 0x11c3c0 bytes_l11c3c0 b_l11c3c0 := by
  have f0 : InstrSpec 0x11c3c0 [0x48, 0x8B, 0x4E, 0x18] (LoadPre 0x11c3c0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11c3c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3c0 1 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c3c0 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11c3c0 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c3c4 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x11c3c4) (bswapR64Effect 0x11c3c4 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x11c3c4 3 1).toInstrSpec (bswap_r64_effect_step 0x11c3c4 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x11c3c7 [0x48, 0x8B, 0x56, 0x10] (LoadPre 0x11c3c7 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11c3c7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3c7 2 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11c3c7 2 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11c3c7 0x48 (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11c3cb [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x11c3cb) (bswapR64Effect 0x11c3cb 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x11c3cb 3 2).toInstrSpec (bswap_r64_effect_step 0x11c3cb 0x48 (by decide) 0xca (by decide)) pre_rip
  have f4 : InstrSpec 0x11c3ce [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11c3ce) (movR64R64Effect 0x11c3ce 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c3ce 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11c3ce 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c3d1 [0x48, 0x8B, 0x7E, 0x08] (LoadPre 0x11c3d1 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11c3d1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3d1 7 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11c3d1 7 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11c3d1 0x48 (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11c3d5 [0x48, 0x0F, 0xCF] (fun s => s.RIP = 0x11c3d5) (bswapR64Effect 0x11c3d5 3 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR64Effect_footprint 0x11c3d5 3 7).toInstrSpec (bswap_r64_effect_step 0x11c3d5 0x48 (by decide) 0xcf (by decide)) pre_rip
  have f7 : InstrSpec 0x11c3d8 [0x48, 0x8B, 0x36] (LoadPre 0x11c3d8 (fun s => AddrMode.addr (.base 6 .none) s (0x11c3d8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c3d8 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11c3d8 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c3d8 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11c3db [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x11c3db) (bswapR64Effect 0x11c3db 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x11c3db 3 6).toInstrSpec (bswap_r64_effect_step 0x11c3db 0x48 (by decide) 0xce (by decide)) pre_rip
  have f9 : InstrSpec 0x11c3de [0x48, 0x89, 0x08] (StorePre 0x11c3de 3 (fun s => AddrMode.addr (.base 0 .none) s (0x11c3de + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11c3de 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c3de 1 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11c3de 0x48 (by decide) 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11c3e1 [0x48, 0x89, 0x50, 0x08] (StorePre 0x11c3e1 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x11c3e1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e1 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c3e1 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11c3e1 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11c3e5 [0x48, 0x89, 0x78, 0x10] (StorePre 0x11c3e5 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x11c3e5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e5 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c3e5 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11c3e5 0x48 (by decide) 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x11c3e9 [0x48, 0x89, 0x70, 0x18] (StorePre 0x11c3e9 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x11c3e9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e9 6 (.base 0 (.d8 0x18)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c3e9 6 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11c3e9 0x48 (by decide) 6 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x11c3ed [0xC3] (RetPre 0x11c3ed) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11c3ed).toInstrSpec (ret_effect_step 0x11c3ed) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3c7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3cb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3ce) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3d1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3d5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3d8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3db) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3de) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3e1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3e5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3e9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3ed) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 61), (1, 55), (2, 59), (3, 3), (4, 76), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f13 (by decide) rfl rfl rfl (by decide)

theorem block_l11c3c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c3c0 :=
  Rest.liftedBlock (rest_l11c3c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c3c0 x hx)

theorem rest_l11c3f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c3f0 bytes_l11c3f0) (entryMap (live .l11c3f0))
      1 0x11c3f0 bytes_l11c3f0 b_l11c3f0 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x11c3f0 0xb (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c3f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c3f0 :=
  Rest.liftedBlock (rest_l11c3f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c3f0 x hx)

theorem rest_l11c400_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x11c400 bytes_l11c400) [(1, 126), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x11c494 bytes_l11c400_2 b_l11c400_2 := by
  have f40 : InstrSpec 0x11c494 [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x11c494 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c494 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c494 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c494 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11c494 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x11c499 [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x11c499) (decR64Effect 0x11c499 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x11c499 1).toInstrSpec (dec_r64_effect_step 0x11c499 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x11c49c [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x11c49c) (shrR64Effect 0x11c49c 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c49c 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x11c49c 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x11c4a0 [0x4C, 0x01, 0xE9] (fun s => s.RIP = 0x11c4a0) (addR64R64Effect 0x11c4a0 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c4a0 1 13).toInstrSpec (add_r64_r64_effect_step 0x11c4a0 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x11c4a3 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x11c4a3) (movR64R64Effect 0x11c4a3 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11c4a3 2 13).toInstrSpec (mov_r64_r64_effect_step 0x11c4a3 0x4c 0xea (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x11c4a6 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x11c4a6) (notR64Effect 0x11c4a6 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x11c4a6 2).toInstrSpec (not_r64_effect_step 0x11c4a6 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x11c4a9 [0x48, 0x09, 0xCA] (fun s => s.RIP = 0x11c4a9) (orR64R64Effect 0x11c4a9 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11c4a9 2 1).toInstrSpec (or_r64_r64_effect_step 0x11c4a9 0x48 0xca (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x11c4ac [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x11c4ac) (shrR64Effect 0x11c4ac 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c4ac 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x11c4ac 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x11c4b0 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x11c4b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c4b0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c4b0 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c4b0 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11c4b0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x11c4b5 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x11c4b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c4b5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11c4b5 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11c4b5 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x11c4b5 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f50 : InstrSpec 0x11c4ba [0x24, 0x01] (fun s => s.RIP = 0x11c4ba) (andAlImm8Effect 0x11c4ba 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x11c4ba 0x1).toInstrSpec (and_al_imm8_effect_step 0x11c4ba 0x1) pre_rip
  have f51 : InstrSpec 0x11c4bc [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x11c4bc) (movzxR32R8Effect 0x11c4bc 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x11c4bc 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c4bc 0xf8 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x11c4bf [0xE8, 0x8C, 0xB8, 0x00, 0x00] (PushPre 0x11c4bf 5) (callEffect (fun _ => 0x127d50) 0x11c4c4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c4bf 0x127d50 0x11c4c4).toInstrSpec (call_rel32_effect_step 0x11c4bf 0xb88c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(1, 129), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c499) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(1, 131), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c49c) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(1, 133), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4a0) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(1, 135), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4a3) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(1, 135), (2, 137), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4a6) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f45 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(1, 135), (2, 139), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4a9) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f46 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(1, 135), (2, 141), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4ac) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f47 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(1, 135), (2, 143), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4b0) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(1, 135), (2, 143), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4b5) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 146), (1, 135), (2, 143), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4ba) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 148), (1, 135), (2, 143), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4bc) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f51 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 148), (1, 135), (2, 143), (3, 65), (4, 63), (5, 5), (6, 101), (7, 150), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4bf) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f52 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 148), (1, 135), (2, 143), (3, 65), (4, 152), (5, 5), (6, 101), (7, 150), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f52 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 154) (by decide) (by decide) rfl rfl

theorem rest_l11c400_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x11c400 bytes_l11c400) [(1, 89), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x11c445 bytes_l11c400_1 b_l11c400_1 := by
  have f20 : InstrSpec 0x11c445 [0x31, 0xD2] (fun s => s.RIP = 0x11c445) (xorR32R32Effect 0x11c445 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c445 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x11c445 0xd2 (by decide)) pre_rip
  have f21 : InstrSpec 0x11c447 [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x11c447 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c447 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c447 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11c447 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11c447 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x11c44c [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x11c44c) (sarR64Effect 0x11c44c 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x11c44c 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x11c44c 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11c450 [0x48, 0xBE, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x11c450) (movR64Imm64Effect 0x11c450 6 0x4551231950b75fc5)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x11c450 6 0x4551231950b75fc5).toInstrSpec (mov_r64_imm64_effect_step 0x11c450 0x48 0xbe (by decide) (by decide) 0x4551231950b75fc5) pre_rip
  have f24 : InstrSpec 0x11c45a [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x11c45a) (addR64R64Effect 0x11c45a 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c45a 6 15).toInstrSpec (add_r64_r64_effect_step 0x11c45a 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x11c45d [0x48, 0x01, 0xD6] (fun s => s.RIP = 0x11c45d) (addR64R64Effect 0x11c45d 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c45d 6 2).toInstrSpec (add_r64_r64_effect_step 0x11c45d 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x11c460 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x11c460) (movR64R64Effect 0x11c460 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11c460 2 15).toInstrSpec (mov_r64_r64_effect_step 0x11c460 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x11c463 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x11c463) (notR64Effect 0x11c463 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x11c463 2).toInstrSpec (not_r64_effect_step 0x11c463 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x11c466 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x11c466) (orR64R64Effect 0x11c466 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11c466 2 6).toInstrSpec (or_r64_r64_effect_step 0x11c466 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x11c469 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x11c469) (shrR64Effect 0x11c469 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c469 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x11c469 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x11c46d [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x11c46d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c46d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c46d 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c46d 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11c46d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x11c472 [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x11c472 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c472 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c472 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11c472 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11c472 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x11c477 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x11c477) (sarR64Effect 0x11c477 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x11c477 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x11c477 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x11c47b [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x11c47b) (movR64R64Effect 0x11c47b 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11c47b 2 12).toInstrSpec (mov_r64_r64_effect_step 0x11c47b 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x11c47e [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x11c47e) (notR64Effect 0x11c47e 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x11c47e 2).toInstrSpec (not_r64_effect_step 0x11c47e 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x11c481 [0x4C, 0x01, 0xE1] (fun s => s.RIP = 0x11c481) (addR64R64Effect 0x11c481 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c481 1 12).toInstrSpec (add_r64_r64_effect_step 0x11c481 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x11c484 [0x48, 0x83, 0xC1, 0x02] (fun s => s.RIP = 0x11c484) (addR64Imm8Effect 0x11c484 1 0x2)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11c484 1 0x2).toInstrSpec (add_r64_imm8_effect_step 0x11c484 0x48 0xc1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x11c488 [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x11c488) (orR64R64Effect 0x11c488 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11c488 1 2).toInstrSpec (or_r64_r64_effect_step 0x11c488 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x11c48b [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x11c48b) (shrR64Effect 0x11c48b 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c48b 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x11c48b 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x11c48f [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x11c48f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c48f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c48f 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c48f 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11c48f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 89), (2, 91), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c447) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 89), (2, 93), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c44c) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 89), (2, 95), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c450) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 89), (2, 95), (3, 65), (4, 63), (5, 5), (6, 97), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c45a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 89), (2, 95), (3, 65), (4, 63), (5, 5), (6, 99), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c45d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(1, 89), (2, 95), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c460) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(1, 89), (2, 103), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c463) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(1, 89), (2, 105), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c466) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(1, 89), (2, 107), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c469) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(1, 89), (2, 109), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c46d) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(1, 89), (2, 109), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c472) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(1, 112), (2, 109), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c477) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(1, 114), (2, 109), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c47b) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(1, 114), (2, 116), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c47e) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(1, 114), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c481) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(1, 120), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c484) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(1, 122), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c488) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(1, 124), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c48b) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(1, 126), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c48f) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.exec (n := 128) (ρ' := [(1, 126), (2, 118), (3, 65), (4, 63), (5, 5), (6, 101), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c494) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11c400_2 code

theorem rest_l11c400 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c400 bytes_l11c400) (entryMap (live .l11c400))
      53 0x11c400 bytes_l11c400 b_l11c400 := by
  have f0 : InstrSpec 0x11c400 [0x41, 0x57] (PushPre 0x11c400 2) (pushR64Effect 0x11c400 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c400 2 15).toInstrSpec (push_r64_rex_effect_step 0x11c400 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x11c402 [0x41, 0x56] (PushPre 0x11c402 2) (pushR64Effect 0x11c402 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c402 2 14).toInstrSpec (push_r64_rex_effect_step 0x11c402 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x11c404 [0x41, 0x55] (PushPre 0x11c404 2) (pushR64Effect 0x11c404 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c404 2 13).toInstrSpec (push_r64_rex_effect_step 0x11c404 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x11c406 [0x41, 0x54] (PushPre 0x11c406 2) (pushR64Effect 0x11c406 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c406 2 12).toInstrSpec (push_r64_rex_effect_step 0x11c406 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11c408 [0x53] (PushPre 0x11c408 1) (pushR64Effect 0x11c408 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c408 1 3).toInstrSpec (push_r64_effect_step 0x11c408 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x11c409 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x11c409) (subR64Imm8Effect 0x11c409 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x11c409 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x11c409 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c40d [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x11c40d) (movR64R64Effect 0x11c40d 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11c40d 3 7).toInstrSpec (mov_r64_r64_effect_step 0x11c40d 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11c410 [0x4C, 0x8B, 0x36] (LoadPre 0x11c410 (fun s => AddrMode.addr (.base 6 .none) s (0x11c410 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c410 14 (.base 6 .none))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x11c410 14 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c410 0x4c (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11c413 [0x4C, 0x8B, 0x7E, 0x08] (LoadPre 0x11c413 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11c413 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c413 15 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x11c413 15 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11c413 0x4c (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11c417 [0x4C, 0x8B, 0x66, 0x10] (LoadPre 0x11c417 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11c417 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c417 12 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x11c417 12 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11c417 0x4c (by decide) 4 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11c41b [0x4C, 0x8B, 0x6E, 0x18] (LoadPre 0x11c41b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11c41b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c41b 13 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x11c41b 13 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11c41b 0x4c (by decide) 5 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11c41f [0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x11c41f) (movR64Imm64Effect 0x11c41f 0 0x402da1732fc9bebf)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x11c41f 0 0x402da1732fc9bebf).toInstrSpec (mov_r64_imm64_effect_step 0x11c41f 0x48 0xb8 (by decide) (by decide) 0x402da1732fc9bebf) pre_rip
  have f12 : InstrSpec 0x11c429 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x11c429) (addR64R64Effect 0x11c429 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c429 0 14).toInstrSpec (add_r64_r64_effect_step 0x11c429 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11c42c [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x11c42c) (movR64R64Effect 0x11c42c 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11c42c 1 14).toInstrSpec (mov_r64_r64_effect_step 0x11c42c 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11c42f [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x11c42f) (notR64Effect 0x11c42f 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x11c42f 1).toInstrSpec (not_r64_effect_step 0x11c42f 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11c432 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x11c432) (orR64R64Effect 0x11c432 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11c432 1 0).toInstrSpec (or_r64_r64_effect_step 0x11c432 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11c435 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x11c435) (shrR64Effect 0x11c435 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c435 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x11c435 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11c439 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x11c439 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c439 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c439 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c439 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11c439 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x11c43e [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x11c43e) (leaR64Effect 0x11c43e 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11c43e 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x11c43e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11c443 [0x31, 0xC9] (fun s => s.RIP = 0x11c443) (xorR32R32Effect 0x11c443 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c443 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x11c443 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c402) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c404) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c406) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c408) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c409) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c40d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c410) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c413) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c417) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c41b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c41f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c429) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c42c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 79), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c42f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 81), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c432) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 77), (1, 83), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c435) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 77), (1, 85), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c439) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 77), (1, 85), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c43e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(1, 85), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c443) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 89), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c445) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11c400_1 code

theorem block_l11c400 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c400 :=
  Rest.liftedBlock (rest_l11c400 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c400 x hx)

theorem rest_l11c4c4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c4c4 bytes_l11c4c4) (entryMap (live .l11c4c4))
      3 0x11c4c4 bytes_l11c4c4 b_l11c4c4 := by
  have f0 : InstrSpec 0x11c4c4 [0x88, 0x44, 0x24, 0x07] (StorePre 0x11c4c4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11c4c4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11c4c4 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11c4c4 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x11c4c4 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11c4c8 [0x3C, 0x01] (fun s => s.RIP = 0x11c4c8) (cmpAlImm8Effect 0x11c4c8 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x11c4c8 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x11c4c8 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4c8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x11c4ca 5 0x20) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c4c4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c4c4 :=
  Rest.liftedBlock (rest_l11c4c4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c4c4 x hx)

theorem rest_l11c4cc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c4cc bytes_l11c4cc) (entryMap (live .l11c4cc))
      12 0x11c4cc bytes_l11c4cc b_l11c4cc := by
  have f0 : InstrSpec 0x11c4cc [0x4C, 0x89, 0x33] (StorePre 0x11c4cc 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11c4cc + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11c4cc 14 (.base 3 .none))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c4cc 14 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11c4cc 0x4c (by decide) 6 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11c4cf [0x4C, 0x89, 0x7B, 0x08] (StorePre 0x11c4cf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x11c4cf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c4cf 15 (.base 3 (.d8 0x8)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c4cf 15 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11c4cf 0x4c (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11c4d3 [0x4C, 0x89, 0x63, 0x10] (StorePre 0x11c4d3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x11c4d3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c4d3 12 (.base 3 (.d8 0x10)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c4d3 12 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11c4d3 0x4c (by decide) 4 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11c4d7 [0x4C, 0x89, 0x6B, 0x18] (StorePre 0x11c4d7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x11c4d7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c4d7 13 (.base 3 (.d8 0x18)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c4d7 13 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11c4d7 0x4c (by decide) 5 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11c4db [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x11c4db) (movR64R64Effect 0x11c4db 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c4db 0 3).toInstrSpec (mov_r64_r64_effect_step 0x11c4db 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c4de [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x11c4de) (addR64Imm8Effect 0x11c4de 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11c4de 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x11c4de 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c4e2 [0x5B] (PopPre 0x11c4e2) (popR64Effect 0x11c4e2 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c4e2 1 3).toInstrSpec (pop_r64_effect_step 0x11c4e2 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x11c4e3 [0x41, 0x5C] (PopPre 0x11c4e3) (popR64Effect 0x11c4e3 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c4e3 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11c4e3 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x11c4e5 [0x41, 0x5D] (PopPre 0x11c4e5) (popR64Effect 0x11c4e5 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c4e5 2 13).toInstrSpec (pop_r64_rex_effect_step 0x11c4e5 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x11c4e7 [0x41, 0x5E] (PopPre 0x11c4e7) (popR64Effect 0x11c4e7 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c4e7 2 14).toInstrSpec (pop_r64_rex_effect_step 0x11c4e7 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x11c4e9 [0x41, 0x5F] (PopPre 0x11c4e9) (popR64Effect 0x11c4e9 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c4e9 2 15).toInstrSpec (pop_r64_rex_effect_step 0x11c4e9 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x11c4eb [0xC3] (RetPre 0x11c4eb) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11c4eb).toInstrSpec (ret_effect_step 0x11c4eb) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4cf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4d3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4d7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4db) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4de) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4e2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4e3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4e5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4e7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4e9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 74), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c4eb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 78) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 77), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) f11 (by decide) rfl rfl rfl (by decide)

theorem block_l11c4cc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c4cc :=
  Rest.liftedBlock (rest_l11c4cc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c4cc x hx)

theorem rest_l11c4ec [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c4ec bytes_l11c4ec) (entryMap (live .l11c4ec))
      6 0x11c4ec bytes_l11c4ec b_l11c4ec := by
  have f0 : InstrSpec 0x11c4ec [0x48, 0x8D, 0x74, 0x24, 0x07] (fun s => s.RIP = 0x11c4ec) (leaR64Effect 0x11c4ec 6 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11c4ec 6 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x11c4ec 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c4f1 [0x31, 0xFF] (fun s => s.RIP = 0x11c4f1) (xorR32R32Effect 0x11c4f1 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c4f1 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c4f1 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x11c4f3 [0x48, 0xC7, 0xC2, 0xDD, 0x31, 0x20, 0x00] (fun s => s.RIP = 0x11c4f3) (movR64Imm32Effect 0x11c4f3 2 0x2031dd)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11c4f3 2 0x2031dd).toInstrSpec (mov_r64_imm32_effect_step 0x11c4f3 0x48 0xc2 (by decide) (by decide) (by decide) 0x2031dd) pre_rip
  have f3 : InstrSpec 0x11c4fa [0x31, 0xC9] (fun s => s.RIP = 0x11c4fa) (xorR32R32Effect 0x11c4fa 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c4fa 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x11c4fa 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x11c4fc [0x49, 0xC7, 0xC1, 0xE0, 0x31, 0x20, 0x00] (fun s => s.RIP = 0x11c4fc) (movR64Imm32Effect 0x11c4fc 9 0x2031e0)
      [] [] [.reg 9, .rip] :=
    (movR64Imm32Effect_footprint 0x11c4fc 9 0x2031e0).toInstrSpec (mov_r64_imm32_effect_step 0x11c4fc 0x49 0xc1 (by decide) (by decide) (by decide) 0x2031e0) pre_rip
  have f5 : InstrSpec 0x11c503 [0xE8, 0x00, 0x8F, 0xFF, 0xFF] (PushPre 0x11c503 5) (callEffect (fun _ => 0x115408) 0x11c508)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c503 0x115408 0x11c508).toInstrSpec (call_rel32_effect_step 0x11c503 0xffff8f00 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)]) (p' := 0x11c4f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x11c4f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x11c4fa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x11c4fc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)]) (p' := 0x11c503) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 59), (2, 57), (4, 63), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)]) (p' := 0x115408) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l11c4ec [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c4ec :=
  Rest.liftedBlock (rest_l11c4ec code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c4ec x hx)

theorem rest_l11c508 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c508 bytes_l11c508) (entryMap (live .l11c508))
      1 0x11c508 bytes_l11c508 b_l11c508 := by
  have f0 : InstrSpec 0x11c508 [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c508) (fun _ => nopEffect 0x11c508 8)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11c508 8).toInstrSpec (nop_m_effect_step 0x11c508 [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c510) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l11c508 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c508 :=
  Rest.liftedBlock (rest_l11c508 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c508 x hx)

theorem rest_l120350 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120350 bytes_l120350) (entryMap (live .l120350))
      18 0x120350 bytes_l120350 b_l120350 := by
  have f0 : InstrSpec 0x120350 [0x41, 0x56] (PushPre 0x120350 2) (pushR64Effect 0x120350 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120350 2 14).toInstrSpec (push_r64_rex_effect_step 0x120350 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x120352 [0x53] (PushPre 0x120352 1) (pushR64Effect 0x120352 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120352 1 3).toInstrSpec (push_r64_effect_step 0x120352 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x120353 [0x48, 0x83, 0xEC, 0x58] (fun s => s.RIP = 0x120353) (subR64Imm8Effect 0x120353 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x120353 4 0x58).toInstrSpec (sub_r64_imm8_effect_step 0x120353 0x48 0xec 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x120357 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x120357) (movR64R64Effect 0x120357 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x120357 3 7).toInstrSpec (mov_r64_r64_effect_step 0x120357 0x48 0xfb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12035a [0x48, 0x8B, 0x46, 0x20] (LoadPre 0x12035a (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x12035a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12035a 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12035a 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x12035a 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12035e [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x12035e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12035e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12035e 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12035e 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x12035e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x120363 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x120363 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x120363 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120363 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120363 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x120363 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x120367 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x120367 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120367 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120367 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120367 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x120367 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12036c [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x12036c (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x12036c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12036c 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12036c 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12036c 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x120370 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x120370 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120370 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120370 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120370 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x120370 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x120375 [0x48, 0x8B, 0x06] (LoadPre 0x120375 (fun s => AddrMode.addr (.base 6 .none) s (0x120375 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x120375 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120375 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x120375 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x120378 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x120378 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x120378 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120378 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120378 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120378 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12037c [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x12037c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12037c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12037c 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12037c 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12037c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x120381 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x120381 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120381 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120381 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120381 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x120381 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x120386 [0x4C, 0x8D, 0x74, 0x24, 0x30] (fun s => s.RIP = 0x120386) (leaR64Effect 0x120386 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x120386 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x120386 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x12038b [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x12038b) (leaR64Effect 0x12038b 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x12038b 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x12038b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x120390 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x120390) (movR64R64Effect 0x120390 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x120390 7 14).toInstrSpec (mov_r64_r64_effect_step 0x120390 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x120393 [0xE8, 0x98, 0x45, 0xFF, 0xFF] (PushPre 0x120393 5) (callEffect (fun _ => 0x114930) 0x120398)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120393 0x114930 0x120398).toInstrSpec (call_rel32_effect_step 0x120393 0xffff4598 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120352) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120353) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120357) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12035a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12035e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120363) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120367) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12036c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120370) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120375) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120378) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12037c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120381) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120386) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12038b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 78), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120390) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 78), (7, 80), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120393) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 82), (5, 5), (6, 78), (7, 80), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f17 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l120350 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120350 :=
  Rest.liftedBlock (rest_l120350 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120350 x hx)

theorem rest_l120398 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120398 bytes_l120398) (entryMap (live .l120398))
      3 0x120398 bytes_l120398 b_l120398 := by
  have f0 : InstrSpec 0x120398 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x120398) (movR64R64Effect 0x120398 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x120398 7 3).toInstrSpec (mov_r64_r64_effect_step 0x120398 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12039b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x12039b) (movR64R64Effect 0x12039b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12039b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x12039b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12039e [0xE8, 0x2D, 0x45, 0xFF, 0xFF] (PushPre 0x12039e 5) (callEffect (fun _ => 0x1148d0) 0x1203a3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12039e 0x1148d0 0x1203a3).toInstrSpec (call_rel32_effect_step 0x12039e 0xffff452d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12039b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12039e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l120398 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120398 :=
  Rest.liftedBlock (rest_l120398 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120398 x hx)

theorem rest_l1203a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1203a3 bytes_l1203a3) (entryMap (live .l1203a3))
      5 0x1203a3 bytes_l1203a3 b_l1203a3 := by
  have f0 : InstrSpec 0x1203a3 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1203a3) (movR64R64Effect 0x1203a3 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1203a3 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1203a3 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1203a6 [0x48, 0x83, 0xC4, 0x58] (fun s => s.RIP = 0x1203a6) (addR64Imm8Effect 0x1203a6 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1203a6 4 0x58).toInstrSpec (add_r64_imm8_effect_step 0x1203a6 0x48 0xc4 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1203aa [0x5B] (PopPre 0x1203aa) (popR64Effect 0x1203aa 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1203aa 1 3).toInstrSpec (pop_r64_effect_step 0x1203aa 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1203ab [0x41, 0x5E] (PopPre 0x1203ab) (popR64Effect 0x1203ab 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1203ab 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1203ab 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1203ad [0xC3] (RetPre 0x1203ad) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1203ad).toInstrSpec (ret_effect_step 0x1203ad) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203a6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203aa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203ad) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l1203a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1203a3 :=
  Rest.liftedBlock (rest_l1203a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1203a3 x hx)

theorem rest_l1203b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1203b0 bytes_l1203b0) (entryMap (live .l1203b0))
      4 0x1203b0 bytes_l1203b0 b_l1203b0 := by
  have f0 : InstrSpec 0x1203b0 [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x1203b0) (subR64Imm8Effect 0x1203b0 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1203b0 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x1203b0 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1203b4 [0x48, 0x8D, 0x77, 0x28] (fun s => s.RIP = 0x1203b4) (leaR64Effect 0x1203b4 6 (.base 7 (.d8 0x28)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1203b4 6 (.base 7 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x1203b4 0x48 (by decide) 6 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1203b8 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1203b8) (movR64R64Effect 0x1203b8 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1203b8 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1203b8 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1203bb [0xE8, 0x70, 0x45, 0xFF, 0xFF] (PushPre 0x1203bb 5) (callEffect (fun _ => 0x114930) 0x1203c0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1203bb 0x114930 0x1203c0).toInstrSpec (call_rel32_effect_step 0x1203bb 0xffff4570 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 55), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203b8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 55), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203bb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1203b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1203b0 :=
  Rest.liftedBlock (rest_l1203b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1203b0 x hx)

theorem rest_l1203c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1203c0 bytes_l1203c0) (entryMap (live .l1203c0))
      4 0x1203c0 bytes_l1203c0 b_l1203c0 := by
  have f0 : InstrSpec 0x1203c0 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x1203c0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1203c0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1203c0 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1203c0 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x1203c0 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1203c4 [0x24, 0x01] (fun s => s.RIP = 0x1203c4) (andAlImm8Effect 0x1203c4 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1203c4 0x1).toInstrSpec (and_al_imm8_effect_step 0x1203c4 0x1) pre_rip
  have f2 : InstrSpec 0x1203c6 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1203c6) (movzxR32R8Effect 0x1203c6 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1203c6 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1203c6 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1203c9 [0xE8, 0x82, 0x79, 0x00, 0x00] (PushPre 0x1203c9 5) (callEffect (fun _ => 0x127d50) 0x1203ce)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1203c9 0x127d50 0x1203ce).toInstrSpec (call_rel32_effect_step 0x1203c9 0x7982 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203c6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1203c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1203c0 :=
  Rest.liftedBlock (rest_l1203c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1203c0 x hx)

theorem rest_l1203ce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1203ce bytes_l1203ce) (entryMap (live .l1203ce))
      2 0x1203ce bytes_l1203ce b_l1203ce := by
  have f0 : InstrSpec 0x1203ce [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x1203ce) (addR64Imm8Effect 0x1203ce 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1203ce 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x1203ce 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1203d2 [0xC3] (RetPre 0x1203d2) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1203d2).toInstrSpec (ret_effect_step 0x1203d2) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l1203ce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1203ce :=
  Rest.liftedBlock (rest_l1203ce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1203ce x hx)

theorem rest_l120470_4 [Bindings] (code : CodeMap) :
    Rest (n := 201) code lifted (codeRange 0x120470 bytes_l120470) [(0, 197), (1, 82), (2, 194), (3, 120), (4, 199), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x120577 bytes_l120470_4 b_l120470_4 := by
  have f80 : InstrSpec 0x120577 [0x5B] (PopPre 0x120577) (popR64Effect 0x120577 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120577 1 3).toInstrSpec (pop_r64_effect_step 0x120577 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f81 : InstrSpec 0x120578 [0x41, 0x5C] (PopPre 0x120578) (popR64Effect 0x120578 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120578 2 12).toInstrSpec (pop_r64_rex_effect_step 0x120578 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f82 : InstrSpec 0x12057a [0x41, 0x5D] (PopPre 0x12057a) (popR64Effect 0x12057a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12057a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x12057a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f83 : InstrSpec 0x12057c [0x41, 0x5E] (PopPre 0x12057c) (popR64Effect 0x12057c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12057c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x12057c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f84 : InstrSpec 0x12057e [0x41, 0x5F] (PopPre 0x12057e) (popR64Effect 0x12057e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12057e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x12057e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f85 : InstrSpec 0x120580 [0x5D] (PopPre 0x120580) (popR64Effect 0x120580 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120580 1 5).toInstrSpec (pop_r64_effect_step 0x120580 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f86 : InstrSpec 0x120581 [0xC3] (RetPre 0x120581) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x120581).toInstrSpec (ret_effect_step 0x120581) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f80 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 202) f80 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 203) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 202), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120578) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f81 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 205) f81 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 206) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 205), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12057a) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f82 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 208) f82 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 209) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 208), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12057c) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f83 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 211) f83 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 212) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 211), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 210), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12057e) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f84 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 214) f84 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 215) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 214), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 210), (15, 213), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120580) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f85 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 217) f85 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 218) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 217), (5, 216), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 210), (15, 213), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120581) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f86 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 220) f86 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 221) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 220), (5, 216), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 210), (15, 213), (22, 22), (39, 39), (50, 50), (51, 51)]) f86 (by decide) rfl rfl rfl (by decide)

theorem rest_l120470_3 [Bindings] (code : CodeMap) :
    Rest (n := 172) code lifted (codeRange 0x120470 bytes_l120470) [(0, 170), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]
      27 0x12052e bytes_l120470_3 b_l120470_3 := by
  have f60 : InstrSpec 0x12052e [0x0F, 0xB6, 0x76, 0x50] (LoadPre 0x12052e (fun s => AddrMode.addr (.base 6 (.d8 0x50)) s (0x12052e + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12052e 4 6 (.base 6 (.d8 0x50)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x12052e 4 6 (.base 6 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x12052e 6 (.base 6 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x120532 [0x0F, 0xB6, 0x52, 0x50] (LoadPre 0x120532 (fun s => AddrMode.addr (.base 2 (.d8 0x50)) s (0x120532 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x120532 4 2 (.base 2 (.d8 0x50)))
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x120532 4 2 (.base 2 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x120532 2 (.base 2 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x120536 [0x4C, 0x8B, 0x0C, 0x24] (LoadPre 0x120536 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x120536 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120536 9 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x120536 9 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x120536 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f63 : InstrSpec 0x12053a [0x41, 0xF6, 0xD9] (fun s => s.RIP = 0x12053a) (negR8Effect 0x12053a 3 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR8Effect_footprint 0x12053a 3 9).toInstrSpec (neg_r8_rex_effect_step 0x12053a 0x41 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x12053d [0x40, 0x30, 0xF2] (fun s => s.RIP = 0x12053d) (xorR8R8Effect 0x12053d 3 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR8R8Effect_footprint 0x12053d 3 2 6).toInstrSpec (xor_r8_r8_rex_effect_step 0x12053d 0x40 0xf2 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x120540 [0x44, 0x20, 0xCA] (fun s => s.RIP = 0x120540) (andR8R8Effect 0x120540 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (andR8R8Effect_footprint 0x120540 3 2 9).toInstrSpec (and_r8_r8_rex_effect_step 0x120540 0x44 0xca (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x120543 [0x48, 0x89, 0x0F] (StorePre 0x120543 3 (fun s => AddrMode.addr (.base 7 .none) s (0x120543 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x120543 1 (.base 7 .none))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120543 1 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x120543 0x48 (by decide) 1 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x120546 [0x4C, 0x89, 0x47, 0x08] (StorePre 0x120546 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x120546 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120546 8 (.base 7 (.d8 0x8)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120546 8 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x120546 0x4c (by decide) 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x12054a [0x4C, 0x89, 0x57, 0x10] (StorePre 0x12054a 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x12054a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12054a 10 (.base 7 (.d8 0x10)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12054a 10 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12054a 0x4c (by decide) 2 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f69 : InstrSpec 0x12054e [0x4C, 0x89, 0x5F, 0x18] (StorePre 0x12054e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x12054e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12054e 11 (.base 7 (.d8 0x18)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12054e 11 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12054e 0x4c (by decide) 3 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x120552 [0x48, 0x89, 0x5F, 0x20] (StorePre 0x120552 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x120552 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120552 3 (.base 7 (.d8 0x20)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120552 3 (.base 7 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x120552 0x48 (by decide) 3 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f71 : InstrSpec 0x120556 [0x4C, 0x89, 0x77, 0x28] (StorePre 0x120556 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x120556 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120556 14 (.base 7 (.d8 0x28)))
      [.gpr 14, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120556 14 (.base 7 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x120556 0x4c (by decide) 6 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x12055a [0x4C, 0x89, 0x7F, 0x30] (StorePre 0x12055a 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x12055a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12055a 15 (.base 7 (.d8 0x30)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12055a 15 (.base 7 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x12055a 0x4c (by decide) 7 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x12055e [0x4C, 0x89, 0x67, 0x38] (StorePre 0x12055e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x12055e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12055e 12 (.base 7 (.d8 0x38)))
      [.gpr 12, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12055e 12 (.base 7 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x12055e 0x4c (by decide) 4 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f74 : InstrSpec 0x120562 [0x4C, 0x89, 0x6F, 0x40] (StorePre 0x120562 4 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x120562 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120562 13 (.base 7 (.d8 0x40)))
      [.gpr 13, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120562 13 (.base 7 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x120562 0x4c (by decide) 5 (.base 7 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x120566 [0x48, 0x89, 0x47, 0x48] (StorePre 0x120566 4 (fun s => AddrMode.addr (.base 7 (.d8 0x48)) s (0x120566 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120566 0 (.base 7 (.d8 0x48)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120566 0 (.base 7 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x120566 0x48 (by decide) 0 (.base 7 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x12056a [0x40, 0x30, 0xF2] (fun s => s.RIP = 0x12056a) (xorR8R8Effect 0x12056a 3 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR8R8Effect_footprint 0x12056a 3 2 6).toInstrSpec (xor_r8_r8_rex_effect_step 0x12056a 0x40 0xf2 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x12056d [0x88, 0x57, 0x50] (StorePre 0x12056d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x50)) s (0x12056d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12056d 3 2 (.base 7 (.d8 0x50)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x12056d 3 2 (.base 7 (.d8 0x50))).toInstrSpec (mov_m8_r8_effect_step 0x12056d 2 (by decide) (.base 7 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x120570 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x120570) (movR64R64Effect 0x120570 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120570 0 7).toInstrSpec (mov_r64_r64_effect_step 0x120570 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x120573 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x120573) (addR64Imm8Effect 0x120573 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x120573 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x120573 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f60 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 170), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120532) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 170), (1, 82), (2, 174), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120536) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f62 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 170), (1, 82), (2, 174), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 176), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12053a) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f63 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 170), (1, 82), (2, 174), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12053d) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f64 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 170), (1, 82), (2, 180), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120540) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f65 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120543) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.exec (n := 184) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120546) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 185) (RestInside.exec (n := 185) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12054a) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12054e) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.exec (n := 187) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120552) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 188) (RestInside.exec (n := 188) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120556) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 189) (RestInside.exec (n := 189) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12055a) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 190) (RestInside.exec (n := 190) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12055e) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120562) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.exec (n := 192) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120566) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 193) (RestInside.exec (n := 193) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12056a) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 170), (1, 82), (2, 194), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12056d) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.exec (n := 196) (ρ' := [(0, 170), (1, 82), (2, 194), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120570) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120573) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f79 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 120), (4, 199), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120577) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120470_4 code

theorem rest_l120470_2 [Bindings] (code : CodeMap) :
    Rest (n := 132) code lifted (codeRange 0x120470 bytes_l120470) [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 130), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]
      47 0x1204ea bytes_l120470_2 b_l120470_2 := by
  have f40 : InstrSpec 0x1204ea [0x4C, 0x8B, 0x66, 0x30] (LoadPre 0x1204ea (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x1204ea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204ea 12 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1204ea 12 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1204ea 0x4c (by decide) 4 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x1204ee [0x4C, 0x8B, 0x7A, 0x30] (LoadPre 0x1204ee (fun s => AddrMode.addr (.base 2 (.d8 0x30)) s (0x1204ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204ee 15 (.base 2 (.d8 0x30)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1204ee 15 (.base 2 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1204ee 0x4c (by decide) 7 (.base 2 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x1204f2 [0x4D, 0x31, 0xE7] (fun s => s.RIP = 0x1204f2) (xorR64R64Effect 0x1204f2 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204f2 15 12).toInstrSpec (xor_r64_r64_effect_step 0x1204f2 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1204f5 [0x4D, 0x21, 0xCF] (fun s => s.RIP = 0x1204f5) (andR64R64Effect 0x1204f5 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204f5 15 9).toInstrSpec (and_r64_r64_effect_step 0x1204f5 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1204f8 [0x4D, 0x31, 0xE7] (fun s => s.RIP = 0x1204f8) (xorR64R64Effect 0x1204f8 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204f8 15 12).toInstrSpec (xor_r64_r64_effect_step 0x1204f8 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1204fb [0x4C, 0x8B, 0x6E, 0x38] (LoadPre 0x1204fb (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x1204fb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204fb 13 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1204fb 13 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1204fb 0x4c (by decide) 5 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x1204ff [0x4C, 0x8B, 0x62, 0x38] (LoadPre 0x1204ff (fun s => AddrMode.addr (.base 2 (.d8 0x38)) s (0x1204ff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204ff 12 (.base 2 (.d8 0x38)))
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1204ff 12 (.base 2 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1204ff 0x4c (by decide) 4 (.base 2 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x120503 [0x4D, 0x31, 0xEC] (fun s => s.RIP = 0x120503) (xorR64R64Effect 0x120503 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120503 12 13).toInstrSpec (xor_r64_r64_effect_step 0x120503 0x4d 0xec (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x120506 [0x4D, 0x21, 0xCC] (fun s => s.RIP = 0x120506) (andR64R64Effect 0x120506 12 9)
      [.gpr 12, .gpr 9] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120506 12 9).toInstrSpec (and_r64_r64_effect_step 0x120506 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x120509 [0x4D, 0x31, 0xEC] (fun s => s.RIP = 0x120509) (xorR64R64Effect 0x120509 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120509 12 13).toInstrSpec (xor_r64_r64_effect_step 0x120509 0x4d 0xec (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x12050c [0x48, 0x8B, 0x6E, 0x40] (LoadPre 0x12050c (fun s => AddrMode.addr (.base 6 (.d8 0x40)) s (0x12050c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12050c 5 (.base 6 (.d8 0x40)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x12050c 5 (.base 6 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x12050c 0x48 (by decide) 5 (.base 6 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x120510 [0x4C, 0x8B, 0x6A, 0x40] (LoadPre 0x120510 (fun s => AddrMode.addr (.base 2 (.d8 0x40)) s (0x120510 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120510 13 (.base 2 (.d8 0x40)))
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x120510 13 (.base 2 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x120510 0x4c (by decide) 5 (.base 2 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x120514 [0x49, 0x31, 0xED] (fun s => s.RIP = 0x120514) (xorR64R64Effect 0x120514 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120514 13 5).toInstrSpec (xor_r64_r64_effect_step 0x120514 0x49 0xed (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x120517 [0x4D, 0x21, 0xCD] (fun s => s.RIP = 0x120517) (andR64R64Effect 0x120517 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120517 13 9).toInstrSpec (and_r64_r64_effect_step 0x120517 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x12051a [0x49, 0x31, 0xED] (fun s => s.RIP = 0x12051a) (xorR64R64Effect 0x12051a 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12051a 13 5).toInstrSpec (xor_r64_r64_effect_step 0x12051a 0x49 0xed (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x12051d [0x48, 0x8B, 0x6E, 0x48] (LoadPre 0x12051d (fun s => AddrMode.addr (.base 6 (.d8 0x48)) s (0x12051d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12051d 5 (.base 6 (.d8 0x48)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x12051d 5 (.base 6 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x12051d 0x48 (by decide) 5 (.base 6 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f56 : InstrSpec 0x120521 [0x48, 0x8B, 0x42, 0x48] (LoadPre 0x120521 (fun s => AddrMode.addr (.base 2 (.d8 0x48)) s (0x120521 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120521 0 (.base 2 (.d8 0x48)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120521 0 (.base 2 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x120521 0x48 (by decide) 0 (.base 2 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f57 : InstrSpec 0x120525 [0x48, 0x31, 0xE8] (fun s => s.RIP = 0x120525) (xorR64R64Effect 0x120525 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120525 0 5).toInstrSpec (xor_r64_r64_effect_step 0x120525 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x120528 [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x120528) (andR64R64Effect 0x120528 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120528 0 9).toInstrSpec (and_r64_r64_effect_step 0x120528 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x12052b [0x48, 0x31, 0xE8] (fun s => s.RIP = 0x12052b) (xorR64R64Effect 0x12052b 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12052b 0 5).toInstrSpec (xor_r64_r64_effect_step 0x12052b 0x48 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f40 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204ee) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f41 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204f2) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f42 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204f5) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f43 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204f8) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204fb) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f45 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204ff) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f46 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 144), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120503) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f47 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 146), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120506) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f48 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 148), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120509) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f49 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12050c) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f50 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120510) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f51 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 154), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120514) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f52 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 156), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120517) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f53 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 158), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12051a) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f54 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12051d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f55 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120521) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f56 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 164), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120525) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f57 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 166), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120528) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 168), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12052b) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f59 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 170), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12052e) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120470_3 code

theorem rest_l120470_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x120470 bytes_l120470) [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      67 0x1204a6 bytes_l120470_1 b_l120470_1 := by
  have f20 : InstrSpec 0x1204a6 [0x4C, 0x8B, 0x5E, 0x10] (LoadPre 0x1204a6 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1204a6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204a6 11 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1204a6 11 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1204a6 0x4c (by decide) 3 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1204aa [0x4C, 0x8B, 0x52, 0x10] (LoadPre 0x1204aa (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1204aa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204aa 10 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1204aa 10 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1204aa 0x4c (by decide) 2 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1204ae [0x4D, 0x31, 0xDA] (fun s => s.RIP = 0x1204ae) (xorR64R64Effect 0x1204ae 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204ae 10 11).toInstrSpec (xor_r64_r64_effect_step 0x1204ae 0x4d 0xda (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1204b1 [0x4D, 0x21, 0xCA] (fun s => s.RIP = 0x1204b1) (andR64R64Effect 0x1204b1 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204b1 10 9).toInstrSpec (and_r64_r64_effect_step 0x1204b1 0x4d 0xca (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1204b4 [0x4D, 0x31, 0xDA] (fun s => s.RIP = 0x1204b4) (xorR64R64Effect 0x1204b4 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204b4 10 11).toInstrSpec (xor_r64_r64_effect_step 0x1204b4 0x4d 0xda (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1204b7 [0x48, 0x8B, 0x5E, 0x18] (LoadPre 0x1204b7 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1204b7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204b7 3 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1204b7 3 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1204b7 0x48 (by decide) 3 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x1204bb [0x4C, 0x8B, 0x5A, 0x18] (LoadPre 0x1204bb (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1204bb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204bb 11 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1204bb 11 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1204bb 0x4c (by decide) 3 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x1204bf [0x49, 0x31, 0xDB] (fun s => s.RIP = 0x1204bf) (xorR64R64Effect 0x1204bf 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204bf 11 3).toInstrSpec (xor_r64_r64_effect_step 0x1204bf 0x49 0xdb (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1204c2 [0x4D, 0x21, 0xCB] (fun s => s.RIP = 0x1204c2) (andR64R64Effect 0x1204c2 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204c2 11 9).toInstrSpec (and_r64_r64_effect_step 0x1204c2 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1204c5 [0x49, 0x31, 0xDB] (fun s => s.RIP = 0x1204c5) (xorR64R64Effect 0x1204c5 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204c5 11 3).toInstrSpec (xor_r64_r64_effect_step 0x1204c5 0x49 0xdb (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1204c8 [0x4C, 0x8B, 0x76, 0x20] (LoadPre 0x1204c8 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1204c8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204c8 14 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1204c8 14 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1204c8 0x4c (by decide) 6 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x1204cc [0x48, 0x8B, 0x5A, 0x20] (LoadPre 0x1204cc (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1204cc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204cc 3 (.base 2 (.d8 0x20)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1204cc 3 (.base 2 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1204cc 0x48 (by decide) 3 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x1204d0 [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x1204d0) (xorR64R64Effect 0x1204d0 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204d0 3 14).toInstrSpec (xor_r64_r64_effect_step 0x1204d0 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x1204d3 [0x4C, 0x21, 0xCB] (fun s => s.RIP = 0x1204d3) (andR64R64Effect 0x1204d3 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204d3 3 9).toInstrSpec (and_r64_r64_effect_step 0x1204d3 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1204d6 [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x1204d6) (xorR64R64Effect 0x1204d6 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204d6 3 14).toInstrSpec (xor_r64_r64_effect_step 0x1204d6 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x1204d9 [0x4C, 0x8B, 0x7E, 0x28] (LoadPre 0x1204d9 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x1204d9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204d9 15 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1204d9 15 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1204d9 0x4c (by decide) 7 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x1204dd [0x4C, 0x8B, 0x72, 0x28] (LoadPre 0x1204dd (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x1204dd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204dd 14 (.base 2 (.d8 0x28)))
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1204dd 14 (.base 2 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1204dd 0x4c (by decide) 6 (.base 2 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x1204e1 [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x1204e1) (xorR64R64Effect 0x1204e1 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204e1 14 15).toInstrSpec (xor_r64_r64_effect_step 0x1204e1 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1204e4 [0x4D, 0x21, 0xCE] (fun s => s.RIP = 0x1204e4) (andR64R64Effect 0x1204e4 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204e4 14 9).toInstrSpec (and_r64_r64_effect_step 0x1204e4 0x4d 0xce (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x1204e7 [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x1204e7) (xorR64R64Effect 0x1204e7 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204e7 14 15).toInstrSpec (xor_r64_r64_effect_step 0x1204e7 0x4d 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 74), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204aa) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 94), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204ae) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 96), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204b1) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 98), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204b4) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204b7) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204bb) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 104), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204bf) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 106), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204c2) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204c5) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204c8) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f30 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204cc) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f31 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 114), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204d0) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 116), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204d3) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 118), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204d6) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204d9) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f35 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204dd) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f36 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 124), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204e1) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f37 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 126), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204e4) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f38 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 128), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204e7) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f39 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 130), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204ea) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120470_2 code

theorem rest_l120470 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120470 bytes_l120470) (entryMap (live .l120470))
      87 0x120470 bytes_l120470 b_l120470 := by
  have f0 : InstrSpec 0x120470 [0x55] (PushPre 0x120470 1) (pushR64Effect 0x120470 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120470 1 5).toInstrSpec (push_r64_effect_step 0x120470 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x120471 [0x41, 0x57] (PushPre 0x120471 2) (pushR64Effect 0x120471 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120471 2 15).toInstrSpec (push_r64_rex_effect_step 0x120471 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x120473 [0x41, 0x56] (PushPre 0x120473 2) (pushR64Effect 0x120473 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120473 2 14).toInstrSpec (push_r64_rex_effect_step 0x120473 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x120475 [0x41, 0x55] (PushPre 0x120475 2) (pushR64Effect 0x120475 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120475 2 13).toInstrSpec (push_r64_rex_effect_step 0x120475 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x120477 [0x41, 0x54] (PushPre 0x120477 2) (pushR64Effect 0x120477 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120477 2 12).toInstrSpec (push_r64_rex_effect_step 0x120477 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x120479 [0x53] (PushPre 0x120479 1) (pushR64Effect 0x120479 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120479 1 3).toInstrSpec (push_r64_effect_step 0x120479 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12047a [0x50] (PushPre 0x12047a 1) (pushR64Effect 0x12047a 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12047a 1 0).toInstrSpec (push_r64_effect_step 0x12047a 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x12047b [0x44, 0x0F, 0xB6, 0xC9] (fun s => s.RIP = 0x12047b) (movzxR32R8Effect 0x12047b 4 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movzxR32R8Effect_footprint 0x12047b 4 9 1).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12047b 0x44 (by decide) 0xc9 (by decide)) pre_rip
  have f8 : InstrSpec 0x12047f [0x4C, 0x89, 0x0C, 0x24] (StorePre 0x12047f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12047f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12047f 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12047f 9 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x12047f 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x120483 [0x49, 0xF7, 0xD9] (fun s => s.RIP = 0x120483) (negR64Effect 0x120483 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR64Effect_footprint 0x120483 9).toInstrSpec (neg_r64_effect_step 0x120483 0x49 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x120486 [0x4C, 0x8B, 0x06] (LoadPre 0x120486 (fun s => AddrMode.addr (.base 6 .none) s (0x120486 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x120486 8 (.base 6 .none))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x120486 8 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x120486 0x4c (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x120489 [0x4C, 0x8B, 0x56, 0x08] (LoadPre 0x120489 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x120489 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120489 10 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x120489 10 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120489 0x4c (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12048d [0x48, 0x8B, 0x0A] (LoadPre 0x12048d (fun s => AddrMode.addr (.base 2 .none) s (0x12048d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12048d 1 (.base 2 .none))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12048d 1 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12048d 0x48 (by decide) 1 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x120490 [0x4C, 0x31, 0xC1] (fun s => s.RIP = 0x120490) (xorR64R64Effect 0x120490 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120490 1 8).toInstrSpec (xor_r64_r64_effect_step 0x120490 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x120493 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x120493) (andR64R64Effect 0x120493 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120493 1 9).toInstrSpec (and_r64_r64_effect_step 0x120493 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x120496 [0x4C, 0x31, 0xC1] (fun s => s.RIP = 0x120496) (xorR64R64Effect 0x120496 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120496 1 8).toInstrSpec (xor_r64_r64_effect_step 0x120496 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x120499 [0x4C, 0x8B, 0x42, 0x08] (LoadPre 0x120499 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x120499 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120499 8 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x120499 8 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120499 0x4c (by decide) 0 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x12049d [0x4D, 0x31, 0xD0] (fun s => s.RIP = 0x12049d) (xorR64R64Effect 0x12049d 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12049d 8 10).toInstrSpec (xor_r64_r64_effect_step 0x12049d 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1204a0 [0x4D, 0x21, 0xC8] (fun s => s.RIP = 0x1204a0) (andR64R64Effect 0x1204a0 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204a0 8 9).toInstrSpec (and_r64_r64_effect_step 0x1204a0 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1204a3 [0x4D, 0x31, 0xD0] (fun s => s.RIP = 0x1204a3) (xorR64R64Effect 0x1204a3 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204a3 8 10).toInstrSpec (xor_r64_r64_effect_step 0x1204a3 0x4d 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120471) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120473) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120475) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120477) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120479) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12047a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12047b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12047f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120483) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120486) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120489) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12048d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 76), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120490) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 78), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120493) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 80), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120496) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120499) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 84), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12049d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204a0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 88), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204a3) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204a6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120470_1 code

theorem block_l120470 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120470 :=
  Rest.liftedBlock (rest_l120470 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120470 x hx)

theorem rest_l124100 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124100 bytes_l124100) (entryMap (live .l124100))
      7 0x124100 bytes_l124100 b_l124100 := by
  have f0 : InstrSpec 0x124100 [0x41, 0x56] (PushPre 0x124100 2) (pushR64Effect 0x124100 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124100 2 14).toInstrSpec (push_r64_rex_effect_step 0x124100 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124102 [0x53] (PushPre 0x124102 1) (pushR64Effect 0x124102 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124102 1 3).toInstrSpec (push_r64_effect_step 0x124102 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124103 [0x50] (PushPre 0x124103 1) (pushR64Effect 0x124103 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124103 1 0).toInstrSpec (push_r64_effect_step 0x124103 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124104 [0x48, 0x8B, 0x4F, 0x10] (LoadPre 0x124104 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x124104 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124104 1 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124104 1 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x124104 0x48 (by decide) 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124108 [0x48, 0x8D, 0x41, 0x01] (fun s => s.RIP = 0x124108) (leaR64Effect 0x124108 0 (.base 1 (.d8 0x1)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x124108 0 (.base 1 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x124108 0x48 (by decide) 0 (.base 1 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12410c [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x12410c) (cmpR64R64Effect 0x12410c 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12410c 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x12410c 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124102) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124103) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124104) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124108) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 59), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12410c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 59), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12410f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x12410f 4 0x9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124100 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124100 :=
  Rest.liftedBlock (rest_l124100 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124100 x hx)

theorem rest_l124111 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124111 bytes_l124111) (entryMap (live .l124111))
      2 0x124111 bytes_l124111 b_l124111 := by
  have f0 : InstrSpec 0x124111 [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x124111) (cmpR64R64Effect 0x124111 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x124111 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x124111 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124114) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x124114 5 0xa5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124111 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124111 :=
  Rest.liftedBlock (rest_l124111 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124111 x hx)

theorem rest_l12411a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12411a bytes_l12411a) (entryMap (live .l12411a))
      2 0x12411a bytes_l12411a b_l12411a := by
  have f0 : InstrSpec 0x12411a [0x48, 0x39, 0xCE] (fun s => s.RIP = 0x12411a) (cmpR64R64Effect 0x12411a 6 1)
      [.gpr 6, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12411a 6 1).toInstrSpec (cmp_r64_r64_effect_step 0x12411a 0x48 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12411d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x12411d 6 0x5d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12411a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12411a :=
  Rest.liftedBlock (rest_l12411a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12411a x hx)

theorem rest_l12411f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12411f bytes_l12411f) (entryMap (live .l12411f))
      6 0x12411f bytes_l12411f b_l12411f := by
  have f0 : InstrSpec 0x12411f [0x48, 0x89, 0x47, 0x10] (StorePre 0x12411f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x12411f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12411f 0 (.base 7 (.d8 0x10)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12411f 0 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12411f 0x48 (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124123 [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x124123 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x124123 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124123 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124123 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x124123 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124127 [0x48, 0x8B, 0x47, 0x20] (LoadPre 0x124127 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x124127 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124127 0 (.base 7 (.d8 0x20)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x124127 0 (.base 7 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x124127 0x48 (by decide) 0 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12412b [0x48, 0x89, 0x47, 0x18] (StorePre 0x12412b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x12412b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12412b 0 (.base 7 (.d8 0x18)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12412b 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12412b 0x48 (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12412f [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x12412f) (testR64R64Effect 0x12412f 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12412f 1 1).toInstrSpec (test_r64_r64_effect_step 0x12412f 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124123) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124127) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 54), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12412b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (1, 54), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12412f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 56), (1, 54), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124132) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x124132 4 0x58) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12411f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12411f :=
  Rest.liftedBlock (rest_l12411f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12411f x hx)

theorem rest_l124134 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124134 bytes_l124134) (entryMap (live .l124134))
      2 0x124134 bytes_l124134 b_l124134 := by
  have f0 : InstrSpec 0x124134 [0x48, 0x83, 0xF9, 0x07] (fun s => s.RIP = 0x124134) (cmpR64Imm8Effect 0x124134 1 0x7)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x124134 1 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x124134 0x48 0xf9 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124138) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x124138 7 0x64) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124134 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124134 :=
  Rest.liftedBlock (rest_l124134 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124134 x hx)

theorem rest_l12413a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12413a bytes_l12413a) (entryMap (live .l12413a))
      8 0x12413a bytes_l12413a b_l12413a := by
  have f0 : InstrSpec 0x12413a [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12413a 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12413a + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12413a (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12413a (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12413a 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124142 [0x48, 0x8B, 0x37] (LoadPre 0x124142 (fun s => AddrMode.addr (.base 7 .none) s (0x124142 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x124142 6 (.base 7 .none))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124142 6 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x124142 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124145 [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x124145) (movR64R64Effect 0x124145 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x124145 2 4).toInstrSpec (mov_r64_r64_effect_step 0x124145 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124148 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x124148) (movR64R64Effect 0x124148 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x124148 14 7).toInstrSpec (mov_r64_r64_effect_step 0x124148 0x49 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12414b [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x12414b) (movR64R64Effect 0x12414b 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12414b 7 2).toInstrSpec (mov_r64_r64_effect_step 0x12414b 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12414e [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x12414e) (movR64R64Effect 0x12414e 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12414e 2 1).toInstrSpec (mov_r64_r64_effect_step 0x12414e 0x48 0xca (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x124151 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x124151) (movR64R64Effect 0x124151 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x124151 3 0).toInstrSpec (mov_r64_r64_effect_step 0x124151 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x124154 [0xFF, 0x15, 0x76, 0xFC, 0x0D, 0x00] (GoesTo (CallMemPre 0x124154 (.rip 0xdfc76)) (callEffect (callMemPtr 0x124154 (.rip 0xdfc76)) (0x124154 + BitVec.ofNat 64 (callMemLen (.rip 0xdfc76)))) 0x12a820) (callEffect (callMemPtr 0x124154 (.rip 0xdfc76)) (0x124154 + BitVec.ofNat 64 (callMemLen (.rip 0xdfc76))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x124154 (.rip 0xdfc76)).toInstrSpec (call_m64_effect_step 0x124154 (.rip 0xdfc76) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124142) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 54), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124145) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (4, 4), (5, 5), (6, 54), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124148) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 56), (4, 4), (5, 5), (6, 54), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12414b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 56), (4, 4), (5, 5), (6, 54), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12414e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 54), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124151) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 64), (4, 4), (5, 5), (6, 54), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124154) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 64), (4, 66), (5, 5), (6, 54), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f7 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l12413a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12413a :=
  Rest.liftedBlock (rest_l12413a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12413a x hx)

theorem rest_l12415a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12415a bytes_l12415a) (entryMap (live .l12415a))
      9 0x12415a bytes_l12415a b_l12415a := by
  have f0 : InstrSpec 0x12415a [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x12415a) (movR64R64Effect 0x12415a 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12415a 0 3).toInstrSpec (mov_r64_r64_effect_step 0x12415a 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12415d [0x48, 0x8B, 0x14, 0x24] (LoadPre 0x12415d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12415d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12415d 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12415d 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12415d 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124161 [0x49, 0x89, 0x56, 0x20] (StorePre 0x124161 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x124161 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124161 2 (.base 14 (.d8 0x20)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124161 2 (.base 14 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x124161 0x49 (by decide) 2 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124165 [0x49, 0xC7, 0x06, 0x01, 0x00, 0x00, 0x00] (StorePre 0x124165 7 (fun s => AddrMode.addr (.base 14 .none) s (0x124165 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x124165 (.base 14 .none) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124165 (.base 14 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x124165 0x49 (by decide) (.base 14 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12416c [0x49, 0xC7, 0x46, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12416c 8 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12416c + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12416c (.base 14 (.d8 0x8)) 0x0)
      [.gpr 14] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12416c (.base 14 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12416c 0x49 (by decide) (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124174 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x124174) (addR64Imm8Effect 0x124174 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124174 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x124174 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x124178 [0x5B] (PopPre 0x124178) (popR64Effect 0x124178 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124178 1 3).toInstrSpec (pop_r64_effect_step 0x124178 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x124179 [0x41, 0x5E] (PopPre 0x124179) (popR64Effect 0x124179 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124179 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124179 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x12417b [0xC3] (RetPre 0x12417b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12417b).toInstrSpec (ret_effect_step 0x12417b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12415d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124161) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124165) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12416c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124174) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124178) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 62), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124179) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 62), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12417b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 70) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 62), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l12415a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12415a :=
  Rest.liftedBlock (rest_l12415a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12415a x hx)

theorem rest_l12417c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12417c bytes_l12417c) (entryMap (live .l12417c))
      6 0x12417c bytes_l12417c b_l12417c := by
  have f0 : InstrSpec 0x12417c [0x48, 0x8B, 0x47, 0x18] (LoadPre 0x12417c (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x12417c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12417c 0 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12417c 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12417c 0x48 (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124180 [0x48, 0x8B, 0x57, 0x20] (LoadPre 0x124180 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x124180 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124180 2 (.base 7 (.d8 0x20)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124180 2 (.base 7 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x124180 0x48 (by decide) 2 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124184 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x124184) (addR64Imm8Effect 0x124184 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124184 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x124184 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124188 [0x5B] (PopPre 0x124188) (popR64Effect 0x124188 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124188 1 3).toInstrSpec (pop_r64_effect_step 0x124188 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124189 [0x41, 0x5E] (PopPre 0x124189) (popR64Effect 0x124189 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124189 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124189 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12418b [0xC3] (RetPre 0x12418b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12418b).toInstrSpec (ret_effect_step 0x12418b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124180) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124184) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 55), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124188) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 59), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124189) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 59), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12418b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 67) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 59), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l12417c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12417c :=
  Rest.liftedBlock (rest_l12417c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12417c x hx)

theorem rest_l12418c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12418c bytes_l12418c) (entryMap (live .l12418c))
      6 0x12418c bytes_l12418c b_l12418c := by
  have f0 : InstrSpec 0x12418c [0x48, 0xC7, 0x47, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12418c 8 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x12418c + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12418c (.base 7 (.d8 0x20)) 0x0)
      [.gpr 7] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12418c (.base 7 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12418c 0x48 (by decide) (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124194 [0x31, 0xD2] (fun s => s.RIP = 0x124194) (xorR32R32Effect 0x124194 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x124194 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x124194 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x124196 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x124196) (addR64Imm8Effect 0x124196 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124196 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x124196 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12419a [0x5B] (PopPre 0x12419a) (popR64Effect 0x12419a 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12419a 1 3).toInstrSpec (pop_r64_effect_step 0x12419a 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x12419b [0x41, 0x5E] (PopPre 0x12419b) (popR64Effect 0x12419b 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12419b 2 14).toInstrSpec (pop_r64_rex_effect_step 0x12419b 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12419d [0xC3] (RetPre 0x12419d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12419d).toInstrSpec (ret_effect_step 0x12419d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124194) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124196) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12419a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 58), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12419b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 58), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12419d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 66) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 58), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l12418c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12418c :=
  Rest.liftedBlock (rest_l12418c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12418c x hx)

theorem rest_l12419e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12419e bytes_l12419e) (entryMap (live .l12419e))
      11 0x12419e bytes_l12419e b_l12419e := by
  have f0 : InstrSpec 0x12419e [0x48, 0x8B, 0x37] (LoadPre 0x12419e (fun s => AddrMode.addr (.base 7 .none) s (0x12419e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12419e 6 (.base 7 .none))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12419e 6 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12419e 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1241a1 [0x48, 0x83, 0xC1, 0xF8] (fun s => s.RIP = 0x1241a1) (addR64Imm8Effect 0x1241a1 1 0xf8)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1241a1 1 0xf8).toInstrSpec (add_r64_imm8_effect_step 0x1241a1 0x48 0xc1 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1241a5 [0x48, 0x8B, 0x16] (LoadPre 0x1241a5 (fun s => AddrMode.addr (.base 6 .none) s (0x1241a5 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1241a5 2 (.base 6 .none))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1241a5 2 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1241a5 0x48 (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1241a8 [0x48, 0x83, 0xC6, 0x08] (fun s => s.RIP = 0x1241a8) (addR64Imm8Effect 0x1241a8 6 0x8)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1241a8 6 0x8).toInstrSpec (add_r64_imm8_effect_step 0x1241a8 0x48 0xc6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1241ac [0x48, 0x89, 0x57, 0x20] (StorePre 0x1241ac 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x1241ac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1241ac 2 (.base 7 (.d8 0x20)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1241ac 2 (.base 7 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1241ac 0x48 (by decide) 2 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1241b0 [0x48, 0x89, 0x37] (StorePre 0x1241b0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1241b0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1241b0 6 (.base 7 .none))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1241b0 6 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1241b0 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1241b3 [0x48, 0x89, 0x4F, 0x08] (StorePre 0x1241b3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1241b3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1241b3 1 (.base 7 (.d8 0x8)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1241b3 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1241b3 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1241b7 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x1241b7) (addR64Imm8Effect 0x1241b7 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1241b7 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x1241b7 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1241bb [0x5B] (PopPre 0x1241bb) (popR64Effect 0x1241bb 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1241bb 1 3).toInstrSpec (pop_r64_effect_step 0x1241bb 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x1241bc [0x41, 0x5E] (PopPre 0x1241bc) (popR64Effect 0x1241bc 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1241bc 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1241bc 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x1241be [0xC3] (RetPre 0x1241be) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1241be).toInstrSpec (ret_effect_step 0x1241be) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241a5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241a8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241ac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241b0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241b3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241b7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 55), (2, 57), (4, 64), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241bb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 66), (4, 67), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241bc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 66), (4, 70), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241be) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 74) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 66), (4, 73), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f10 (by decide) rfl rfl rfl (by decide)

theorem block_l12419e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12419e :=
  Rest.liftedBlock (rest_l12419e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12419e x hx)

theorem rest_l1241bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1241bf bytes_l1241bf) (entryMap (live .l1241bf))
      4 0x1241bf bytes_l1241bf b_l1241bf := by
  have f0 : InstrSpec 0x1241bf [0xBE, 0x41, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1241bf) (movR32Imm32Effect 0x1241bf 5 6 0x41)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1241bf 5 6 0x41).toInstrSpec (mov_r32_imm32_effect_step 0x1241bf 0xbe (by decide) 0x41) pre_rip
  have f1 : InstrSpec 0x1241c4 [0x48, 0xC7, 0xC7, 0x00, 0x34, 0x20, 0x00] (fun s => s.RIP = 0x1241c4) (movR64Imm32Effect 0x1241c4 7 0x203400)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x1241c4 7 0x203400).toInstrSpec (mov_r64_imm32_effect_step 0x1241c4 0x48 0xc7 (by decide) (by decide) (by decide) 0x203400) pre_rip
  have f2 : InstrSpec 0x1241cb [0x48, 0xC7, 0xC2, 0x48, 0x34, 0x20, 0x00] (fun s => s.RIP = 0x1241cb) (movR64Imm32Effect 0x1241cb 2 0x203448)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1241cb 2 0x203448).toInstrSpec (mov_r64_imm32_effect_step 0x1241cb 0x48 0xc2 (by decide) (by decide) (by decide) 0x203448) pre_rip
  have f3 : InstrSpec 0x1241d2 [0xE8, 0x79, 0x55, 0x00, 0x00] (PushPre 0x1241d2 5) (callEffect (fun _ => 0x129750) 0x1241d7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1241d2 0x129750 0x1241d7).toInstrSpec (call_rel32_effect_step 0x1241d2 0x5579 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x1241c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x1241cb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x1241d2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129750) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1241bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1241bf :=
  Rest.liftedBlock (rest_l1241bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1241bf x hx)

theorem rest_l1241d7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1241d7 bytes_l1241d7) (entryMap (live .l1241d7))
      1 0x1241d7 bytes_l1241d7 b_l1241d7 := by
  have f0 : InstrSpec 0x1241d7 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1241d7) (fun _ => nopEffect 0x1241d7 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1241d7 9).toInstrSpec (nop_m_effect_step 0x1241d7 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241e0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l1241d7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1241d7 :=
  Rest.liftedBlock (rest_l1241d7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1241d7 x hx)

theorem rest_l1241e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1241e0 bytes_l1241e0) (entryMap (live .l1241e0))
      6 0x1241e0 bytes_l1241e0 b_l1241e0 := by
  have f0 : InstrSpec 0x1241e0 [0x41, 0x56] (PushPre 0x1241e0 2) (pushR64Effect 0x1241e0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1241e0 2 14).toInstrSpec (push_r64_rex_effect_step 0x1241e0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1241e2 [0x53] (PushPre 0x1241e2 1) (pushR64Effect 0x1241e2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1241e2 1 3).toInstrSpec (push_r64_effect_step 0x1241e2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1241e3 [0x50] (PushPre 0x1241e3 1) (pushR64Effect 0x1241e3 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1241e3 1 0).toInstrSpec (push_r64_effect_step 0x1241e3 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1241e4 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1241e4) (movR64R64Effect 0x1241e4 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1241e4 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1241e4 0x48 0xfb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1241e7 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x1241e7) (testR64R64Effect 0x1241e7 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1241e7 2 2).toInstrSpec (test_r64_r64_effect_step 0x1241e7 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241e2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241e4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241e7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241ea) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x1241ea 4 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1241e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1241e0 :=
  Rest.liftedBlock (rest_l1241e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1241e0 x hx)

theorem rest_l1241ec [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1241ec bytes_l1241ec) (entryMap (live .l1241ec))
      2 0x1241ec bytes_l1241ec b_l1241ec := by
  have f0 : InstrSpec 0x1241ec [0x48, 0x83, 0xFA, 0x07] (fun s => s.RIP = 0x1241ec) (cmpR64Imm8Effect 0x1241ec 2 0x7)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1241ec 2 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x1241ec 0x48 0xfa 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241f0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x1241f0 7 0x45) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1241ec [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1241ec :=
  Rest.liftedBlock (rest_l1241ec code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1241ec x hx)

theorem rest_l1241f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1241f2 bytes_l1241f2) (entryMap (live .l1241f2))
      3 0x1241f2 bytes_l1241f2 b_l1241f2 := by
  have f0 : InstrSpec 0x1241f2 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1241f2 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1241f2 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1241f2 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1241f2 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1241f2 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1241fa [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1241fa) (movR64R64Effect 0x1241fa 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1241fa 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1241fa 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1241fd [0xFF, 0x15, 0xCD, 0xFB, 0x0D, 0x00] (GoesTo (CallMemPre 0x1241fd (.rip 0xdfbcd)) (callEffect (callMemPtr 0x1241fd (.rip 0xdfbcd)) (0x1241fd + BitVec.ofNat 64 (callMemLen (.rip 0xdfbcd)))) 0x12a820) (callEffect (callMemPtr 0x1241fd (.rip 0xdfbcd)) (0x1241fd + BitVec.ofNat 64 (callMemLen (.rip 0xdfbcd))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1241fd (.rip 0xdfbcd)).toInstrSpec (call_m64_effect_step 0x1241fd (.rip 0xdfbcd) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241fa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241fd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f2 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 58) (by decide) (by decide) rfl rfl

theorem block_l1241f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1241f2 :=
  Rest.liftedBlock (rest_l1241f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1241f2 x hx)

theorem rest_l124203 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124203 bytes_l124203) (entryMap (live .l124203))
      3 0x124203 bytes_l124203 b_l124203 := by
  have f0 : InstrSpec 0x124203 [0x4C, 0x8B, 0x34, 0x24] (LoadPre 0x124203 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124203 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124203 14 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x124203 14 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x124203 0x4c (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124207 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124207) (movR32Imm32Effect 0x124207 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x124207 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x124207 0xbe (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124207) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12420c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x12420c 0x3 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124203 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124203 :=
  Rest.liftedBlock (rest_l124203 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124203 x hx)

theorem rest_l12420e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12420e bytes_l12420e) (entryMap (live .l12420e))
      1 0x12420e bytes_l12420e b_l12420e := by
  have f0 : InstrSpec 0x12420e [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x12420e) (xorR32R32Effect 0x12420e 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12420e 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x12420e 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124211) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12420e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12420e :=
  Rest.liftedBlock (rest_l12420e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12420e x hx)

theorem rest_l124211 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124211 bytes_l124211) (entryMap (live .l124211))
      1 0x124211 bytes_l124211 b_l124211 := by
  have f0 : InstrSpec 0x124211 [0x31, 0xC9] (fun s => s.RIP = 0x124211) (xorR32R32Effect 0x124211 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x124211 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x124211 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124213) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l124211 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124211 :=
  Rest.liftedBlock (rest_l124211 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124211 x hx)

theorem rest_l124213 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124213 bytes_l124213) (entryMap (live .l124213))
      1 0x124213 bytes_l124213 b_l124213 := by
  have f0 : InstrSpec 0x124213 [0x31, 0xD2] (fun s => s.RIP = 0x124213) (xorR32R32Effect 0x124213 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x124213 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x124213 0xd2 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124215) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l124213 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124213 :=
  Rest.liftedBlock (rest_l124213 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124213 x hx)

theorem rest_l124215 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124215 bytes_l124215) (entryMap (live .l124215))
      10 0x124215 bytes_l124215 b_l124215 := by
  have f0 : InstrSpec 0x124215 [0x48, 0x89, 0x33] (StorePre 0x124215 3 (fun s => AddrMode.addr (.base 3 .none) s (0x124215 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x124215 6 (.base 3 .none))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124215 6 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x124215 0x48 (by decide) 6 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124218 [0x48, 0x89, 0x53, 0x08] (StorePre 0x124218 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124218 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124218 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124218 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x124218 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12421c [0x48, 0xC7, 0x43, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12421c 8 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12421c + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12421c (.base 3 (.d8 0x10)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12421c (.base 3 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12421c 0x48 (by decide) (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124224 [0x4C, 0x89, 0x73, 0x18] (StorePre 0x124224 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124224 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124224 14 (.base 3 (.d8 0x18)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124224 14 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x124224 0x4c (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124228 [0x48, 0x89, 0x4B, 0x20] (StorePre 0x124228 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x124228 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124228 1 (.base 3 (.d8 0x20)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124228 1 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x124228 0x48 (by decide) 1 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12422c [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x12422c) (movR64R64Effect 0x12422c 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12422c 0 3).toInstrSpec (mov_r64_r64_effect_step 0x12422c 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12422f [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x12422f) (addR64Imm8Effect 0x12422f 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12422f 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x12422f 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x124233 [0x5B] (PopPre 0x124233) (popR64Effect 0x124233 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124233 1 3).toInstrSpec (pop_r64_effect_step 0x124233 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x124234 [0x41, 0x5E] (PopPre 0x124234) (popR64Effect 0x124234 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124234 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124234 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x124236 [0xC3] (RetPre 0x124236) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x124236).toInstrSpec (ret_effect_step 0x124236) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124218) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12421c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124224) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124228) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12422c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12422f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124233) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124234) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124236) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 70) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f9 (by decide) rfl rfl rfl (by decide)

theorem block_l124215 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124215 :=
  Rest.liftedBlock (rest_l124215 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124215 x hx)

theorem rest_l124237 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124237 bytes_l124237) (entryMap (live .l124237))
      5 0x124237 bytes_l124237 b_l124237 := by
  have f0 : InstrSpec 0x124237 [0x48, 0x8D, 0x46, 0x08] (fun s => s.RIP = 0x124237) (leaR64Effect 0x124237 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x124237 0 (.base 6 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x124237 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12423b [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12423b) (movR64R64Effect 0x12423b 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12423b 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12423b 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12423e [0x4C, 0x8B, 0x36] (LoadPre 0x12423e (fun s => AddrMode.addr (.base 6 .none) s (0x12423e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12423e 14 (.base 6 .none))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x12423e 14 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12423e 0x4c (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124241 [0x48, 0x83, 0xC1, 0xF8] (fun s => s.RIP = 0x124241) (addR64Imm8Effect 0x124241 1 0xf8)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124241 1 0xf8).toInstrSpec (add_r64_imm8_effect_step 0x124241 0x48 0xc1 0xf8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12423b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12423e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124241) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124245) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x124245 4 0x28) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124237 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124237 :=
  Rest.liftedBlock (rest_l124237 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124237 x hx)

theorem rest_l124247 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124247 bytes_l124247) (entryMap (live .l124247))
      2 0x124247 bytes_l124247 b_l124247 := by
  have f0 : InstrSpec 0x124247 [0x48, 0x83, 0xFA, 0x0F] (fun s => s.RIP = 0x124247) (cmpR64Imm8Effect 0x124247 2 0xf)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x124247 2 0xf).toInstrSpec (cmp_r64_imm8_effect_step 0x124247 0x48 0xfa 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12424b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x12424b 7 0x2b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124247 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124247 :=
  Rest.liftedBlock (rest_l124247 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124247 x hx)

theorem rest_l12424d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12424d bytes_l12424d) (entryMap (live .l12424d))
      5 0x12424d bytes_l12424d b_l12424d := by
  have f0 : InstrSpec 0x12424d [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12424d 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12424d + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12424d (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12424d (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12424d 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124255 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x124255) (movR64R64Effect 0x124255 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124255 7 4).toInstrSpec (mov_r64_r64_effect_step 0x124255 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124258 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x124258) (movR64R64Effect 0x124258 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124258 6 0).toInstrSpec (mov_r64_r64_effect_step 0x124258 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12425b [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x12425b) (movR64R64Effect 0x12425b 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12425b 2 1).toInstrSpec (mov_r64_r64_effect_step 0x12425b 0x48 0xca (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12425e [0xFF, 0x15, 0x6C, 0xFB, 0x0D, 0x00] (GoesTo (CallMemPre 0x12425e (.rip 0xdfb6c)) (callEffect (callMemPtr 0x12425e (.rip 0xdfb6c)) (0x12425e + BitVec.ofNat 64 (callMemLen (.rip 0xdfb6c)))) 0x12a820) (callEffect (callMemPtr 0x12425e (.rip 0xdfb6c)) (0x12425e + BitVec.ofNat 64 (callMemLen (.rip 0xdfb6c))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12425e (.rip 0xdfb6c)).toInstrSpec (call_m64_effect_step 0x12425e (.rip 0xdfb6c) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124255) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124258) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12425b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12425e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l12424d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12424d :=
  Rest.liftedBlock (rest_l12424d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12424d x hx)

theorem rest_l124264 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124264 bytes_l124264) (entryMap (live .l124264))
      3 0x124264 bytes_l124264 b_l124264 := by
  have f0 : InstrSpec 0x124264 [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x124264 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124264 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124264 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124264 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x124264 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124268 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124268) (movR32Imm32Effect 0x124268 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x124268 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x124268 0xbe (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124268) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12426d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x12426d 0xa4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124264 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124264 :=
  Rest.liftedBlock (rest_l124264 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124264 x hx)

theorem rest_l12426f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12426f bytes_l12426f) (entryMap (live .l12426f))
      4 0x12426f bytes_l12426f b_l12426f := by
  have f0 : InstrSpec 0x12426f [0x31, 0xC9] (fun s => s.RIP = 0x12426f) (xorR32R32Effect 0x12426f 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12426f 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x12426f 0xc9 (by decide)) pre_rip
  have f1 : InstrSpec 0x124271 [0x31, 0xD2] (fun s => s.RIP = 0x124271) (xorR32R32Effect 0x124271 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x124271 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x124271 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x124273 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x124273) (movR64R64Effect 0x124273 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124273 6 0).toInstrSpec (mov_r64_r64_effect_step 0x124273 0x48 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124271) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124273) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124276) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x124276 0x9d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12426f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12426f :=
  Rest.liftedBlock (rest_l12426f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12426f x hx)

theorem rest_l124278 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124278 bytes_l124278) (entryMap (live .l124278))
      4 0x124278 bytes_l124278 b_l124278 := by
  have f0 : InstrSpec 0x124278 [0x48, 0x83, 0xC2, 0xF0] (fun s => s.RIP = 0x124278) (addR64Imm8Effect 0x124278 2 0xf0)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124278 2 0xf0).toInstrSpec (add_r64_imm8_effect_step 0x124278 0x48 0xc2 0xf0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12427c [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x12427c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12427c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12427c 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12427c 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12427c 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124280 [0x48, 0x83, 0xC6, 0x10] (fun s => s.RIP = 0x124280) (addR64Imm8Effect 0x124280 6 0x10)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124280 6 0x10).toInstrSpec (add_r64_imm8_effect_step 0x124280 0x48 0xc6 0x10 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12427c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124280) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124284) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x124284 0x8f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124278 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124278 :=
  Rest.liftedBlock (rest_l124278 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124278 x hx)

theorem rest_l124290 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124290 bytes_l124290) (entryMap (live .l124290))
      8 0x124290 bytes_l124290 b_l124290 := by
  have f0 : InstrSpec 0x124290 [0x55] (PushPre 0x124290 1) (pushR64Effect 0x124290 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124290 1 5).toInstrSpec (push_r64_effect_step 0x124290 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124291 [0x41, 0x56] (PushPre 0x124291 2) (pushR64Effect 0x124291 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124291 2 14).toInstrSpec (push_r64_rex_effect_step 0x124291 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124293 [0x53] (PushPre 0x124293 1) (pushR64Effect 0x124293 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124293 1 3).toInstrSpec (push_r64_effect_step 0x124293 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124294 [0x48, 0x83, 0xEC, 0x60] (fun s => s.RIP = 0x124294) (subR64Imm8Effect 0x124294 4 0x60)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x124294 4 0x60).toInstrSpec (sub_r64_imm8_effect_step 0x124294 0x48 0xec 0x60 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124298 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x124298) (movR64R64Effect 0x124298 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x124298 3 7).toInstrSpec (mov_r64_r64_effect_step 0x124298 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12429b [0x8B, 0x46, 0x18] (LoadPre 0x12429b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12429b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12429b 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12429b 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x12429b 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12429e [0x3B, 0x46, 0x1C] (LoadPre 0x12429e (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x12429e + BitVec.ofNat 64 3)) 4) (cmpR32M32Effect 0x12429e 3 0 (.base 6 (.d8 0x1c)))
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR32M32Effect_footprint 0x12429e 3 0 (.base 6 (.d8 0x1c))).toInstrSpec (cmp_r32_m32_effect_step 0x12429e 0 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124291) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124293) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124294) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124298) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12429b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12429e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242a1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x1242a1 6 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124290 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124290 :=
  Rest.liftedBlock (rest_l124290 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124290 x hx)

theorem rest_l1242a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1242a3 bytes_l1242a3) (entryMap (live .l1242a3))
      15 0x1242a3 bytes_l1242a3 b_l1242a3 := by
  have f0 : InstrSpec 0x1242a3 [0x89, 0xD5] (fun s => s.RIP = 0x1242a3) (movR32R32Effect 0x1242a3 2 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x1242a3 2 5 2).toInstrSpec (mov_r32_r32_effect_step 0x1242a3 0xd5 (by decide)) pre_rip
  have f1 : InstrSpec 0x1242a5 [0x41, 0x89, 0xCE] (fun s => s.RIP = 0x1242a5) (movR32R32Effect 0x1242a5 3 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x1242a5 3 14 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1242a5 0x41 0xce (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1242a8 [0x48, 0x8B, 0x06] (LoadPre 0x1242a8 (fun s => AddrMode.addr (.base 6 .none) s (0x1242a8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1242a8 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1242a8 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1242a8 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1242ab [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x1242ab (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1242ab + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242ab 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1242ab 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1242ab 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1242af [0x0F, 0xB6, 0x56, 0x20] (LoadPre 0x1242af (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1242af + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1242af 4 2 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1242af 4 2 (.base 6 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x1242af 2 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1242b3 [0x48, 0x8B, 0x7E, 0x18] (LoadPre 0x1242b3 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1242b3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242b3 7 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1242b3 7 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1242b3 0x48 (by decide) 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1242b7 [0x48, 0x89, 0x7C, 0x24, 0x50] (StorePre 0x1242b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1242b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242b7 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1242b7 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1242b7 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1242bc [0x48, 0x8B, 0x76, 0x10] (LoadPre 0x1242bc (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1242bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242bc 6 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1242bc 6 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1242bc 0x48 (by decide) 6 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1242c0 [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x1242c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1242c0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242c0 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1242c0 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1242c0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1242c5 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x1242c5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1242c5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242c5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1242c5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1242c5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1242ca [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x1242ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1242ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242ca 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1242ca 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1242ca 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1242cf [0x88, 0x54, 0x24, 0x58] (StorePre 0x1242cf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1242cf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1242cf 4 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1242cf 4 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m8_r8_effect_step 0x1242cf 2 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1242d3 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1242d3) (movR64R64Effect 0x1242d3 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1242d3 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1242d3 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1242d6 [0x48, 0x8D, 0x74, 0x24, 0x38] (fun s => s.RIP = 0x1242d6) (leaR64Effect 0x1242d6 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1242d6 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x1242d6 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1242db [0xE8, 0x50, 0x01, 0x00, 0x00] (PushPre 0x1242db 5) (callEffect (fun _ => 0x124430) 0x1242e0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1242db 0x124430 0x1242e0).toInstrSpec (call_rel32_effect_step 0x1242db 0x150 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242a8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242af) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242b3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242b7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242bc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242c0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242c5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242ca) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242cf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242d3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242d6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242db) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 76), (5, 53), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124430) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 78) (by decide) (by decide) rfl rfl

theorem block_l1242a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1242a3 :=
  Rest.liftedBlock (rest_l1242a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1242a3 x hx)

theorem rest_l1242e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1242e0 bytes_l1242e0) (entryMap (live .l1242e0))
      4 0x1242e0 bytes_l1242e0 b_l1242e0 := by
  have f0 : InstrSpec 0x1242e0 [0x8B, 0x0C, 0x24] (LoadPre 0x1242e0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1242e0 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1242e0 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1242e0 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x1242e0 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1242e3 [0x48, 0x8B, 0x44, 0x24, 0x04] (LoadPre 0x1242e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1242e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1242e3 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1242e3 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r64_m64_effect_step 0x1242e3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1242e8 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x1242e8) (cmpR32Imm8Effect 0x1242e8 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1242e8 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1242e8 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242e8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242eb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1242eb 5 0x3e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1242e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1242e0 :=
  Rest.liftedBlock (rest_l1242e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1242e0 x hx)

theorem rest_l1242ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1242ed bytes_l1242ed) (entryMap (live .l1242ed))
      10 0x1242ed bytes_l1242ed b_l1242ed := by
  have f0 : InstrSpec 0x1242ed [0x8D, 0x50, 0xEA] (fun s => s.RIP = 0x1242ed) (leaR32Effect 0x1242ed 3 2 (.base 0 (.d8 0xea)))
      [.gpr 0] [] [.reg 2, .rip] :=
    (leaR32Effect_footprint 0x1242ed 3 2 (.base 0 (.d8 0xea))).toInstrSpec (lea_r32_effect_step 0x1242ed 2 (.base 0 (.d8 0xea)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1242f0 [0x89, 0xD6] (fun s => s.RIP = 0x1242f0) (movR32R32Effect 0x1242f0 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1242f0 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x1242f0 0xd6 (by decide)) pre_rip
  have f2 : InstrSpec 0x1242f2 [0x40, 0xC0, 0xE6, 0x06] (fun s => s.RIP = 0x1242f2) (shlR8Effect 0x1242f2 4 6 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR8Effect_footprint 0x1242f2 4 6 6).toInstrSpec (shl_r8_imm8_rex_effect_step 0x1242f2 0x40 0xe6 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1242f6 [0x40, 0x80, 0xC6, 0x40] (fun s => s.RIP = 0x1242f6) (addR8Imm8Effect 0x1242f6 4 6 0x40)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR8Imm8Effect_footprint 0x1242f6 4 6 0x40).toInstrSpec (add_r8_imm8_rex_effect_step 0x1242f6 0x40 0xc6 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1242fa [0x31, 0xC9] (fun s => s.RIP = 0x1242fa) (xorR32R32Effect 0x1242fa 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1242fa 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1242fa 0xc9 (by decide)) pre_rip
  have f5 : InstrSpec 0x1242fc [0x80, 0xFA, 0x03] (fun s => s.RIP = 0x1242fc) (cmpR8Imm8Effect 0x1242fc 3 2 0x3)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1242fc 3 2 0x3).toInstrSpec (cmp_r8_imm8_effect_step 0x1242fc 0xfa 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1242ff [0x40, 0x0F, 0xB6, 0xD6] (fun s => s.RIP = 0x1242ff) (movzxR32R8Effect 0x1242ff 4 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1242ff 4 2 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1242ff 0x40 (by decide) 0xd6 (by decide)) pre_rip
  have f7 : InstrSpec 0x124303 [0x0F, 0x43, 0xD1] (fun s => s.RIP = 0x124303) (atFlags (condHolds 3) (cmovR32R32Effect 0x124303 3 2 1))
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (cmovR32R32Effect_footprint 0x124303 3 2 1 3).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x124303 3 0xd1 (by decide) c)) pre_rip
  have f8 : InstrSpec 0x124306 [0x40, 0x38, 0xEA] (fun s => s.RIP = 0x124306) (cmpR8R8Effect 0x124306 3 2 5)
      [.gpr 2, .gpr 5] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x124306 3 2 5).toInstrSpec (cmp_r8_r8_rex_effect_step 0x124306 0x40 0xea (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242f0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242f2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242f6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242fc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242ff) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124303) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124306) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124309) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel32_effect_step 0x124309 5 0x102) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1242ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1242ed :=
  Rest.liftedBlock (rest_l1242ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1242ed x hx)

theorem rest_l12430f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12430f bytes_l12430f) (entryMap (live .l12430f))
      1 0x12430f bytes_l12430f b_l12430f := by
  have f0 : InstrSpec 0x12430f [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x12430f) (movzxR32R8Effect 0x12430f 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x12430f 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x12430f 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0)]) (p' := 0x124312) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12430f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12430f :=
  Rest.liftedBlock (rest_l12430f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12430f x hx)

theorem rest_l124322 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124322 bytes_l124322) (entryMap (live .l124322))
      2 0x124322 bytes_l124322 b_l124322 := by
  have f0 : InstrSpec 0x124322 [0xC6, 0x43, 0x04, 0x00] (StorePre 0x124322 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124322 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124322 (.base 3 (.d8 0x4)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124322 (.base 3 (.d8 0x4)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x124322 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124326) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel32_effect_step 0x124326 0xe9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124322 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124322 :=
  Rest.liftedBlock (rest_l124322 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124322 x hx)

theorem rest_l12432b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12432b bytes_l12432b) (entryMap (live .l12432b))
      15 0x12432b bytes_l12432b b_l12432b := by
  have f0 : InstrSpec 0x12432b [0x8B, 0x54, 0x24, 0x34] (LoadPre 0x12432b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12432b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12432b 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x12432b 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x12432b 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12432f [0x89, 0x53, 0x34] (StorePre 0x12432f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x12432f + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12432f 2 (.base 3 (.d8 0x34)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12432f 2 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x12432f 2 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x124332 [0x48, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x124332 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124332 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124332 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124332 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x124332 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124337 [0x48, 0x89, 0x53, 0x2C] (StorePre 0x124337 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124337 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124337 2 (.base 3 (.d8 0x2c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124337 2 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x124337 0x48 (by decide) 2 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12433b [0x48, 0x8B, 0x54, 0x24, 0x24] (LoadPre 0x12433b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12433b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12433b 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12433b 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x12433b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124340 [0x48, 0x89, 0x53, 0x24] (StorePre 0x124340 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124340 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124340 2 (.base 3 (.d8 0x24)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124340 2 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x124340 0x48 (by decide) 2 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124344 [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x124344 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124344 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124344 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124344 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x124344 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124349 [0x48, 0x89, 0x53, 0x1C] (StorePre 0x124349 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124349 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124349 2 (.base 3 (.d8 0x1c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124349 2 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x124349 0x48 (by decide) 2 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12434d [0x48, 0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x12434d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x12434d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12434d 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12434d 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x12434d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x124352 [0x48, 0x8B, 0x74, 0x24, 0x14] (LoadPre 0x124352 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124352 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124352 6 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124352 6 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x124352 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x124357 [0x48, 0x89, 0x73, 0x14] (StorePre 0x124357 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124357 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124357 6 (.base 3 (.d8 0x14)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124357 6 (.base 3 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x124357 0x48 (by decide) 6 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x12435b [0x48, 0x89, 0x53, 0x0C] (StorePre 0x12435b 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12435b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12435b 2 (.base 3 (.d8 0xc)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12435b 2 (.base 3 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x12435b 0x48 (by decide) 2 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12435f [0x89, 0x0B] (StorePre 0x12435f 2 (fun s => AddrMode.addr (.base 3 .none) s (0x12435f + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x12435f 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12435f 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x12435f 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124361 [0x48, 0x89, 0x43, 0x04] (StorePre 0x124361 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124361 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124361 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124361 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x124361 0x48 (by decide) 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12432f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124332) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124337) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12433b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124340) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124344) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124349) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12434d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124352) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124357) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12435b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12435f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124361) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124365) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 73) (jmp_rel32_effect_step 0x124365 0xb0 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12432b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12432b :=
  Rest.liftedBlock (rest_l12432b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12432b x hx)

theorem rest_l124411 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124411 bytes_l124411) (entryMap (live .l124411))
      1 0x124411 bytes_l124411 b_l124411 := by
  have f0 : InstrSpec 0x124411 [0x88, 0x4B, 0x04] (StorePre 0x124411 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124411 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124411 3 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x124411 3 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x124411 1 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124414) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l124411 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124411 :=
  Rest.liftedBlock (rest_l124411 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124411 x hx)

theorem rest_l124414 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124414 bytes_l124414) (entryMap (live .l124414))
      1 0x124414 bytes_l124414 b_l124414 := by
  have f0 : InstrSpec 0x124414 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x124414 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124414 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124414 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124414 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x124414 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12441a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l124414 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124414 :=
  Rest.liftedBlock (rest_l124414 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124414 x hx)

theorem rest_l12441a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12441a bytes_l12441a) (entryMap (live .l12441a))
      6 0x12441a bytes_l12441a b_l12441a := by
  have f0 : InstrSpec 0x12441a [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x12441a) (movR64R64Effect 0x12441a 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12441a 0 3).toInstrSpec (mov_r64_r64_effect_step 0x12441a 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12441d [0x48, 0x83, 0xC4, 0x60] (fun s => s.RIP = 0x12441d) (addR64Imm8Effect 0x12441d 4 0x60)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12441d 4 0x60).toInstrSpec (add_r64_imm8_effect_step 0x12441d 0x48 0xc4 0x60 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124421 [0x5B] (PopPre 0x124421) (popR64Effect 0x124421 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124421 1 3).toInstrSpec (pop_r64_effect_step 0x124421 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124422 [0x41, 0x5E] (PopPre 0x124422) (popR64Effect 0x124422 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124422 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124422 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124424 [0x5D] (PopPre 0x124424) (popR64Effect 0x124424 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124424 1 5).toInstrSpec (pop_r64_effect_step 0x124424 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x124425 [0xC3] (RetPre 0x124425) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x124425).toInstrSpec (ret_effect_step 0x124425) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12441d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124421) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124422) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124424) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124425) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l12441a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12441a :=
  Rest.liftedBlock (rest_l12441a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12441a x hx)

theorem rest_l124ae0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124ae0 bytes_l124ae0) (entryMap (live .l124ae0))
      7 0x124ae0 bytes_l124ae0 b_l124ae0 := by
  have f0 : InstrSpec 0x124ae0 [0x41, 0x56] (PushPre 0x124ae0 2) (pushR64Effect 0x124ae0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124ae0 2 14).toInstrSpec (push_r64_rex_effect_step 0x124ae0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124ae2 [0x53] (PushPre 0x124ae2 1) (pushR64Effect 0x124ae2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124ae2 1 3).toInstrSpec (push_r64_effect_step 0x124ae2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124ae3 [0x48, 0x83, 0xEC, 0x58] (fun s => s.RIP = 0x124ae3) (subR64Imm8Effect 0x124ae3 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x124ae3 4 0x58).toInstrSpec (sub_r64_imm8_effect_step 0x124ae3 0x48 0xec 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124ae7 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x124ae7) (movR64R64Effect 0x124ae7 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x124ae7 14 6).toInstrSpec (mov_r64_r64_effect_step 0x124ae7 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124aea [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x124aea) (movR64R64Effect 0x124aea 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x124aea 3 7).toInstrSpec (mov_r64_r64_effect_step 0x124aea 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x124aed [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x124aed) (leaR64Effect 0x124aed 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124aed 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x124aed 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x124af2 [0xE8, 0x59, 0x09, 0x00, 0x00] (PushPre 0x124af2 5) (callEffect (fun _ => 0x125450) 0x124af7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124af2 0x125450 0x124af7).toInstrSpec (call_rel32_effect_step 0x124af2 0x959 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ae2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ae3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ae7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aea) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aed) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124af2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 61), (4, 65), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125450) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l124ae0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124ae0 :=
  Rest.liftedBlock (rest_l124ae0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124ae0 x hx)

theorem rest_l124af7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124af7 bytes_l124af7) (entryMap (live .l124af7))
      7 0x124af7 bytes_l124af7 b_l124af7 := by
  have f0 : InstrSpec 0x124af7 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x124af7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124af7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124af7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124af7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x124af7 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124afb [0x48, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x124afb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124afb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124afb 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124afb 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x124afb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124b00 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x124b00 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b00 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b00 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b00 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x124b00 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124b04 [0x48, 0x8B, 0x4C, 0x24, 0x1C] (LoadPre 0x124b04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124b04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b04 1 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b04 1 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x124b04 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124b09 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x124b09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b09 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b09 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x124b09 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124b0e [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124b0e) (cmpR32Imm8Effect 0x124b0e 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124b0e 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124b0e 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124afb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b00) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b04) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b09) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b0e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b11) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x124b11 5 0x3d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124af7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124af7 :=
  Rest.liftedBlock (rest_l124af7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124af7 x hx)

theorem rest_l124b13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b13 bytes_l124b13) (entryMap (live .l124b13))
      7 0x124b13 bytes_l124b13 b_l124b13 := by
  have f0 : InstrSpec 0x124b13 [0x48, 0x8B, 0x34, 0x24] (LoadPre 0x124b13 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b13 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124b13 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124b13 6 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x124b13 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124b17 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x124b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b17 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x124b17 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x124b17 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124b1c [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x124b1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124b1c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b1c 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b1c 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x124b1c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124b21 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x124b21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124b21 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b21 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b21 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x124b21 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124b26 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x124b26) (leaR64Effect 0x124b26 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124b26 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x124b26 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x124b2b [0xBA, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124b2b) (movR32Imm32Effect 0x124b2b 5 2 0x5)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x124b2b 5 2 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x124b2b 0xba (by decide) 0x5) pre_rip
  have f6 : InstrSpec 0x124b30 [0xE8, 0x9B, 0x2B, 0x00, 0x00] (PushPre 0x124b30 5) (callEffect (fun _ => 0x1276d0) 0x124b35)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124b30 0x1276d0 0x124b35).toInstrSpec (call_rel32_effect_step 0x124b30 0x2b9b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b1c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b21) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b26) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b2b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b30) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l124b13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b13 :=
  Rest.liftedBlock (rest_l124b13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b13 x hx)

theorem rest_l124b35 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b35 bytes_l124b35) (entryMap (live .l124b35))
      3 0x124b35 bytes_l124b35 b_l124b35 := by
  have f0 : InstrSpec 0x124b35 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x124b35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124b35 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b35 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124b35 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x124b35 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124b39 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124b39) (cmpR32Imm8Effect 0x124b39 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124b39 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124b39 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b39) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b3c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x124b3c 5 0x52) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124b35 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b35 :=
  Rest.liftedBlock (rest_l124b35 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b35 x hx)

theorem rest_l124b3e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b3e bytes_l124b3e) (entryMap (live .l124b3e))
      4 0x124b3e bytes_l124b3e b_l124b3e := by
  have f0 : InstrSpec 0x124b3e [0x48, 0x8D, 0x54, 0x24, 0x48] (fun s => s.RIP = 0x124b3e) (leaR64Effect 0x124b3e 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x124b3e 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x124b3e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124b43 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x124b43) (movR64R64Effect 0x124b43 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124b43 7 3).toInstrSpec (mov_r64_r64_effect_step 0x124b43 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124b46 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x124b46) (movR64R64Effect 0x124b46 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124b46 6 14).toInstrSpec (mov_r64_r64_effect_step 0x124b46 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124b49 [0xE8, 0x72, 0x1C, 0x00, 0x00] (PushPre 0x124b49 5) (callEffect (fun _ => 0x1267c0) 0x124b4e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124b49 0x1267c0 0x124b4e).toInstrSpec (call_rel32_effect_step 0x124b49 0x1c72 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b43) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b46) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b49) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267c0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124b3e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b3e :=
  Rest.liftedBlock (rest_l124b3e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b3e x hx)

theorem rest_l124b4e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b4e bytes_l124b4e) (entryMap (live .l124b4e))
      1 0x124b4e bytes_l124b4e b_l124b4e := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x124b4e 0x7f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124b4e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b4e :=
  Rest.liftedBlock (rest_l124b4e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b4e x hx)

theorem rest_l124b50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b50 bytes_l124b50) (entryMap (live .l124b50))
      16 0x124b50 bytes_l124b50 b_l124b50 := by
  have f0 : InstrSpec 0x124b50 [0x8B, 0x4C, 0x24, 0x44] (LoadPre 0x124b50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x124b50 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b50 1 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x124b50 1 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x124b50 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124b54 [0x89, 0x4B, 0x34] (StorePre 0x124b54 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124b54 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124b54 1 (.base 3 (.d8 0x34)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124b54 1 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x124b54 1 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x124b57 [0x48, 0x8B, 0x4C, 0x24, 0x3C] (LoadPre 0x124b57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124b57 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b57 1 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b57 1 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r64_m64_effect_step 0x124b57 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124b5c [0x48, 0x89, 0x4B, 0x2C] (StorePre 0x124b5c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124b5c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b5c 1 (.base 3 (.d8 0x2c)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b5c 1 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x124b5c 0x48 (by decide) 1 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124b60 [0x48, 0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x124b60 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124b60 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b60 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b60 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x124b60 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124b65 [0x48, 0x89, 0x4B, 0x24] (StorePre 0x124b65 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124b65 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b65 1 (.base 3 (.d8 0x24)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b65 1 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x124b65 0x48 (by decide) 1 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124b69 [0x48, 0x8B, 0x4C, 0x24, 0x24] (LoadPre 0x124b69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124b69 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b69 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b69 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x124b69 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124b6e [0x48, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x124b6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124b6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b6e 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124b6e 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x124b6e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x124b73 [0x48, 0x89, 0x53, 0x1C] (StorePre 0x124b73 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124b73 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b73 2 (.base 3 (.d8 0x1c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b73 2 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x124b73 0x48 (by decide) 2 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x124b77 [0x48, 0x89, 0x4B, 0x14] (StorePre 0x124b77 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124b77 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b77 1 (.base 3 (.d8 0x14)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b77 1 (.base 3 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x124b77 0x48 (by decide) 1 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x124b7b [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x124b7b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b7b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124b7b 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b7b 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x124b7b 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x124b7f [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x124b7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b7f 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124b7f 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x124b7f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x124b84 [0x48, 0x89, 0x53, 0x0C] (StorePre 0x124b84 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124b84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b84 2 (.base 3 (.d8 0xc)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b84 2 (.base 3 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x124b84 0x48 (by decide) 2 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124b88 [0x48, 0x89, 0x4B, 0x04] (StorePre 0x124b88 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124b88 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b88 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b88 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x124b88 0x48 (by decide) 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x124b8c [0x89, 0x03] (StorePre 0x124b8c 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124b8c + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124b8c 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124b8c 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x124b8c 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b57) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b60) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b65) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b69) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b6e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b73) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b77) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b7b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b7f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b84) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b88) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b8c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b8e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 75) (jmp_rel8_effect_step 0x124b8e 0x3f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124b50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b50 :=
  Rest.liftedBlock (rest_l124b50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b50 x hx)

theorem rest_l124b90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b90 bytes_l124b90) (entryMap (live .l124b90))
      15 0x124b90 bytes_l124b90 b_l124b90 := by
  have f0 : InstrSpec 0x124b90 [0x48, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x124b90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124b90 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b90 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b90 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x124b90 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124b95 [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x124b95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124b95 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b95 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124b95 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x124b95 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124b9a [0x8B, 0x74, 0x24, 0x44] (LoadPre 0x124b9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x124b9a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b9a 6 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x124b9a 6 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x124b9a 6 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124b9e [0x89, 0x73, 0x34] (StorePre 0x124b9e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124b9e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124b9e 6 (.base 3 (.d8 0x34)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124b9e 6 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x124b9e 6 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124ba1 [0x48, 0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x124ba1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124ba1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ba1 6 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124ba1 6 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r64_m64_effect_step 0x124ba1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124ba6 [0x48, 0x89, 0x73, 0x2C] (StorePre 0x124ba6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124ba6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ba6 6 (.base 3 (.d8 0x2c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124ba6 6 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x124ba6 0x48 (by decide) 6 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124baa [0x48, 0x8B, 0x74, 0x24, 0x34] (LoadPre 0x124baa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124baa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124baa 6 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124baa 6 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x124baa 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124baf [0x48, 0x89, 0x73, 0x24] (StorePre 0x124baf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124baf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124baf 6 (.base 3 (.d8 0x24)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124baf 6 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x124baf 0x48 (by decide) 6 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x124bb3 [0x48, 0x8B, 0x74, 0x24, 0x2C] (LoadPre 0x124bb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124bb3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124bb3 6 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124bb3 6 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x124bb3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x124bb8 [0x48, 0x89, 0x73, 0x1C] (StorePre 0x124bb8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124bb8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bb8 6 (.base 3 (.d8 0x1c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124bb8 6 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x124bb8 0x48 (by decide) 6 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x124bbc [0x48, 0x8B, 0x74, 0x24, 0x24] (LoadPre 0x124bbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124bbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124bbc 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124bbc 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x124bbc 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x124bc1 [0x48, 0x89, 0x73, 0x14] (StorePre 0x124bc1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124bc1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bc1 6 (.base 3 (.d8 0x14)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124bc1 6 (.base 3 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x124bc1 0x48 (by decide) 6 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x124bc5 [0x48, 0x89, 0x53, 0x0C] (StorePre 0x124bc5 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124bc5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bc5 2 (.base 3 (.d8 0xc)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124bc5 2 (.base 3 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x124bc5 0x48 (by decide) 2 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124bc9 [0x89, 0x03] (StorePre 0x124bc9 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124bc9 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124bc9 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124bc9 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x124bc9 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x124bcb [0x48, 0x89, 0x4B, 0x04] (StorePre 0x124bcb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124bcb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bcb 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124bcb 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x124bcb 0x48 (by decide) 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b95) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b9a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b9e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ba1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 60), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ba6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 60), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124baa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124baf) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bb3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bb8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bbc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bc1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bc5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bc9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bcb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bcf) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 75) (by decide) rfl

theorem block_l124b90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b90 :=
  Rest.liftedBlock (rest_l124b90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b90 x hx)

theorem rest_l124bcf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124bcf bytes_l124bcf) (entryMap (live .l124bcf))
      5 0x124bcf bytes_l124bcf b_l124bcf := by
  have f0 : InstrSpec 0x124bcf [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x124bcf) (movR64R64Effect 0x124bcf 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x124bcf 0 3).toInstrSpec (mov_r64_r64_effect_step 0x124bcf 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124bd2 [0x48, 0x83, 0xC4, 0x58] (fun s => s.RIP = 0x124bd2) (addR64Imm8Effect 0x124bd2 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124bd2 4 0x58).toInstrSpec (add_r64_imm8_effect_step 0x124bd2 0x48 0xc4 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124bd6 [0x5B] (PopPre 0x124bd6) (popR64Effect 0x124bd6 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124bd6 1 3).toInstrSpec (pop_r64_effect_step 0x124bd6 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124bd7 [0x41, 0x5E] (PopPre 0x124bd7) (popR64Effect 0x124bd7 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124bd7 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124bd7 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124bd9 [0xC3] (RetPre 0x124bd9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x124bd9).toInstrSpec (ret_effect_step 0x124bd9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bd6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bd7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bd9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l124bcf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124bcf :=
  Rest.liftedBlock (rest_l124bcf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124bcf x hx)

theorem rest_l125760 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125760 bytes_l125760) (entryMap (live .l125760))
      2 0x125760 bytes_l125760 b_l125760 := by
  have f0 : InstrSpec 0x125760 [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x125760) (testR64R64Effect 0x125760 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x125760 6 6).toInstrSpec (test_r64_r64_effect_step 0x125760 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125763) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x125763 4 0xa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125760 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125760 :=
  Rest.liftedBlock (rest_l125760 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125760 x hx)

theorem rest_l125765 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125765 bytes_l125765) (entryMap (live .l125765))
      4 0x125765 bytes_l125765 b_l125765 := by
  have f0 : InstrSpec 0x125765 [0x0F, 0xB6, 0x44, 0x37, 0xFF] (LoadPre 0x125765 (fun s => AddrMode.addr (.sib 7 (some 6) 0 (.d8 0xff)) s (0x125765 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125765 5 0 (.sib 7 (some 6) 0 (.d8 0xff)))
      [.gpr 7, .gpr 6] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x125765 5 0 (.sib 7 (some 6) 0 (.d8 0xff))).toInstrSpec (movzx_r32_m8_effect_step 0x125765 0 (.sib 7 (some 6) 0 (.d8 0xff)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12576a [0x24, 0x01] (fun s => s.RIP = 0x12576a) (andAlImm8Effect 0x12576a 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x12576a 0x1).toInstrSpec (and_al_imm8_effect_step 0x12576a 0x1) pre_rip
  have f2 : InstrSpec 0x12576c [0x0C, 0x02] (fun s => s.RIP = 0x12576c) (orAlImm8Effect 0x12576c 0x2)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orAlImm8Effect_footprint 0x12576c 0x2).toInstrSpec (or_al_imm8_effect_step 0x12576c 0x2) pre_rip
  have f3 : InstrSpec 0x12576e [0xC3] (RetPre 0x12576e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12576e).toInstrSpec (ret_effect_step 0x12576e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12576a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12576c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12576e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l125765 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125765 :=
  Rest.liftedBlock (rest_l125765 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125765 x hx)

theorem rest_l12576f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12576f bytes_l12576f) (entryMap (live .l12576f))
      5 0x12576f bytes_l12576f b_l12576f := by
  have f0 : InstrSpec 0x12576f [0x50] (PushPre 0x12576f 1) (pushR64Effect 0x12576f 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12576f 1 0).toInstrSpec (push_r64_effect_step 0x12576f 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x125770 [0xBE, 0x12, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125770) (movR32Imm32Effect 0x125770 5 6 0x12)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x125770 5 6 0x12).toInstrSpec (mov_r32_imm32_effect_step 0x125770 0xbe (by decide) 0x12) pre_rip
  have f2 : InstrSpec 0x125775 [0x48, 0xC7, 0xC7, 0xB0, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x125775) (movR64Imm32Effect 0x125775 7 0x2036b0)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x125775 7 0x2036b0).toInstrSpec (mov_r64_imm32_effect_step 0x125775 0x48 0xc7 (by decide) (by decide) (by decide) 0x2036b0) pre_rip
  have f3 : InstrSpec 0x12577c [0x48, 0xC7, 0xC2, 0xC8, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x12577c) (movR64Imm32Effect 0x12577c 2 0x2036c8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x12577c 2 0x2036c8).toInstrSpec (mov_r64_imm32_effect_step 0x12577c 0x48 0xc2 (by decide) (by decide) (by decide) 0x2036c8) pre_rip
  have f4 : InstrSpec 0x125783 [0xE8, 0xD8, 0x3D, 0x00, 0x00] (PushPre 0x125783 5) (callEffect (fun _ => 0x129560) 0x125788)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125783 0x129560 0x125788).toInstrSpec (call_rel32_effect_step 0x125783 0x3dd8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 53), (5, 5)]) (p' := 0x125770) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (4, 53), (5, 5), (6, 55)]) (p' := 0x125775) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (4, 53), (5, 5), (6, 55), (7, 57)]) (p' := 0x12577c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (4, 53), (5, 5), (6, 55), (7, 57)]) (p' := 0x125783) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (4, 61), (5, 5), (6, 55), (7, 57)]) (p' := 0x129560) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l12576f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12576f :=
  Rest.liftedBlock (rest_l12576f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12576f x hx)

theorem rest_l125788 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125788 bytes_l125788) (entryMap (live .l125788))
      1 0x125788 bytes_l125788 b_l125788 := by
  have f0 : InstrSpec 0x125788 [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125788) (fun _ => nopEffect 0x125788 8)
      [] [] [.rip] :=
    (nopEffect_footprint 0x125788 8).toInstrSpec (nop_m_effect_step 0x125788 [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125790) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l125788 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125788 :=
  Rest.liftedBlock (rest_l125788 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125788 x hx)

theorem rest_l1275f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1275f0 bytes_l1275f0) (entryMap (live .l1275f0))
      4 0x1275f0 bytes_l1275f0 b_l1275f0 := by
  have f0 : InstrSpec 0x1275f0 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x1275f0) (movR64R64Effect 0x1275f0 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1275f0 0 7).toInstrSpec (mov_r64_r64_effect_step 0x1275f0 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1275f3 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x1275f3 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1275f3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1275f3 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1275f3 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1275f3 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1275f7 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x1275f7) (testR64R64Effect 0x1275f7 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1275f7 1 1).toInstrSpec (test_r64_r64_effect_step 0x1275f7 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275f7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275fa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1275fa 4 0x40) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1275f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1275f0 :=
  Rest.liftedBlock (rest_l1275f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1275f0 x hx)

theorem rest_l1275fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1275fc bytes_l1275fc) (entryMap (live .l1275fc))
      4 0x1275fc bytes_l1275fc b_l1275fc := by
  have f0 : InstrSpec 0x1275fc [0x48, 0x8B, 0x3E] (LoadPre 0x1275fc (fun s => AddrMode.addr (.base 6 .none) s (0x1275fc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1275fc 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1275fc 7 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1275fc 0x48 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1275ff [0x4C, 0x8D, 0x41, 0xFF] (fun s => s.RIP = 0x1275ff) (leaR64Effect 0x1275ff 8 (.base 1 (.d8 0xff)))
      [.gpr 1] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1275ff 8 (.base 1 (.d8 0xff))).toInstrSpec (lea_r64_effect_step 0x1275ff 0x4c (by decide) 0 (.base 1 (.d8 0xff)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127603 [0x31, 0xD2] (fun s => s.RIP = 0x127603) (xorR32R32Effect 0x127603 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127603 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x127603 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x127605 [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127605) (fun _ => nopEffect 0x127605 11)
      [] [] [.rip] :=
    (nopEffect_footprint 0x127605 11).toInstrSpec (nop_m_effect_step 0x127605 [0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1275ff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127603) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127605) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127610) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l1275fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1275fc :=
  Rest.liftedBlock (rest_l1275fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1275fc x hx)

theorem rest_l127610 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127610 bytes_l127610) (entryMap (live .l127610))
      4 0x127610 bytes_l127610 b_l127610 := by
  have f0 : InstrSpec 0x127610 [0x0F, 0xB6, 0x34, 0x17] (LoadPre 0x127610 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x127610 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x127610 4 6 (.sib 7 (some 2) 0 .none))
      [.gpr 7, .gpr 2] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x127610 4 6 (.sib 7 (some 2) 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x127610 6 (.sib 7 (some 2) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127614 [0x49, 0x39, 0xD0] (fun s => s.RIP = 0x127614) (cmpR64R64Effect 0x127614 8 2)
      [.gpr 8, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127614 8 2).toInstrSpec (cmp_r64_r64_effect_step 0x127614 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127617 [0x48, 0x8D, 0x52, 0x01] (fun s => s.RIP = 0x127617) (leaR64Effect 0x127617 2 (.base 2 (.d8 0x1)))
      [.gpr 2] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x127617 2 (.base 2 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x127617 0x48 (by decide) 2 (.base 2 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127614) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127617) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12761b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12761b 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127610 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127610 :=
  Rest.liftedBlock (rest_l127610 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127610 x hx)

theorem rest_l12761d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12761d bytes_l12761d) (entryMap (live .l12761d))
      2 0x12761d bytes_l12761d b_l12761d := by
  have f0 : InstrSpec 0x12761d [0x40, 0x84, 0xF6] (fun s => s.RIP = 0x12761d) (testR8R8Effect 0x12761d 3 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x12761d 3 6 6).toInstrSpec (test_r8_r8_rex_effect_step 0x12761d 0x40 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127620) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127620 4 0xee) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12761d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12761d :=
  Rest.liftedBlock (rest_l12761d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12761d x hx)

theorem rest_l127622 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127622 bytes_l127622) (entryMap (live .l127622))
      5 0x127622 bytes_l127622 b_l127622 := by
  have f0 : InstrSpec 0x127622 [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x127622) (movR64R64Effect 0x127622 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x127622 7 1).toInstrSpec (mov_r64_r64_effect_step 0x127622 0x48 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127625 [0x48, 0x29, 0xD7] (fun s => s.RIP = 0x127625) (subR64R64Effect 0x127625 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (subR64R64Effect_footprint 0x127625 7 2).toInstrSpec (sub_r64_r64_effect_step 0x127625 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127628 [0x48, 0xFF, 0xC7] (fun s => s.RIP = 0x127628) (incR64Effect 0x127628 7)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (incR64Effect_footprint 0x127628 7).toInstrSpec (inc_r64_effect_step 0x127628 0x48 0xc7 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12762b [0x48, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x12762b) (shrR64Effect 0x12762b 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x12762b 4 7 32).toInstrSpec (shr_r64_imm8_effect_step 0x12762b 0x48 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127625) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127628) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12762b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 60) f3 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x12762b 4 7 32 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12762f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x12762f 4 0x17) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127622 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127622 :=
  Rest.liftedBlock (rest_l127622 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127622 x hx)

theorem rest_l127631 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127631 bytes_l127631) (entryMap (live .l127631))
      3 0x127631 bytes_l127631 b_l127631 := by
  have f0 : InstrSpec 0x127631 [0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x127631 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127631 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127631 6 (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127631 6 (.base 0 .none) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x127631 (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127637 [0xC6, 0x40, 0x08, 0x0C] (StorePre 0x127637 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127637 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127637 (.base 0 (.d8 0x8)) 0xc)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127637 (.base 0 (.d8 0x8)) 0xc).toInstrSpec (mov_m8_imm8_effect_step 0x127637 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0xc) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12763b [0xC3] (RetPre 0x12763b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12763b).toInstrSpec (ret_effect_step 0x12763b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127637) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12763b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l127631 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127631 :=
  Rest.liftedBlock (rest_l127631 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127631 x hx)

theorem rest_l12763c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12763c bytes_l12763c) (entryMap (live .l12763c))
      4 0x12763c bytes_l12763c b_l12763c := by
  have f0 : InstrSpec 0x12763c [0x31, 0xF6] (fun s => s.RIP = 0x12763c) (xorR32R32Effect 0x12763c 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12763c 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x12763c 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x12763e [0x89, 0x70, 0x04] (StorePre 0x12763e 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x12763e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12763e 6 (.base 0 (.d8 0x4)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12763e 6 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x12763e 6 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127641 [0xC7, 0x00, 0x02, 0x00, 0x00, 0x00] (StorePre 0x127641 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127641 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127641 6 (.base 0 .none) 0x2)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127641 6 (.base 0 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x127641 (.base 0 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127647 [0xC3] (RetPre 0x127647) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127647).toInstrSpec (ret_effect_step 0x127647) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12763e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127641) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127647) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l12763c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12763c :=
  Rest.liftedBlock (rest_l12763c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12763c x hx)

theorem rest_l127648 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127648 bytes_l127648) (entryMap (live .l127648))
      10 0x127648 bytes_l127648 b_l127648 := by
  have f0 : InstrSpec 0x127648 [0x40, 0x0F, 0xB6, 0xF6] (fun s => s.RIP = 0x127648) (movzxR32R8Effect 0x127648 4 6 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x127648 4 6 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x127648 0x40 (by decide) 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x12764c [0x89, 0xCF] (fun s => s.RIP = 0x12764c) (movR32R32Effect 0x12764c 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x12764c 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x12764c 0xcf (by decide)) pre_rip
  have f2 : InstrSpec 0x12764e [0x29, 0xD7] (fun s => s.RIP = 0x12764e) (subR32R32Effect 0x12764e 2 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12764e 2 7 2).toInstrSpec (sub_r32_r32_effect_step 0x12764e 0xd7 (by decide)) pre_rip
  have f3 : InstrSpec 0x127650 [0xFF, 0xC7] (fun s => s.RIP = 0x127650) (incR32Effect 0x127650 2 7)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (incR32Effect_footprint 0x127650 2 7).toInstrSpec (inc_r32_effect_step 0x127650 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127652 [0xC1, 0xEE, 0x07] (fun s => s.RIP = 0x127652) (shrR32Effect 0x127652 3 6 7)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x127652 3 6 7).toInstrSpec (shr_r32_imm8_effect_step 0x127652 0xee 0x7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x127655 [0x48, 0x01, 0xCE] (fun s => s.RIP = 0x127655) (addR64R64Effect 0x127655 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127655 6 1).toInstrSpec (add_r64_r64_effect_step 0x127655 0x48 0xce (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x127658 [0x48, 0x29, 0xD6] (fun s => s.RIP = 0x127658) (subR64R64Effect 0x127658 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x127658 6 2).toInstrSpec (sub_r64_r64_effect_step 0x127658 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12765b [0x48, 0xFF, 0xC6] (fun s => s.RIP = 0x12765b) (incR64Effect 0x12765b 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (incR64Effect_footprint 0x12765b 6).toInstrSpec (inc_r64_effect_step 0x12765b 0x48 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12765e [0x39, 0xFE] (fun s => s.RIP = 0x12765e) (cmpR32R32Effect 0x12765e 2 6 7)
      [.gpr 6, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x12765e 2 6 7).toInstrSpec (cmp_r32_r32_effect_step 0x12765e 0xfe (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12764c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12764e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127650) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127652) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127655) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 63), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127658) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12765b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12765e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127660) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x127660 2 0xcf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127648 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127648 :=
  Rest.liftedBlock (rest_l127648 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127648 x hx)

theorem rest_l127662 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127662 bytes_l127662) (entryMap (live .l127662))
      3 0x127662 bytes_l127662 b_l127662 := by
  have f0 : InstrSpec 0x127662 [0x89, 0x70, 0x04] (StorePre 0x127662 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127662 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127662 6 (.base 0 (.d8 0x4)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127662 6 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127662 6 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127665 [0xC7, 0x00, 0x02, 0x00, 0x00, 0x00] (StorePre 0x127665 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127665 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127665 6 (.base 0 .none) 0x2)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127665 6 (.base 0 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x127665 (.base 0 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12766b [0xC3] (RetPre 0x12766b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12766b).toInstrSpec (ret_effect_step 0x12766b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127665) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12766b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l127662 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127662 :=
  Rest.liftedBlock (rest_l127662 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127662 x hx)

theorem rest_l127670 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127670 bytes_l127670) (entryMap (live .l127670))
      7 0x127670 bytes_l127670 b_l127670 := by
  have f0 : InstrSpec 0x127670 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127670) (movR64R64Effect 0x127670 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127670 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127670 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127673 [0x0F, 0xB6, 0x0E] (LoadPre 0x127673 (fun s => AddrMode.addr (.base 6 .none) s (0x127673 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x127673 3 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x127673 3 1 (.base 6 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x127673 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127676 [0xC1, 0xE9, 0x07] (fun s => s.RIP = 0x127676) (shrR32Effect 0x127676 3 1 7)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x127676 3 1 7).toInstrSpec (shr_r32_imm8_effect_step 0x127676 0xe9 0x7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127679 [0xFF, 0xC1] (fun s => s.RIP = 0x127679) (incR32Effect 0x127679 2 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR32Effect_footprint 0x127679 2 1).toInstrSpec (inc_r32_effect_step 0x127679 0xc1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12767b [0x89, 0x4F, 0x04] (StorePre 0x12767b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x12767b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12767b 1 (.base 7 (.d8 0x4)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12767b 1 (.base 7 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x12767b 1 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12767e [0xC7, 0x07, 0x02, 0x00, 0x00, 0x00] (StorePre 0x12767e 6 (fun s => AddrMode.addr (.base 7 .none) s (0x12767e + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12767e 6 (.base 7 .none) 0x2)
      [.gpr 7] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x12767e 6 (.base 7 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x12767e (.base 7 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127684 [0xC3] (RetPre 0x127684) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127684).toInstrSpec (ret_effect_step 0x127684) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127673) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127676) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127679) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12767b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12767e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127684) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l127670 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127670 :=
  Rest.liftedBlock (rest_l127670 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127670 x hx)

theorem rest_l127690 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127690 bytes_l127690) (entryMap (live .l127690))
      4 0x127690 bytes_l127690 b_l127690 := by
  have f0 : InstrSpec 0x127690 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127690) (movR64R64Effect 0x127690 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127690 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127690 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127693 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x127693) (movR64R64Effect 0x127693 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127693 1 2).toInstrSpec (mov_r64_r64_effect_step 0x127693 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127696 [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x127696) (shrR64Effect 0x127696 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x127696 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x127696 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127693) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127696) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 58) f2 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x127696 4 1 32 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12769a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x12769a 4 0xe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127690 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127690 :=
  Rest.liftedBlock (rest_l127690 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127690 x hx)

theorem rest_l12769c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12769c bytes_l12769c) (entryMap (live .l12769c))
      5 0x12769c bytes_l12769c b_l12769c := by
  have f0 : InstrSpec 0x12769c [0xBE, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12769c) (movR32Imm32Effect 0x12769c 5 6 0xc)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x12769c 5 6 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x12769c 0xbe (by decide) 0xc) pre_rip
  have f1 : InstrSpec 0x1276a1 [0x31, 0xC9] (fun s => s.RIP = 0x1276a1) (xorR32R32Effect 0x1276a1 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1276a1 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1276a1 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x1276a3 [0x89, 0x08] (StorePre 0x1276a3 2 (fun s => AddrMode.addr (.base 0 .none) s (0x1276a3 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1276a3 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1276a3 1 (.base 0 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1276a3 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1276a5 [0x48, 0x89, 0x70, 0x08] (StorePre 0x1276a5 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1276a5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276a5 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1276a5 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1276a5 0x48 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1276a9 [0xC3] (RetPre 0x1276a9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1276a9).toInstrSpec (ret_effect_step 0x1276a9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276a5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276a9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 60), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l12769c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12769c :=
  Rest.liftedBlock (rest_l12769c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12769c x hx)

theorem rest_l1276aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1276aa bytes_l1276aa) (entryMap (live .l1276aa))
      9 0x1276aa bytes_l1276aa b_l1276aa := by
  have f0 : InstrSpec 0x1276aa [0x48, 0x89, 0x50, 0x10] (StorePre 0x1276aa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x1276aa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276aa 2 (.base 0 (.d8 0x10)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1276aa 2 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1276aa 0x48 (by decide) 2 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1276ae [0x48, 0xC7, 0x40, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1276ae 8 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x1276ae + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1276ae (.base 0 (.d8 0x18)) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1276ae (.base 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1276ae 0x48 (by decide) (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1276b6 [0x89, 0x50, 0x20] (StorePre 0x1276b6 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x1276b6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1276b6 2 (.base 0 (.d8 0x20)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1276b6 2 (.base 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_low_effect_step 0x1276b6 2 (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1276b9 [0xC7, 0x40, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1276b9 7 (fun s => AddrMode.addr (.base 0 (.d8 0x24)) s (0x1276b9 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1276b9 7 (.base 0 (.d8 0x24)) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1276b9 7 (.base 0 (.d8 0x24)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x1276b9 (.base 0 (.d8 0x24)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1276c0 [0xC6, 0x40, 0x28, 0x00] (StorePre 0x1276c0 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x1276c0 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1276c0 (.base 0 (.d8 0x28)) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1276c0 (.base 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1276c0 (.base 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1276c4 [0xB9, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1276c4) (movR32Imm32Effect 0x1276c4 5 1 0x2)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1276c4 5 1 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x1276c4 0xb9 (by decide) 0x2) pre_rip
  have f6 : InstrSpec 0x1276c9 [0x89, 0x08] (StorePre 0x1276c9 2 (fun s => AddrMode.addr (.base 0 .none) s (0x1276c9 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1276c9 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1276c9 1 (.base 0 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1276c9 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1276cb [0x48, 0x89, 0x70, 0x08] (StorePre 0x1276cb 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1276cb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276cb 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1276cb 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1276cb 0x48 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1276cf [0xC3] (RetPre 0x1276cf) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1276cf).toInstrSpec (ret_effect_step 0x1276cf) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276ae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276b6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276b9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276c0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276c4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276c9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276cb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276cf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 64) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l1276aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1276aa :=
  Rest.liftedBlock (rest_l1276aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1276aa x hx)

theorem rest_l1276d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1276d0 bytes_l1276d0) (entryMap (live .l1276d0))
      3 0x1276d0 bytes_l1276d0 b_l1276d0 := by
  have f0 : InstrSpec 0x1276d0 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x1276d0) (movR64R64Effect 0x1276d0 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1276d0 0 7).toInstrSpec (mov_r64_r64_effect_step 0x1276d0 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1276d3 [0x40, 0x38, 0xD6] (fun s => s.RIP = 0x1276d3) (cmpR8R8Effect 0x1276d3 3 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x1276d3 3 6 2).toInstrSpec (cmp_r8_r8_rex_effect_step 0x1276d3 0x40 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1276d6 5 0x4e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1276d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1276d0 :=
  Rest.liftedBlock (rest_l1276d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1276d0 x hx)

theorem rest_l1276d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1276d8 bytes_l1276d8) (entryMap (live .l1276d8))
      10 0x1276d8 bytes_l1276d8 b_l1276d8 := by
  have f0 : InstrSpec 0x1276d8 [0x41, 0x89, 0xF0] (fun s => s.RIP = 0x1276d8) (movR32R32Effect 0x1276d8 3 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x1276d8 3 8 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x1276d8 0x41 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1276db [0x41, 0xC1, 0xE8, 0x08] (fun s => s.RIP = 0x1276db) (shrR32Effect 0x1276db 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x1276db 4 8 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1276db 0x41 0xe8 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1276df [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x1276df) (movR64R64Effect 0x1276df 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1276df 1 6).toInstrSpec (mov_r64_r64_effect_step 0x1276df 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1276e2 [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x1276e2) (shrR64Effect 0x1276e2 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1276e2 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x1276e2 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1276e6 [0x41, 0x89, 0xD1] (fun s => s.RIP = 0x1276e6) (movR32R32Effect 0x1276e6 3 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1276e6 3 9 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x1276e6 0x41 0xd1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1276e9 [0x41, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x1276e9) (shrR32Effect 0x1276e9 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1276e9 4 9 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1276e9 0x41 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1276ed [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x1276ed) (movR64R64Effect 0x1276ed 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1276ed 7 2).toInstrSpec (mov_r64_r64_effect_step 0x1276ed 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1276f0 [0x48, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x1276f0) (shrR64Effect 0x1276f0 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x1276f0 4 7 32).toInstrSpec (shr_r64_imm8_effect_step 0x1276f0 0x48 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1276f4 [0x40, 0x80, 0xFE, 0x18] (fun s => s.RIP = 0x1276f4) (cmpR8Imm8Effect 0x1276f4 4 6 0x18)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1276f4 4 6 0x18).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x1276f4 0x40 0xfe 0x18 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276ed) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276f0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276f4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276f8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x1276f8 4 0x10) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1276d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1276d8 :=
  Rest.liftedBlock (rest_l1276d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1276d8 x hx)

theorem rest_l1276fa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1276fa bytes_l1276fa) (entryMap (live .l1276fa))
      3 0x1276fa bytes_l1276fa b_l1276fa := by
  have f0 : InstrSpec 0x1276fa [0x44, 0x0F, 0xB6, 0xD6] (fun s => s.RIP = 0x1276fa) (movzxR32R8Effect 0x1276fa 4 10 6)
      [.gpr 6] [] [.reg 10, .rip] :=
    (movzxR32R8Effect_footprint 0x1276fa 4 10 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1276fa 0x44 (by decide) 0xd6 (by decide)) pre_rip
  have f1 : InstrSpec 0x1276fe [0x41, 0x83, 0xFA, 0x17] (fun s => s.RIP = 0x1276fe) (cmpR32Imm8Effect 0x1276fe 4 10 0x17)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1276fe 4 10 0x17).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x1276fe 0x41 0xfa 0x17 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127702) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x127702 4 0x6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1276fa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1276fa :=
  Rest.liftedBlock (rest_l1276fa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1276fa x hx)

theorem rest_l127704 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127704 bytes_l127704) (entryMap (live .l127704))
      2 0x127704 bytes_l127704 b_l127704 := by
  have f0 : InstrSpec 0x127704 [0x41, 0x83, 0xFA, 0x16] (fun s => s.RIP = 0x127704) (cmpR32Imm8Effect 0x127704 4 10 0x16)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x127704 4 10 0x16).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x127704 0x41 0xfa 0x16 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127708) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127708 5 0x11) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127704 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127704 :=
  Rest.liftedBlock (rest_l127704 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127704 x hx)

theorem rest_l12770a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12770a bytes_l12770a) (entryMap (live .l12770a))
      6 0x12770a bytes_l12770a b_l12770a := by
  have f0 : InstrSpec 0x12770a [0x45, 0x38, 0xC8] (fun s => s.RIP = 0x12770a) (cmpR8R8Effect 0x12770a 3 8 9)
      [.gpr 8, .gpr 9] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x12770a 3 8 9).toInstrSpec (cmp_r8_r8_rex_effect_step 0x12770a 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12770d [0x41, 0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x12770d) (atFlags (condHolds 4) (setccR8Effect 0x12770d 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x12770d 4 8 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x12770d 4 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f2 : InstrSpec 0x127711 [0x39, 0xF9] (fun s => s.RIP = 0x127711) (cmpR32R32Effect 0x127711 2 1 7)
      [.gpr 1, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127711 2 1 7).toInstrSpec (cmp_r32_r32_effect_step 0x127711 0xf9 (by decide)) pre_rip
  have f3 : InstrSpec 0x127713 [0x0F, 0x94, 0xC1] (fun s => s.RIP = 0x127713) (atFlags (condHolds 4) (setccR8Effect 0x127713 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x127713 3 1 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x127713 4 0xc1 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x127716 [0x44, 0x84, 0xC1] (fun s => s.RIP = 0x127716) (testR8R8Effect 0x127716 3 1 8)
      [.gpr 1, .gpr 8] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x127716 3 1 8).toInstrSpec (test_r8_r8_rex_effect_step 0x127716 0x44 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12770d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127711) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127713) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127716) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127719) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x127719 4 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12770a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12770a :=
  Rest.liftedBlock (rest_l12770a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12770a x hx)

theorem rest_l12771b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12771b bytes_l12771b) (entryMap (live .l12771b))
      3 0x12771b bytes_l12771b b_l12771b := by
  have f0 : InstrSpec 0x12771b [0x48, 0x89, 0x70, 0x04] (StorePre 0x12771b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x12771b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12771b 6 (.base 0 (.d8 0x4)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x12771b 6 (.base 0 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x12771b 0x48 (by decide) 6 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12771f [0xC7, 0x00, 0x02, 0x00, 0x00, 0x00] (StorePre 0x12771f 6 (fun s => AddrMode.addr (.base 0 .none) s (0x12771f + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12771f 6 (.base 0 .none) 0x2)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x12771f 6 (.base 0 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x12771f (.base 0 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127725 [0xC3] (RetPre 0x127725) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127725).toInstrSpec (ret_effect_step 0x127725) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12771f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127725) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l12771b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12771b :=
  Rest.liftedBlock (rest_l12771b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12771b x hx)

theorem rest_l127726 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127726 bytes_l127726) (entryMap (live .l127726))
      5 0x127726 bytes_l127726 b_l127726 := by
  have f0 : InstrSpec 0x127726 [0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x127726 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127726 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127726 6 (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127726 6 (.base 0 .none) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x127726 (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12772c [0xC6, 0x40, 0x08, 0x11] (StorePre 0x12772c 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12772c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12772c (.base 0 (.d8 0x8)) 0x11)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x12772c (.base 0 (.d8 0x8)) 0x11).toInstrSpec (mov_m8_imm8_effect_step 0x12772c (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x11) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127730 [0x48, 0x89, 0x50, 0x0C] (StorePre 0x127730 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127730 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127730 2 (.base 0 (.d8 0xc)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127730 2 (.base 0 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x127730 0x48 (by decide) 2 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127734 [0x48, 0x89, 0x70, 0x14] (StorePre 0x127734 4 (fun s => AddrMode.addr (.base 0 (.d8 0x14)) s (0x127734 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127734 6 (.base 0 (.d8 0x14)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127734 6 (.base 0 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x127734 0x48 (by decide) 6 (.base 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127738 [0xC3] (RetPre 0x127738) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127738).toInstrSpec (ret_effect_step 0x127738) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12772c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127730) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127734) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127738) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l127726 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127726 :=
  Rest.liftedBlock (rest_l127726 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127726 x hx)

theorem rest_l127b80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127b80 bytes_l127b80) (entryMap (live .l127b80))
      3 0x127b80 bytes_l127b80 b_l127b80 := by
  have f0 : InstrSpec 0x127b80 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127b80) (movR64R64Effect 0x127b80 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127b80 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127b80 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127b83 [0x80, 0x7E, 0x20, 0x00] (LoadPre 0x127b83 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127b83 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x127b83 4 (.base 6 (.d8 0x20)) 0x0)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x127b83 4 (.base 6 (.d8 0x20)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x127b83 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b83) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b87) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x127b87 4 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127b80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127b80 :=
  Rest.liftedBlock (rest_l127b80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127b80 x hx)

theorem rest_l127b89 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127b89 bytes_l127b89) (entryMap (live .l127b89))
      6 0x127b89 bytes_l127b89 b_l127b89 := by
  have f0 : InstrSpec 0x127b89 [0xC6, 0x46, 0x20, 0x01] (StorePre 0x127b89 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127b89 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127b89 (.base 6 (.d8 0x20)) 0x1)
      [.gpr 6] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127b89 (.base 6 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x127b89 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127b8d [0x8B, 0x4E, 0x1C] (LoadPre 0x127b8d (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127b8d + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127b8d 1 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x127b8d 1 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x127b8d 1 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127b90 [0xC7, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x127b90 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127b90 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127b90 6 (.base 0 .none) 0x1)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127b90 6 (.base 0 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x127b90 (.base 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127b96 [0x89, 0x48, 0x04] (StorePre 0x127b96 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127b96 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127b96 1 (.base 0 (.d8 0x4)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127b96 1 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127b96 1 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127b99 [0xC6, 0x40, 0x08, 0x02] (StorePre 0x127b99 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127b99 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127b99 (.base 0 (.d8 0x8)) 0x2)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127b99 (.base 0 (.d8 0x8)) 0x2).toInstrSpec (mov_m8_imm8_effect_step 0x127b99 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127b9d [0xC3] (RetPre 0x127b9d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127b9d).toInstrSpec (ret_effect_step 0x127b9d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b8d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b90) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b96) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b99) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b9d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127b89 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127b89 :=
  Rest.liftedBlock (rest_l127b89 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127b89 x hx)

theorem rest_l127b9e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127b9e bytes_l127b9e) (entryMap (live .l127b9e))
      5 0x127b9e bytes_l127b9e b_l127b9e := by
  have f0 : InstrSpec 0x127b9e [0x48, 0x8B, 0x7E, 0x08] (LoadPre 0x127b9e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x127b9e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127b9e 7 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x127b9e 7 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x127b9e 0x48 (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127ba2 [0x8B, 0x4E, 0x1C] (LoadPre 0x127ba2 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127ba2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127ba2 1 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x127ba2 1 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x127ba2 1 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127ba5 [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x127ba5) (movR64R64Effect 0x127ba5 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x127ba5 9 7).toInstrSpec (mov_r64_r64_effect_step 0x127ba5 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127ba8 [0x49, 0x29, 0xC9] (fun s => s.RIP = 0x127ba8) (subR64R64Effect 0x127ba8 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x127ba8 9 1).toInstrSpec (sub_r64_r64_effect_step 0x127ba8 0x49 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ba2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ba5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ba8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x127bab 3 0x26) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127b9e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127b9e :=
  Rest.liftedBlock (rest_l127b9e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127b9e x hx)

theorem rest_l127bad [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bad bytes_l127bad) (entryMap (live .l127bad))
      9 0x127bad bytes_l127bad b_l127bad := by
  have f0 : InstrSpec 0x127bad [0x48, 0x89, 0xF9] (fun s => s.RIP = 0x127bad) (movR64R64Effect 0x127bad 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127bad 1 7).toInstrSpec (mov_r64_r64_effect_step 0x127bad 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127bb0 [0x48, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x127bb0) (shlR64Effect 0x127bb0 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x127bb0 4 1 32).toInstrSpec (shl_r64_imm8_effect_step 0x127bb0 0x48 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127bb4 [0x48, 0xBA, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127bb4) (movR64Imm64Effect 0x127bb4 2 0x100000003)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x127bb4 2 0x100000003).toInstrSpec (mov_r64_imm64_effect_step 0x127bb4 0x48 0xba (by decide) (by decide) 0x100000003) pre_rip
  have f3 : InstrSpec 0x127bbe [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x127bbe) (addR64R64Effect 0x127bbe 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127bbe 2 1).toInstrSpec (add_r64_r64_effect_step 0x127bbe 0x48 0xca (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127bc1 [0xC7, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x127bc1 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127bc1 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127bc1 6 (.base 0 .none) 0x1)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127bc1 6 (.base 0 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x127bc1 (.base 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127bc7 [0x89, 0x78, 0x04] (StorePre 0x127bc7 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127bc7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bc7 7 (.base 0 (.d8 0x4)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127bc7 7 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127bc7 7 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127bca [0x48, 0x89, 0x50, 0x08] (StorePre 0x127bca 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127bca + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127bca 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127bca 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127bca 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x127bce [0x48, 0x89, 0x78, 0x10] (StorePre 0x127bce 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127bce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127bce 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127bce 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127bce 0x48 (by decide) 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x127bd2 [0xC3] (RetPre 0x127bd2) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127bd2).toInstrSpec (ret_effect_step 0x127bd2) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bb0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bb4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bbe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bc1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bc7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bce) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bd2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 67) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l127bad [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bad :=
  Rest.liftedBlock (rest_l127bad code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bad x hx)

theorem rest_l127bd3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bd3 bytes_l127bd3) (entryMap (live .l127bd3))
      4 0x127bd3 bytes_l127bd3 b_l127bd3 := by
  have f0 : InstrSpec 0x127bd3 [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x127bd3) (movR32R32Effect 0x127bd3 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x127bd3 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x127bd3 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127bd6 [0x01, 0xCA] (fun s => s.RIP = 0x127bd6) (addR32R32Effect 0x127bd6 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x127bd6 2 2 1).toInstrSpec (add_r32_r32_effect_step 0x127bd6 0xca (by decide)) pre_rip
  have f2 : InstrSpec 0x127bd8 [0x4D, 0x39, 0xC1] (fun s => s.RIP = 0x127bd8) (cmpR64R64Effect 0x127bd8 9 8)
      [.gpr 9, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127bd8 9 8).toInstrSpec (cmp_r64_r64_effect_step 0x127bd8 0x4d 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bd6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bd8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bdb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x127bdb 3 0x1c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127bd3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bd3 :=
  Rest.liftedBlock (rest_l127bd3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bd3 x hx)

theorem rest_l127bdd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bdd bytes_l127bdd) (entryMap (live .l127bdd))
      2 0x127bdd bytes_l127bdd b_l127bdd := by
  have f0 : InstrSpec 0x127bdd [0x39, 0xCA] (fun s => s.RIP = 0x127bdd) (cmpR32R32Effect 0x127bdd 2 2 1)
      [.gpr 2, .gpr 1] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127bdd 2 2 1).toInstrSpec (cmp_r32_r32_effect_step 0x127bdd 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bdf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127bdf 2 0x55) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127bdd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bdd :=
  Rest.liftedBlock (rest_l127bdd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bdd x hx)

theorem rest_l127be1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127be1 bytes_l127be1) (entryMap (live .l127be1))
      7 0x127be1 bytes_l127be1 b_l127be1 := by
  have f0 : InstrSpec 0x127be1 [0xC6, 0x46, 0x20, 0x01] (StorePre 0x127be1 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127be1 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127be1 (.base 6 (.d8 0x20)) 0x1)
      [.gpr 6] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127be1 (.base 6 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x127be1 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127be5 [0xC7, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x127be5 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127be5 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127be5 6 (.base 0 .none) 0x1)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127be5 6 (.base 0 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x127be5 (.base 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127beb [0x89, 0x48, 0x04] (StorePre 0x127beb 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127beb + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127beb 1 (.base 0 (.d8 0x4)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127beb 1 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127beb 1 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127bee [0xC6, 0x40, 0x08, 0x03] (StorePre 0x127bee 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127bee + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127bee (.base 0 (.d8 0x8)) 0x3)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127bee (.base 0 (.d8 0x8)) 0x3).toInstrSpec (mov_m8_imm8_effect_step 0x127bee (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127bf2 [0x89, 0x50, 0x0C] (StorePre 0x127bf2 3 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127bf2 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bf2 2 (.base 0 (.d8 0xc)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127bf2 2 (.base 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x127bf2 2 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127bf5 [0x89, 0x78, 0x10] (StorePre 0x127bf5 3 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127bf5 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bf5 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127bf5 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x127bf5 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127bf8 [0xC3] (RetPre 0x127bf8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127bf8).toInstrSpec (ret_effect_step 0x127bf8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127be5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127beb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bf2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bf5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bf8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l127be1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127be1 :=
  Rest.liftedBlock (rest_l127be1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127be1 x hx)

theorem rest_l127bf9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bf9 bytes_l127bf9) (entryMap (live .l127bf9))
      2 0x127bf9 bytes_l127bf9 b_l127bf9 := by
  have f0 : InstrSpec 0x127bf9 [0x39, 0xCA] (fun s => s.RIP = 0x127bf9) (cmpR32R32Effect 0x127bf9 2 2 1)
      [.gpr 2, .gpr 1] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127bf9 2 2 1).toInstrSpec (cmp_r32_r32_effect_step 0x127bf9 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bfb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127bfb 2 0x44) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127bf9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bf9 :=
  Rest.liftedBlock (rest_l127bf9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bf9 x hx)

theorem rest_l127bfd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bfd bytes_l127bfd) (entryMap (live .l127bfd))
      3 0x127bfd bytes_l127bfd b_l127bfd := by
  have f0 : InstrSpec 0x127bfd [0x8B, 0x7E, 0x18] (LoadPre 0x127bfd (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x127bfd + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127bfd 7 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x127bfd 7 (.base 6 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x127bfd 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127c00 [0x39, 0xFA] (fun s => s.RIP = 0x127c00) (cmpR32R32Effect 0x127c00 2 2 7)
      [.gpr 2, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127c00 2 2 7).toInstrSpec (cmp_r32_r32_effect_step 0x127c00 0xfa (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c00) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c02) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x127c02 6 0x1a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127bfd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bfd :=
  Rest.liftedBlock (rest_l127bfd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bfd x hx)

theorem rest_l127c04 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c04 bytes_l127c04) (entryMap (live .l127c04))
      2 0x127c04 bytes_l127c04 b_l127c04 := by
  have f0 : InstrSpec 0x127c04 [0x41, 0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127c04) (movR32Imm32Effect 0x127c04 6 8 0x1)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x127c04 6 8 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x127c04 0x41 0xb8 (by decide) (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x127c0a [0x40, 0xB6, 0x03] (fun s => s.RIP = 0x127c0a) (movR8Imm8Effect 0x127c0a 3 6 0x3)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR8Imm8Effect_footprint 0x127c0a 3 6 0x3).toInstrSpec (mov_r8_imm8_rex_effect_step 0x127c0a 0x40 (by decide) 0xb6 (by decide) 0x3) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c0a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c0d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l127c04 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c04 :=
  Rest.liftedBlock (rest_l127c04 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c04 x hx)

theorem rest_l127c0d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c0d bytes_l127c0d) (entryMap (live .l127c0d))
      6 0x127c0d bytes_l127c0d b_l127c0d := by
  have f0 : InstrSpec 0x127c0d [0x44, 0x89, 0x00] (StorePre 0x127c0d 3 (fun s => AddrMode.addr (.base 0 .none) s (0x127c0d + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x127c0d 8 (.base 0 .none))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM32R32Effect_footprint 0x127c0d 8 (.base 0 .none)).toInstrSpec (mov_m32_r32_effect_step 0x127c0d 0x44 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127c10 [0x89, 0x48, 0x04] (StorePre 0x127c10 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127c10 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c10 1 (.base 0 (.d8 0x4)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c10 1 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c10 1 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127c13 [0x40, 0x88, 0x70, 0x08] (StorePre 0x127c13 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c13 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127c13 4 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x127c13 4 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x127c13 0x40 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127c17 [0x89, 0x50, 0x0C] (StorePre 0x127c17 3 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127c17 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c17 2 (.base 0 (.d8 0xc)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c17 2 (.base 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c17 2 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127c1a [0x89, 0x78, 0x10] (StorePre 0x127c1a 3 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c1a + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c1a 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c1a 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c1a 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127c1d [0xC3] (RetPre 0x127c1d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127c1d).toInstrSpec (ret_effect_step 0x127c1d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c10) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c13) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c17) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c1a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c1d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127c0d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c0d :=
  Rest.liftedBlock (rest_l127c0d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c0d x hx)

theorem rest_l127c1e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c1e bytes_l127c1e) (entryMap (live .l127c1e))
      7 0x127c1e bytes_l127c1e b_l127c1e := by
  have f0 : InstrSpec 0x127c1e [0x48, 0x8B, 0x3E] (LoadPre 0x127c1e (fun s => AddrMode.addr (.base 6 .none) s (0x127c1e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x127c1e 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x127c1e 7 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x127c1e 0x48 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127c21 [0x48, 0x01, 0xCF] (fun s => s.RIP = 0x127c21) (addR64R64Effect 0x127c21 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127c21 7 1).toInstrSpec (add_r64_r64_effect_step 0x127c21 0x48 0xcf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127c24 [0x89, 0x56, 0x1C] (StorePre 0x127c24 3 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127c24 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c24 2 (.base 6 (.d8 0x1c)))
      [.gpr 2, .gpr 6] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c24 2 (.base 6 (.d8 0x1c))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c24 2 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127c27 [0x48, 0x89, 0x78, 0x08] (StorePre 0x127c27 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c27 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c27 7 (.base 0 (.d8 0x8)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127c27 7 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127c27 0x48 (by decide) 7 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127c2b [0x4C, 0x89, 0x40, 0x10] (StorePre 0x127c2b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c2b 8 (.base 0 (.d8 0x10)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127c2b 8 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127c2b 0x4c (by decide) 0 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127c2f [0xC7, 0x00, 0x02, 0x00, 0x00, 0x00] (StorePre 0x127c2f 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127c2f + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127c2f 6 (.base 0 .none) 0x2)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127c2f 6 (.base 0 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x127c2f (.base 0 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127c35 [0xC3] (RetPre 0x127c35) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127c35).toInstrSpec (ret_effect_step 0x127c35) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c21) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c24) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c27) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c2b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c2f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c35) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l127c1e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c1e :=
  Rest.liftedBlock (rest_l127c1e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c1e x hx)

theorem rest_l127c36 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c36 bytes_l127c36) (entryMap (live .l127c36))
      3 0x127c36 bytes_l127c36 b_l127c36 := by
  have f0 : InstrSpec 0x127c36 [0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x127c36 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127c36 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127c36 6 (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127c36 6 (.base 0 .none) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x127c36 (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127c3c [0xC6, 0x40, 0x08, 0x0C] (StorePre 0x127c3c 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c3c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127c3c (.base 0 (.d8 0x8)) 0xc)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127c3c (.base 0 (.d8 0x8)) 0xc).toInstrSpec (mov_m8_imm8_effect_step 0x127c3c (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0xc) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127c40 [0xC3] (RetPre 0x127c40) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127c40).toInstrSpec (ret_effect_step 0x127c40) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c3c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c40) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l127c36 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c36 :=
  Rest.liftedBlock (rest_l127c36 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c36 x hx)

theorem rest_l127c41 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c41 bytes_l127c41) (entryMap (live .l127c41))
      3 0x127c41 bytes_l127c41 b_l127c41 := by
  have f0 : InstrSpec 0x127c41 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x127c41) (xorR32R32Effect 0x127c41 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127c41 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x127c41 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127c44 [0x40, 0xB6, 0x0C] (fun s => s.RIP = 0x127c44) (movR8Imm8Effect 0x127c44 3 6 0xc)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR8Imm8Effect_footprint 0x127c44 3 6 0xc).toInstrSpec (mov_r8_imm8_rex_effect_step 0x127c44 0x40 (by decide) 0xb6 (by decide) 0xc) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c44) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c47) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x127c47 0xc4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127c41 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c41 :=
  Rest.liftedBlock (rest_l127c41 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c41 x hx)

theorem rest_l127c50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c50 bytes_l127c50) (entryMap (live .l127c50))
      5 0x127c50 bytes_l127c50 b_l127c50 := by
  have f0 : InstrSpec 0x127c50 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127c50) (movR64R64Effect 0x127c50 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127c50 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127c50 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127c53 [0x89, 0xC9] (fun s => s.RIP = 0x127c53) (movR32R32Effect 0x127c53 2 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x127c53 2 1 1).toInstrSpec (mov_r32_r32_effect_step 0x127c53 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x127c55 [0xBF, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127c55) (movR32Imm32Effect 0x127c55 5 7 0x2)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x127c55 5 7 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x127c55 0xbf (by decide) 0x2) pre_rip
  have f3 : InstrSpec 0x127c5a [0x48, 0x39, 0xCA] (fun s => s.RIP = 0x127c5a) (cmpR64R64Effect 0x127c5a 2 1)
      [.gpr 2, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127c5a 2 1).toInstrSpec (cmp_r64_r64_effect_step 0x127c5a 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c55) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c5a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c5d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x127c5d 3 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127c50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c50 :=
  Rest.liftedBlock (rest_l127c50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c50 x hx)

theorem rest_l127c5f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c5f bytes_l127c5f) (entryMap (live .l127c5f))
      7 0x127c5f bytes_l127c5f b_l127c5f := by
  have f0 : InstrSpec 0x127c5f [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x127c5f) (movR64R64Effect 0x127c5f 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127c5f 1 2).toInstrSpec (mov_r64_r64_effect_step 0x127c5f 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127c62 [0x48, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x127c62) (shlR64Effect 0x127c62 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x127c62 4 1 32).toInstrSpec (shl_r64_imm8_effect_step 0x127c62 0x48 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127c66 [0x48, 0xBE, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127c66) (movR64Imm64Effect 0x127c66 6 0x100000003)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x127c66 6 0x100000003).toInstrSpec (mov_r64_imm64_effect_step 0x127c66 0x48 0xbe (by decide) (by decide) 0x100000003) pre_rip
  have f3 : InstrSpec 0x127c70 [0x48, 0x01, 0xCE] (fun s => s.RIP = 0x127c70) (addR64R64Effect 0x127c70 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127c70 6 1).toInstrSpec (add_r64_r64_effect_step 0x127c70 0x48 0xce (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127c73 [0x89, 0x50, 0x04] (StorePre 0x127c73 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127c73 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c73 2 (.base 0 (.d8 0x4)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c73 2 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c73 2 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127c76 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127c76) (movR32Imm32Effect 0x127c76 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x127c76 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x127c76 0xbf (by decide) 0x1) pre_rip
  have f6 : InstrSpec 0x127c7b [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x127c7b) (movR64R64Effect 0x127c7b 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127c7b 1 2).toInstrSpec (mov_r64_r64_effect_step 0x127c7b 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c62) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c66) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c70) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c73) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c76) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c7b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c7e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l127c5f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c5f :=
  Rest.liftedBlock (rest_l127c5f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c5f x hx)

theorem rest_l127c7e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c7e bytes_l127c7e) (entryMap (live .l127c7e))
      4 0x127c7e bytes_l127c7e b_l127c7e := by
  have f0 : InstrSpec 0x127c7e [0x89, 0x38] (StorePre 0x127c7e 2 (fun s => AddrMode.addr (.base 0 .none) s (0x127c7e + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x127c7e 7 (.base 0 .none))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c7e 7 (.base 0 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x127c7e 7 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127c80 [0x48, 0x89, 0x70, 0x08] (StorePre 0x127c80 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c80 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c80 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127c80 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127c80 0x48 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127c84 [0x48, 0x89, 0x48, 0x10] (StorePre 0x127c84 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c84 1 (.base 0 (.d8 0x10)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127c84 1 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127c84 0x48 (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127c88 [0xC3] (RetPre 0x127c88) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127c88).toInstrSpec (ret_effect_step 0x127c88) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c80) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c84) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c88) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l127c7e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c7e :=
  Rest.liftedBlock (rest_l127c7e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c7e x hx)

theorem rest_l127d50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127d50 bytes_l127d50) (entryMap (live .l127d50))
      5 0x127d50 bytes_l127d50 b_l127d50 := by
  have f0 : InstrSpec 0x127d50 [0x48, 0x83, 0xEC, 0x01] (fun s => s.RIP = 0x127d50) (subR64Imm8Effect 0x127d50 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x127d50 4 0x1).toInstrSpec (sub_r64_imm8_effect_step 0x127d50 0x48 0xec 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127d54 [0x40, 0x88, 0x3C, 0x24] (StorePre 0x127d54 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127d54 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127d54 4 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x127d54 4 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x127d54 0x40 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127d58 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x127d58 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127d58 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x127d58 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x127d58 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x127d58 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127d5c [0x48, 0x83, 0xC4, 0x01] (fun s => s.RIP = 0x127d5c) (addR64Imm8Effect 0x127d5c 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127d5c 4 0x1).toInstrSpec (add_r64_imm8_effect_step 0x127d5c 0x48 0xc4 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127d60 [0xC3] (RetPre 0x127d60) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127d60).toInstrSpec (ret_effect_step 0x127d60) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d58) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d60) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 62) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l127d50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127d50 :=
  Rest.liftedBlock (rest_l127d50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127d50 x hx)

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

theorem_by block_l110b80_eval :
    program.runBlock (dialect code) ⟨.l110b80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1148d0_eval :
    program.runBlock (dialect code) ⟨.l1148d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c3c0_eval :
    program.runBlock (dialect code) ⟨.l11c3c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c3f0_eval :
    program.runBlock (dialect code) ⟨.l11c3f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c400_eval :
    program.runBlock (dialect code) ⟨.l11c400, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c4c4_eval :
    program.runBlock (dialect code) ⟨.l11c4c4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c4cc_eval :
    program.runBlock (dialect code) ⟨.l11c4cc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c4ec_eval :
    program.runBlock (dialect code) ⟨.l11c4ec, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c508_eval :
    program.runBlock (dialect code) ⟨.l11c508, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120350_eval :
    program.runBlock (dialect code) ⟨.l120350, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120398_eval :
    program.runBlock (dialect code) ⟨.l120398, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1203a3_eval :
    program.runBlock (dialect code) ⟨.l1203a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1203b0_eval :
    program.runBlock (dialect code) ⟨.l1203b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1203c0_eval :
    program.runBlock (dialect code) ⟨.l1203c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1203ce_eval :
    program.runBlock (dialect code) ⟨.l1203ce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120470_eval :
    program.runBlock (dialect code) ⟨.l120470, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124100_eval :
    program.runBlock (dialect code) ⟨.l124100, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124111_eval :
    program.runBlock (dialect code) ⟨.l124111, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12411a_eval :
    program.runBlock (dialect code) ⟨.l12411a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12411f_eval :
    program.runBlock (dialect code) ⟨.l12411f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124134_eval :
    program.runBlock (dialect code) ⟨.l124134, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12413a_eval :
    program.runBlock (dialect code) ⟨.l12413a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12415a_eval :
    program.runBlock (dialect code) ⟨.l12415a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12417c_eval :
    program.runBlock (dialect code) ⟨.l12417c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12418c_eval :
    program.runBlock (dialect code) ⟨.l12418c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12419e_eval :
    program.runBlock (dialect code) ⟨.l12419e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1241bf_eval :
    program.runBlock (dialect code) ⟨.l1241bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1241d7_eval :
    program.runBlock (dialect code) ⟨.l1241d7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1241e0_eval :
    program.runBlock (dialect code) ⟨.l1241e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1241ec_eval :
    program.runBlock (dialect code) ⟨.l1241ec, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1241f2_eval :
    program.runBlock (dialect code) ⟨.l1241f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124203_eval :
    program.runBlock (dialect code) ⟨.l124203, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12420e_eval :
    program.runBlock (dialect code) ⟨.l12420e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124211_eval :
    program.runBlock (dialect code) ⟨.l124211, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124213_eval :
    program.runBlock (dialect code) ⟨.l124213, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124215_eval :
    program.runBlock (dialect code) ⟨.l124215, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124237_eval :
    program.runBlock (dialect code) ⟨.l124237, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124247_eval :
    program.runBlock (dialect code) ⟨.l124247, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12424d_eval :
    program.runBlock (dialect code) ⟨.l12424d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124264_eval :
    program.runBlock (dialect code) ⟨.l124264, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12426f_eval :
    program.runBlock (dialect code) ⟨.l12426f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124278_eval :
    program.runBlock (dialect code) ⟨.l124278, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124290_eval :
    program.runBlock (dialect code) ⟨.l124290, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1242a3_eval :
    program.runBlock (dialect code) ⟨.l1242a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1242e0_eval :
    program.runBlock (dialect code) ⟨.l1242e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1242ed_eval :
    program.runBlock (dialect code) ⟨.l1242ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12430f_eval :
    program.runBlock (dialect code) ⟨.l12430f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124322_eval :
    program.runBlock (dialect code) ⟨.l124322, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12432b_eval :
    program.runBlock (dialect code) ⟨.l12432b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124411_eval :
    program.runBlock (dialect code) ⟨.l124411, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124414_eval :
    program.runBlock (dialect code) ⟨.l124414, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12441a_eval :
    program.runBlock (dialect code) ⟨.l12441a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124ae0_eval :
    program.runBlock (dialect code) ⟨.l124ae0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124af7_eval :
    program.runBlock (dialect code) ⟨.l124af7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b13_eval :
    program.runBlock (dialect code) ⟨.l124b13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b35_eval :
    program.runBlock (dialect code) ⟨.l124b35, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b3e_eval :
    program.runBlock (dialect code) ⟨.l124b3e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b4e_eval :
    program.runBlock (dialect code) ⟨.l124b4e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b50_eval :
    program.runBlock (dialect code) ⟨.l124b50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b90_eval :
    program.runBlock (dialect code) ⟨.l124b90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124bcf_eval :
    program.runBlock (dialect code) ⟨.l124bcf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125760_eval :
    program.runBlock (dialect code) ⟨.l125760, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125765_eval :
    program.runBlock (dialect code) ⟨.l125765, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12576f_eval :
    program.runBlock (dialect code) ⟨.l12576f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125788_eval :
    program.runBlock (dialect code) ⟨.l125788, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1275f0_eval :
    program.runBlock (dialect code) ⟨.l1275f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1275fc_eval :
    program.runBlock (dialect code) ⟨.l1275fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127610_eval :
    program.runBlock (dialect code) ⟨.l127610, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12761d_eval :
    program.runBlock (dialect code) ⟨.l12761d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127622_eval :
    program.runBlock (dialect code) ⟨.l127622, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127631_eval :
    program.runBlock (dialect code) ⟨.l127631, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12763c_eval :
    program.runBlock (dialect code) ⟨.l12763c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127648_eval :
    program.runBlock (dialect code) ⟨.l127648, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127662_eval :
    program.runBlock (dialect code) ⟨.l127662, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127670_eval :
    program.runBlock (dialect code) ⟨.l127670, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127690_eval :
    program.runBlock (dialect code) ⟨.l127690, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12769c_eval :
    program.runBlock (dialect code) ⟨.l12769c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1276aa_eval :
    program.runBlock (dialect code) ⟨.l1276aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1276d0_eval :
    program.runBlock (dialect code) ⟨.l1276d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1276d8_eval :
    program.runBlock (dialect code) ⟨.l1276d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1276fa_eval :
    program.runBlock (dialect code) ⟨.l1276fa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127704_eval :
    program.runBlock (dialect code) ⟨.l127704, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12770a_eval :
    program.runBlock (dialect code) ⟨.l12770a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12771b_eval :
    program.runBlock (dialect code) ⟨.l12771b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127726_eval :
    program.runBlock (dialect code) ⟨.l127726, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127b80_eval :
    program.runBlock (dialect code) ⟨.l127b80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127b89_eval :
    program.runBlock (dialect code) ⟨.l127b89, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127b9e_eval :
    program.runBlock (dialect code) ⟨.l127b9e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bad_eval :
    program.runBlock (dialect code) ⟨.l127bad, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bd3_eval :
    program.runBlock (dialect code) ⟨.l127bd3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bdd_eval :
    program.runBlock (dialect code) ⟨.l127bdd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127be1_eval :
    program.runBlock (dialect code) ⟨.l127be1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bf9_eval :
    program.runBlock (dialect code) ⟨.l127bf9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bfd_eval :
    program.runBlock (dialect code) ⟨.l127bfd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c04_eval :
    program.runBlock (dialect code) ⟨.l127c04, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c0d_eval :
    program.runBlock (dialect code) ⟨.l127c0d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c1e_eval :
    program.runBlock (dialect code) ⟨.l127c1e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c36_eval :
    program.runBlock (dialect code) ⟨.l127c36, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c41_eval :
    program.runBlock (dialect code) ⟨.l127c41, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c50_eval :
    program.runBlock (dialect code) ⟨.l127c50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c5f_eval :
    program.runBlock (dialect code) ⟨.l127c5f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c7e_eval :
    program.runBlock (dialect code) ⟨.l127c7e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127d50_eval :
    program.runBlock (dialect code) ⟨.l127d50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
