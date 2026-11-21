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

theorem rest_l1109b0_7 [Bindings] (code : CodeMap) :
    Rest (n := 326) code lifted (codeRange 0x1109b0 bytes_l1109b0) [(0, 234), (1, 303), (2, 281), (3, 311), (4, 324), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 317), (14, 320), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x110b70 bytes_l1109b0_7 b_l1109b0_7 := by
  have f140 : InstrSpec 0x110b70 [0x5D] (PopPre 0x110b70) (popR64Effect 0x110b70 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110b70 1 5).toInstrSpec (pop_r64_effect_step 0x110b70 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f141 : InstrSpec 0x110b71 [0xC3] (RetPre 0x110b71) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x110b71).toInstrSpec (ret_effect_step 0x110b71) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f140 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 327) f140 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 328) (ρ' := [(0, 234), (1, 303), (2, 281), (3, 311), (4, 327), (5, 326), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 317), (14, 320), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b71) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 329) (RestInside.out (n := 329) f141 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 330) f141 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 331) (ρ' := [(0, 234), (1, 303), (2, 281), (3, 311), (4, 330), (5, 326), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 317), (14, 320), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) f141 (by decide) rfl rfl rfl (by decide)

theorem rest_l1109b0_6 [Bindings] (code : CodeMap) :
    Rest (n := 286) code lifted (codeRange 0x1109b0 bytes_l1109b0) [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 284), (7, 270), (8, 105), (9, 102), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x110b35 bytes_l1109b0_6 b_l1109b0_6 := by
  have f120 : InstrSpec 0x110b35 [0x4D, 0x31, 0xF1] (fun s => s.RIP = 0x110b35) (xorR64R64Effect 0x110b35 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x110b35 9 14).toInstrSpec (xor_r64_r64_effect_step 0x110b35 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x110b38 [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x110b38) (negR64Effect 0x110b38 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x110b38 6).toInstrSpec (neg_r64_effect_step 0x110b38 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x110b3b [0x4C, 0x21, 0xCE] (fun s => s.RIP = 0x110b3b) (andR64R64Effect 0x110b3b 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110b3b 6 9).toInstrSpec (and_r64_r64_effect_step 0x110b3b 0x4c 0xce (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x110b3e [0x4C, 0x31, 0xF6] (fun s => s.RIP = 0x110b3e) (xorR64R64Effect 0x110b3e 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x110b3e 6 14).toInstrSpec (xor_r64_r64_effect_step 0x110b3e 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x110b41 [0x88, 0x0C, 0x24] (StorePre 0x110b41 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b41 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b41 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x110b41 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x110b41 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f125 : InstrSpec 0x110b44 [0x0F, 0xB6, 0x0C, 0x24] (LoadPre 0x110b44 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b44 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b44 4 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x110b44 4 1 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x110b44 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f126 : InstrSpec 0x110b48 [0x4D, 0x31, 0xF8] (fun s => s.RIP = 0x110b48) (xorR64R64Effect 0x110b48 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x110b48 8 15).toInstrSpec (xor_r64_r64_effect_step 0x110b48 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x110b4b [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x110b4b) (negR64Effect 0x110b4b 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x110b4b 1).toInstrSpec (neg_r64_effect_step 0x110b4b 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x110b4e [0x4C, 0x21, 0xC1] (fun s => s.RIP = 0x110b4e) (andR64R64Effect 0x110b4e 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110b4e 1 8).toInstrSpec (and_r64_r64_effect_step 0x110b4e 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x110b51 [0x4C, 0x31, 0xF9] (fun s => s.RIP = 0x110b51) (xorR64R64Effect 0x110b51 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x110b51 1 15).toInstrSpec (xor_r64_r64_effect_step 0x110b51 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x110b54 [0x48, 0x89, 0x38] (StorePre 0x110b54 3 (fun s => AddrMode.addr (.base 0 .none) s (0x110b54 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110b54 7 (.base 0 .none))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x110b54 7 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110b54 0x48 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f131 : InstrSpec 0x110b57 [0x48, 0x89, 0x50, 0x08] (StorePre 0x110b57 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x110b57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b57 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x110b57 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110b57 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f132 : InstrSpec 0x110b5b [0x48, 0x89, 0x70, 0x10] (StorePre 0x110b5b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x110b5b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b5b 6 (.base 0 (.d8 0x10)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x110b5b 6 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x110b5b 0x48 (by decide) 6 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f133 : InstrSpec 0x110b5f [0x48, 0x89, 0x48, 0x18] (StorePre 0x110b5f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x110b5f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b5f 1 (.base 0 (.d8 0x18)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x110b5f 1 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x110b5f 0x48 (by decide) 1 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f134 : InstrSpec 0x110b63 [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x110b63) (addR64Imm8Effect 0x110b63 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x110b63 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x110b63 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x110b67 [0x5B] (PopPre 0x110b67) (popR64Effect 0x110b67 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110b67 1 3).toInstrSpec (pop_r64_effect_step 0x110b67 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f136 : InstrSpec 0x110b68 [0x41, 0x5C] (PopPre 0x110b68) (popR64Effect 0x110b68 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110b68 2 12).toInstrSpec (pop_r64_rex_effect_step 0x110b68 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f137 : InstrSpec 0x110b6a [0x41, 0x5D] (PopPre 0x110b6a) (popR64Effect 0x110b6a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110b6a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x110b6a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f138 : InstrSpec 0x110b6c [0x41, 0x5E] (PopPre 0x110b6c) (popR64Effect 0x110b6c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110b6c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110b6c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f139 : InstrSpec 0x110b6e [0x41, 0x5F] (PopPre 0x110b6e) (popR64Effect 0x110b6e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110b6e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x110b6e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f120 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 284), (7, 270), (8, 105), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b38) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f121 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 288), (7, 270), (8, 105), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b3b) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f122 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 290), (7, 270), (8, 105), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b3e) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f123 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 105), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b41) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.exec (n := 294) (ρ' := [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 105), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b44) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f125 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 234), (1, 295), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 105), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b48) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f126 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 234), (1, 295), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b4b) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f127 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 300) (ρ' := [(0, 234), (1, 299), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b4e) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 301) (RestInside.out (n := 301) f128 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 302) (ρ' := [(0, 234), (1, 301), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b51) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 303) (RestInside.out (n := 303) f129 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 304) (ρ' := [(0, 234), (1, 303), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b54) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 305) (RestInside.exec (n := 305) (ρ' := [(0, 234), (1, 303), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b57) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 306) (RestInside.exec (n := 306) (ρ' := [(0, 234), (1, 303), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b5b) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 307) (RestInside.exec (n := 307) (ρ' := [(0, 234), (1, 303), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b5f) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 308) (RestInside.exec (n := 308) (ρ' := [(0, 234), (1, 303), (2, 281), (4, 65), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b63) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f134 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 234), (1, 303), (2, 281), (4, 309), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b67) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f135 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 312) f135 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 313) (ρ' := [(0, 234), (1, 303), (2, 281), (3, 311), (4, 312), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b68) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f136 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 315) f136 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 316) (ρ' := [(0, 234), (1, 303), (2, 281), (3, 311), (4, 315), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b6a) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 317) (RestInside.out (n := 317) f137 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 318) f137 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 319) (ρ' := [(0, 234), (1, 303), (2, 281), (3, 311), (4, 318), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 317), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b6c) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f138 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 321) f138 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 322) (ρ' := [(0, 234), (1, 303), (2, 281), (3, 311), (4, 321), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 317), (14, 320), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b6e) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f139 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 324) f139 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 325) (ρ' := [(0, 234), (1, 303), (2, 281), (3, 311), (4, 324), (5, 219), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 317), (14, 320), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b70) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1109b0_7 code

theorem rest_l1109b0_5 [Bindings] (code : CodeMap) :
    Rest (n := 252) code lifted (codeRange 0x1109b0 bytes_l1109b0) [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 250), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]
      42 0x110af2 bytes_l1109b0_5 b_l1109b0_5 := by
  have f100 : InstrSpec 0x110af2 [0x80, 0x44, 0x24, 0x0F, 0xFF] (StorePre 0x110af2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x110af2 + BitVec.ofNat 64 5)) 1) (addM8Imm8Effect 0x110af2 5 (.sib 4 none 0 (.d8 0xf)) 0xff)
      [.gpr 4] [] [.flags, .rip] :=
    (addM8Imm8Effect_footprint 0x110af2 5 (.sib 4 none 0 (.d8 0xf)) 0xff).toInstrSpec (add_m8_imm8_effect_step 0x110af2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) 0xff) (StorePre.of_addr rfl)
  have f101 : InstrSpec 0x110af7 [0x48, 0x11, 0xDF] (fun s => s.RIP = 0x110af7) (atFlags StatusFlags.CF (adcR64R64Effect 0x110af7 7 3))
      [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x110af7 7 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x110af7 0x48 0xdf c (by decide) (by decide))) pre_rip
  have f102 : InstrSpec 0x110afa [0x48, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x110afa) (shrR64Effect 0x110afa 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x110afa 4 7 63).toInstrSpec (shr_r64_imm8_effect_step 0x110afa 0x48 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x110afe [0x48, 0x89, 0x3C, 0x24] (StorePre 0x110afe 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110afe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110afe 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110afe 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110afe 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f104 : InstrSpec 0x110b02 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x110b02) (movR64R64Effect 0x110b02 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x110b02 7 4).toInstrSpec (mov_r64_r64_effect_step 0x110b02 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x110b05 [0x88, 0x0C, 0x24] (StorePre 0x110b05 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b05 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b05 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x110b05 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x110b05 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f106 : InstrSpec 0x110b08 [0x48, 0x89, 0xE3] (fun s => s.RIP = 0x110b08) (movR64R64Effect 0x110b08 3 4)
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x110b08 3 4).toInstrSpec (mov_r64_r64_effect_step 0x110b08 0x48 0xe3 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x110b0b [0x0F, 0xB6, 0x3C, 0x24] (LoadPre 0x110b0b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b0b + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b0b 4 7 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x110b0b 4 7 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x110b0b 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f108 : InstrSpec 0x110b0f [0x49, 0x31, 0xD3] (fun s => s.RIP = 0x110b0f) (xorR64R64Effect 0x110b0f 11 2)
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x110b0f 11 2).toInstrSpec (xor_r64_r64_effect_step 0x110b0f 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x110b12 [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x110b12) (negR64Effect 0x110b12 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x110b12 7).toInstrSpec (neg_r64_effect_step 0x110b12 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x110b15 [0x4C, 0x21, 0xDF] (fun s => s.RIP = 0x110b15) (andR64R64Effect 0x110b15 7 11)
      [.gpr 7, .gpr 11] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110b15 7 11).toInstrSpec (and_r64_r64_effect_step 0x110b15 0x4c 0xdf (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x110b18 [0x48, 0x31, 0xD7] (fun s => s.RIP = 0x110b18) (xorR64R64Effect 0x110b18 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x110b18 7 2).toInstrSpec (xor_r64_r64_effect_step 0x110b18 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x110b1b [0x88, 0x0C, 0x24] (StorePre 0x110b1b 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b1b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b1b 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x110b1b 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x110b1b 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f113 : InstrSpec 0x110b1e [0x0F, 0xB6, 0x14, 0x24] (LoadPre 0x110b1e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b1e + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b1e 4 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x110b1e 4 2 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x110b1e 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f114 : InstrSpec 0x110b22 [0x49, 0x31, 0xF2] (fun s => s.RIP = 0x110b22) (xorR64R64Effect 0x110b22 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x110b22 10 6).toInstrSpec (xor_r64_r64_effect_step 0x110b22 0x49 0xf2 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x110b25 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x110b25) (negR64Effect 0x110b25 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x110b25 2).toInstrSpec (neg_r64_effect_step 0x110b25 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x110b28 [0x4C, 0x21, 0xD2] (fun s => s.RIP = 0x110b28) (andR64R64Effect 0x110b28 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110b28 2 10).toInstrSpec (and_r64_r64_effect_step 0x110b28 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x110b2b [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x110b2b) (xorR64R64Effect 0x110b2b 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x110b2b 2 6).toInstrSpec (xor_r64_r64_effect_step 0x110b2b 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x110b2e [0x88, 0x0C, 0x24] (StorePre 0x110b2e 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b2e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b2e 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x110b2e 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x110b2e 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f119 : InstrSpec 0x110b31 [0x0F, 0xB6, 0x34, 0x24] (LoadPre 0x110b31 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b31 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b31 4 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x110b31 4 6 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x110b31 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f100 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 250), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (16, 252), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110af7) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f101 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 254), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110afa) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f102 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 256), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110afe) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.exec (n := 258) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 256), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b02) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 259) (RestInside.exec (n := 259) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b05) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 260) (RestInside.exec (n := 260) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b08) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 261) (RestInside.exec (n := 261) (ρ' := [(0, 234), (1, 240), (2, 117), (4, 65), (5, 219), (6, 149), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b0b) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f107 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 234), (1, 240), (2, 117), (4, 65), (5, 219), (6, 149), (7, 262), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b0f) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f108 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 234), (1, 240), (2, 117), (4, 65), (5, 219), (6, 149), (7, 262), (8, 105), (9, 102), (10, 99), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b12) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f109 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 234), (1, 240), (2, 117), (4, 65), (5, 219), (6, 149), (7, 266), (8, 105), (9, 102), (10, 99), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b15) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f110 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 234), (1, 240), (2, 117), (4, 65), (5, 219), (6, 149), (7, 268), (8, 105), (9, 102), (10, 99), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b18) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f111 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 234), (1, 240), (2, 117), (4, 65), (5, 219), (6, 149), (7, 270), (8, 105), (9, 102), (10, 99), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b1b) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.exec (n := 272) (ρ' := [(0, 234), (1, 240), (2, 117), (4, 65), (5, 219), (6, 149), (7, 270), (8, 105), (9, 102), (10, 99), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b1e) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f113 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 234), (1, 240), (2, 273), (4, 65), (5, 219), (6, 149), (7, 270), (8, 105), (9, 102), (10, 99), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b22) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f114 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 234), (1, 240), (2, 273), (4, 65), (5, 219), (6, 149), (7, 270), (8, 105), (9, 102), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b25) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f115 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 234), (1, 240), (2, 277), (4, 65), (5, 219), (6, 149), (7, 270), (8, 105), (9, 102), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b28) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f116 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 234), (1, 240), (2, 279), (4, 65), (5, 219), (6, 149), (7, 270), (8, 105), (9, 102), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b2b) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.out (n := 281) f117 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 282) (ρ' := [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 149), (7, 270), (8, 105), (9, 102), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b2e) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 283) (RestInside.exec (n := 283) (ρ' := [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 149), (7, 270), (8, 105), (9, 102), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b31) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f119 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 234), (1, 240), (2, 281), (4, 65), (5, 219), (6, 284), (7, 270), (8, 105), (9, 102), (10, 275), (11, 264), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b35) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1109b0_6 code

theorem rest_l1109b0_4 [Bindings] (code : CodeMap) :
    Rest (n := 215) code lifted (codeRange 0x1109b0 bytes_l1109b0) [(1, 203), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 213), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]
      62 0x110ab1 bytes_l1109b0_4 b_l1109b0_4 := by
  have f80 : InstrSpec 0x110ab1 [0x49, 0xF7, 0xD5] (fun s => s.RIP = 0x110ab1) (notR64Effect 0x110ab1 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (notR64Effect_footprint 0x110ab1 13).toInstrSpec (not_r64_effect_step 0x110ab1 0x49 0xd5 (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x110ab4 [0x48, 0x89, 0xCD] (fun s => s.RIP = 0x110ab4) (movR64R64Effect 0x110ab4 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x110ab4 5 1).toInstrSpec (mov_r64_r64_effect_step 0x110ab4 0x48 0xcd (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x110ab7 [0x4C, 0x21, 0xED] (fun s => s.RIP = 0x110ab7) (andR64R64Effect 0x110ab7 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110ab7 5 13).toInstrSpec (and_r64_r64_effect_step 0x110ab7 0x4c 0xed (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x110aba [0x49, 0x09, 0xCD] (fun s => s.RIP = 0x110aba) (orR64R64Effect 0x110aba 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110aba 13 1).toInstrSpec (or_r64_r64_effect_step 0x110aba 0x49 0xcd (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x110abd [0x4D, 0x21, 0xFD] (fun s => s.RIP = 0x110abd) (andR64R64Effect 0x110abd 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110abd 13 15).toInstrSpec (and_r64_r64_effect_step 0x110abd 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x110ac0 [0x49, 0x09, 0xED] (fun s => s.RIP = 0x110ac0) (orR64R64Effect 0x110ac0 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110ac0 13 5).toInstrSpec (or_r64_r64_effect_step 0x110ac0 0x49 0xed (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x110ac3 [0x49, 0xC1, 0xED, 0x3F] (fun s => s.RIP = 0x110ac3) (shrR64Effect 0x110ac3 4 13 63)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x110ac3 4 13 63).toInstrSpec (shr_r64_imm8_effect_step 0x110ac3 0x49 0xed 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x110ac7 [0x4C, 0x89, 0x2C, 0x24] (StorePre 0x110ac7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ac7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110ac7 13 (.sib 4 none 0 .none))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110ac7 13 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110ac7 0x4c (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f88 : InstrSpec 0x110acb [0x45, 0x31, 0xED] (fun s => s.RIP = 0x110acb) (xorR32R32Effect 0x110acb 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110acb 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x110acb 0x45 0xed (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x110ace [0x4C, 0x2B, 0x2C, 0x24] (LoadPre 0x110ace (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ace + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110ace 13 (.sib 4 none 0 .none))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110ace 13 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x110ace 0x4c (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f90 : InstrSpec 0x110ad2 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x110ad2) (movR64R64Effect 0x110ad2 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110ad2 0 7).toInstrSpec (mov_r64_r64_effect_step 0x110ad2 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x110ad5 [0x4D, 0x85, 0xE4] (fun s => s.RIP = 0x110ad5) (testR64R64Effect 0x110ad5 12 12)
      [.gpr 12, .gpr 12] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x110ad5 12 12).toInstrSpec (test_r64_r64_effect_step 0x110ad5 0x4d 0xe4 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x110ad8 [0x0F, 0x94, 0xC1] (fun s => s.RIP = 0x110ad8) (atFlags (condHolds 4) (setccR8Effect 0x110ad8 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x110ad8 3 1 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x110ad8 4 0xc1 (by decide) (by decide) c)) pre_rip
  have f93 : InstrSpec 0x110adb [0x44, 0x20, 0xE9] (fun s => s.RIP = 0x110adb) (andR8R8Effect 0x110adb 3 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (andR8R8Effect_footprint 0x110adb 3 1 13).toInstrSpec (and_r8_r8_rex_effect_step 0x110adb 0x44 0xe9 (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x110ade [0x88, 0x0C, 0x24] (StorePre 0x110ade 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ade + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110ade 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x110ade 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x110ade 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f95 : InstrSpec 0x110ae1 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x110ae1) (movR64R64Effect 0x110ae1 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x110ae1 7 4).toInstrSpec (mov_r64_r64_effect_step 0x110ae1 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x110ae4 [0x0F, 0xB6, 0x3C, 0x24] (LoadPre 0x110ae4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ae4 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110ae4 4 7 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x110ae4 4 7 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x110ae4 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x110ae8 [0x48, 0xFF, 0xCF] (fun s => s.RIP = 0x110ae8) (decR64Effect 0x110ae8 7)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (decR64Effect_footprint 0x110ae8 7).toInstrSpec (dec_r64_effect_step 0x110ae8 0x48 0xcf (by decide) (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x110aeb [0x4C, 0x21, 0xEF] (fun s => s.RIP = 0x110aeb) (andR64R64Effect 0x110aeb 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110aeb 7 13).toInstrSpec (and_r64_r64_effect_step 0x110aeb 0x4c 0xef (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x110aee [0x48, 0xC1, 0xFF, 0x3F] (fun s => s.RIP = 0x110aee) (sarR64Effect 0x110aee 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (sarR64Effect_footprint 0x110aee 4 7 63).toInstrSpec (sar_r64_imm8_effect_step 0x110aee 0x48 0xff 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f80 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 215), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ab4) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f81 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 217), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 215), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ab7) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f82 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 215), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110aba) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f83 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 221), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110abd) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f84 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 223), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ac0) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f85 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 225), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ac3) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f86 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 227), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ac7) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.exec (n := 229) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 227), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110acb) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f88 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 230), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ace) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f89 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ad2) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 234), (1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ad5) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f91 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 234), (1, 203), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (19, 236), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ad8) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f92 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 234), (1, 238), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (19, 236), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110adb) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ade) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.exec (n := 242) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ae1) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 243) (RestInside.exec (n := 243) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ae4) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f96 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 244), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ae8) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f97 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 246), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110aeb) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f98 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 248), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110aee) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f99 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 234), (1, 240), (2, 117), (3, 97), (4, 65), (5, 219), (6, 149), (7, 250), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 232), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110af2) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1109b0_5 code

theorem rest_l1109b0_3 [Bindings] (code : CodeMap) :
    Rest (n := 176) code lifted (codeRange 0x1109b0 bytes_l1109b0) [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 174), (14, 170), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]
      82 0x110a6f bytes_l1109b0_3 b_l1109b0_3 := by
  have f60 : InstrSpec 0x110a6f [0x49, 0x29, 0xED] (fun s => s.RIP = 0x110a6f) (subR64R64Effect 0x110a6f 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110a6f 13 5).toInstrSpec (sub_r64_r64_effect_step 0x110a6f 0x49 0xed (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x110a72 [0x49, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x110a72) (sarR64Effect 0x110a72 4 14 63)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (sarR64Effect_footprint 0x110a72 4 14 63).toInstrSpec (sar_r64_imm8_effect_step 0x110a72 0x49 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x110a76 [0x4D, 0x01, 0xEE] (fun s => s.RIP = 0x110a76) (addR64R64Effect 0x110a76 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110a76 14 13).toInstrSpec (add_r64_r64_effect_step 0x110a76 0x4d 0xee (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x110a79 [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x110a79) (movR64R64Effect 0x110a79 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x110a79 13 9).toInstrSpec (mov_r64_r64_effect_step 0x110a79 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x110a7c [0x49, 0xF7, 0xD5] (fun s => s.RIP = 0x110a7c) (notR64Effect 0x110a7c 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (notR64Effect_footprint 0x110a7c 13).toInstrSpec (not_r64_effect_step 0x110a7c 0x49 0xd5 (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x110a7f [0x49, 0x89, 0xEF] (fun s => s.RIP = 0x110a7f) (movR64R64Effect 0x110a7f 15 5)
      [.gpr 5] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110a7f 15 5).toInstrSpec (mov_r64_r64_effect_step 0x110a7f 0x49 0xef (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x110a82 [0x4D, 0x21, 0xEF] (fun s => s.RIP = 0x110a82) (andR64R64Effect 0x110a82 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110a82 15 13).toInstrSpec (and_r64_r64_effect_step 0x110a82 0x4d 0xef (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x110a85 [0x49, 0x09, 0xED] (fun s => s.RIP = 0x110a85) (orR64R64Effect 0x110a85 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110a85 13 5).toInstrSpec (or_r64_r64_effect_step 0x110a85 0x49 0xed (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x110a88 [0x4D, 0x21, 0xF5] (fun s => s.RIP = 0x110a88) (andR64R64Effect 0x110a88 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110a88 13 14).toInstrSpec (and_r64_r64_effect_step 0x110a88 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x110a8b [0x4D, 0x09, 0xFD] (fun s => s.RIP = 0x110a8b) (orR64R64Effect 0x110a8b 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110a8b 13 15).toInstrSpec (or_r64_r64_effect_step 0x110a8b 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x110a8e [0x49, 0xC1, 0xED, 0x3F] (fun s => s.RIP = 0x110a8e) (shrR64Effect 0x110a8e 4 13 63)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x110a8e 4 13 63).toInstrSpec (shr_r64_imm8_effect_step 0x110a8e 0x49 0xed 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x110a92 [0x4C, 0x89, 0x2C, 0x24] (StorePre 0x110a92 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a92 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a92 13 (.sib 4 none 0 .none))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110a92 13 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110a92 0x4c (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x110a96 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x110a96) (xorR32R32Effect 0x110a96 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110a96 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x110a96 0x45 0xff (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x110a99 [0x4C, 0x2B, 0x3C, 0x24] (LoadPre 0x110a99 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a99 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a99 15 (.sib 4 none 0 .none))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110a99 15 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x110a99 0x4c (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x110a9d [0x48, 0x8B, 0x49, 0x18] (LoadPre 0x110a9d (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x110a9d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a9d 1 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x110a9d 1 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110a9d 0x48 (by decide) 1 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f75 : InstrSpec 0x110aa1 [0x4D, 0x89, 0xC5] (fun s => s.RIP = 0x110aa1) (movR64R64Effect 0x110aa1 13 8)
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x110aa1 13 8).toInstrSpec (mov_r64_r64_effect_step 0x110aa1 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x110aa4 [0x49, 0x29, 0xCD] (fun s => s.RIP = 0x110aa4) (subR64R64Effect 0x110aa4 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110aa4 13 1).toInstrSpec (sub_r64_r64_effect_step 0x110aa4 0x49 0xcd (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x110aa7 [0x49, 0xC1, 0xFF, 0x3F] (fun s => s.RIP = 0x110aa7) (sarR64Effect 0x110aa7 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (sarR64Effect_footprint 0x110aa7 4 15 63).toInstrSpec (sar_r64_imm8_effect_step 0x110aa7 0x49 0xff 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x110aab [0x4D, 0x01, 0xEF] (fun s => s.RIP = 0x110aab) (addR64R64Effect 0x110aab 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110aab 15 13).toInstrSpec (add_r64_r64_effect_step 0x110aab 0x4d 0xef (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x110aae [0x4D, 0x89, 0xC5] (fun s => s.RIP = 0x110aae) (movR64R64Effect 0x110aae 13 8)
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x110aae 13 8).toInstrSpec (mov_r64_r64_effect_step 0x110aae 0x4d 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f60 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 176), (14, 170), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a72) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f61 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 176), (14, 178), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a76) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f62 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 176), (14, 180), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a79) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f63 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 182), (14, 180), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a7c) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f64 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 184), (14, 180), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a7f) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f65 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 184), (14, 180), (15, 186), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a82) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f66 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 184), (14, 180), (15, 188), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a85) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f67 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 190), (14, 180), (15, 188), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a88) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f68 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 192), (14, 180), (15, 188), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a8b) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f69 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 194), (14, 180), (15, 188), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a8e) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f70 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 196), (14, 180), (15, 188), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a92) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.exec (n := 198) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 196), (14, 180), (15, 188), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a96) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f72 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 196), (14, 180), (15, 199), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a99) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f73 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 196), (14, 180), (15, 201), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a9d) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f74 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 196), (14, 180), (15, 201), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110aa1) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f75 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 205), (14, 180), (15, 201), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110aa4) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f76 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 207), (14, 180), (15, 201), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110aa7) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f77 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 207), (14, 180), (15, 209), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110aab) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f78 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 207), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110aae) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f79 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(1, 203), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 213), (14, 180), (15, 211), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ab1) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1109b0_4 code

theorem rest_l1109b0_2 [Bindings] (code : CodeMap) :
    Rest (n := 137) code lifted (codeRange 0x1109b0 bytes_l1109b0) [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 133), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      102 0x110a2d bytes_l1109b0_2 b_l1109b0_2 := by
  have f40 : InstrSpec 0x110a2d [0x31, 0xF6] (fun s => s.RIP = 0x110a2d) (xorR32R32Effect 0x110a2d 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110a2d 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x110a2d 0xf6 (by decide)) pre_rip
  have f41 : InstrSpec 0x110a2f [0x48, 0x2B, 0x34, 0x24] (LoadPre 0x110a2f (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a2f + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a2f 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110a2f 6 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x110a2f 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x110a33 [0x4C, 0x8B, 0x71, 0x08] (LoadPre 0x110a33 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x110a33 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a33 14 (.base 1 (.d8 0x8)))
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x110a33 14 (.base 1 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110a33 0x4c (by decide) 6 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x110a37 [0x4D, 0x89, 0xD7] (fun s => s.RIP = 0x110a37) (movR64R64Effect 0x110a37 15 10)
      [.gpr 10] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110a37 15 10).toInstrSpec (mov_r64_r64_effect_step 0x110a37 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x110a3a [0x4D, 0x29, 0xF7] (fun s => s.RIP = 0x110a3a) (subR64R64Effect 0x110a3a 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110a3a 15 14).toInstrSpec (sub_r64_r64_effect_step 0x110a3a 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x110a3d [0x48, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x110a3d) (sarR64Effect 0x110a3d 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR64Effect_footprint 0x110a3d 4 6 63).toInstrSpec (sar_r64_imm8_effect_step 0x110a3d 0x48 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x110a41 [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x110a41) (addR64R64Effect 0x110a41 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110a41 6 15).toInstrSpec (add_r64_r64_effect_step 0x110a41 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x110a44 [0x4D, 0x89, 0xD7] (fun s => s.RIP = 0x110a44) (movR64R64Effect 0x110a44 15 10)
      [.gpr 10] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110a44 15 10).toInstrSpec (mov_r64_r64_effect_step 0x110a44 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x110a47 [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x110a47) (notR64Effect 0x110a47 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x110a47 15).toInstrSpec (not_r64_effect_step 0x110a47 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x110a4a [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x110a4a) (movR64R64Effect 0x110a4a 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x110a4a 13 14).toInstrSpec (mov_r64_r64_effect_step 0x110a4a 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x110a4d [0x4D, 0x21, 0xFD] (fun s => s.RIP = 0x110a4d) (andR64R64Effect 0x110a4d 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110a4d 13 15).toInstrSpec (and_r64_r64_effect_step 0x110a4d 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x110a50 [0x4D, 0x09, 0xF7] (fun s => s.RIP = 0x110a50) (orR64R64Effect 0x110a50 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110a50 15 14).toInstrSpec (or_r64_r64_effect_step 0x110a50 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x110a53 [0x49, 0x21, 0xF7] (fun s => s.RIP = 0x110a53) (andR64R64Effect 0x110a53 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110a53 15 6).toInstrSpec (and_r64_r64_effect_step 0x110a53 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x110a56 [0x4D, 0x09, 0xEF] (fun s => s.RIP = 0x110a56) (orR64R64Effect 0x110a56 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110a56 15 13).toInstrSpec (or_r64_r64_effect_step 0x110a56 0x4d 0xef (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x110a59 [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x110a59) (shrR64Effect 0x110a59 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x110a59 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x110a59 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x110a5d [0x4C, 0x89, 0x3C, 0x24] (StorePre 0x110a5d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a5d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a5d 15 (.sib 4 none 0 .none))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110a5d 15 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110a5d 0x4c (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x110a61 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x110a61) (xorR32R32Effect 0x110a61 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110a61 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x110a61 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x110a64 [0x4C, 0x2B, 0x34, 0x24] (LoadPre 0x110a64 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a64 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a64 14 (.sib 4 none 0 .none))
      [.gpr 14, .gpr 4] [] [.reg 14, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110a64 14 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x110a64 0x4c (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x110a68 [0x48, 0x8B, 0x69, 0x10] (LoadPre 0x110a68 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x110a68 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a68 5 (.base 1 (.d8 0x10)))
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x110a68 5 (.base 1 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110a68 0x48 (by decide) 5 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x110a6c [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x110a6c) (movR64R64Effect 0x110a6c 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x110a6c 13 9).toInstrSpec (mov_r64_r64_effect_step 0x110a6c 0x4d 0xcd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 137), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a2f) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f41 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 139), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a33) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f42 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 139), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 141), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a37) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f43 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 139), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 141), (15, 143), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a3a) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 139), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 141), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a3d) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f45 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 147), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 141), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a41) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 141), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a44) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f47 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 141), (15, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a47) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f48 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 141), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a4a) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f49 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 155), (14, 141), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a4d) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f50 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 141), (15, 153), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a50) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f51 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 141), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a53) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f52 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 141), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a56) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f53 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 141), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a59) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f54 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 141), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a5d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.exec (n := 167) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 141), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a61) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f56 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 168), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a64) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f57 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 170), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a68) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f58 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 157), (14, 170), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a6c) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f59 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 172), (6, 149), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 174), (14, 170), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a6f) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1109b0_3 code

theorem rest_l1109b0_1 [Bindings] (code : CodeMap) :
    Rest (n := 97) code lifted (codeRange 0x1109b0 bytes_l1109b0) [(0, 95), (1, 1), (2, 2), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 83), (10, 76), (11, 71), (12, 12), (13, 13), (14, 92), (15, 15), (16, 93), (22, 22), (39, 39), (50, 50), (51, 51)]
      122 0x1109eb bytes_l1109b0_1 b_l1109b0_1 := by
  have f20 : InstrSpec 0x1109eb [0x0F, 0x92, 0xC3] (fun s => s.RIP = 0x1109eb) (atFlags (condHolds 2) (setccR8Effect 0x1109eb 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x1109eb 3 3 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1109eb 2 0xc3 (by decide) (by decide) c)) pre_rip
  have f21 : InstrSpec 0x1109ee [0x4C, 0x03, 0x52, 0x08] (LoadPre 0x1109ee (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1109ee + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109ee 10 (.base 2 (.d8 0x8)))
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (addR64M64Effect_footprint 0x1109ee 10 (.base 2 (.d8 0x8))).toInstrSpec (add_r64_m64_effect_step 0x1109ee 0x4c (by decide) 2 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1109f2 [0x49, 0x11, 0xC1] (fun s => s.RIP = 0x1109f2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f2 9 0))
      [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1109f2 9 0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1109f2 0x49 0xc1 c (by decide) (by decide))) pre_rip
  have f23 : InstrSpec 0x1109f5 [0x4D, 0x11, 0xF0] (fun s => s.RIP = 0x1109f5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f5 8 14))
      [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1109f5 8 14).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1109f5 0x4d 0xf0 c (by decide) (by decide))) pre_rip
  have f24 : InstrSpec 0x1109f8 [0x0F, 0x92, 0x44, 0x24, 0x0F] (StorePre 0x1109f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1109f8 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 2) (setccM8Effect 0x1109f8 5 (.sib 4 none 0 (.d8 0xf))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x1109f8 5 (.sib 4 none 0 (.d8 0xf)) 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1109f8 2 0 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x1109fd [0x49, 0x89, 0xDC] (fun s => s.RIP = 0x1109fd) (movR64R64Effect 0x1109fd 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1109fd 12 3).toInstrSpec (mov_r64_r64_effect_step 0x1109fd 0x49 0xdc (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x110a00 [0x49, 0x83, 0xD4, 0x00] (fun s => s.RIP = 0x110a00) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110a00 12 0x0))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x110a00 12 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x110a00 0x49 0xd4 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f27 : InstrSpec 0x110a04 [0x48, 0x8B, 0x01] (LoadPre 0x110a04 (fun s => AddrMode.addr (.base 1 .none) s (0x110a04 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110a04 0 (.base 1 .none))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110a04 0 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110a04 0x48 (by decide) 0 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x110a07 [0x4C, 0x89, 0xDA] (fun s => s.RIP = 0x110a07) (movR64R64Effect 0x110a07 2 11)
      [.gpr 11] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x110a07 2 11).toInstrSpec (mov_r64_r64_effect_step 0x110a07 0x4c 0xda (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x110a0a [0x48, 0x29, 0xC2] (fun s => s.RIP = 0x110a0a) (subR64R64Effect 0x110a0a 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110a0a 2 0).toInstrSpec (sub_r64_r64_effect_step 0x110a0a 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x110a0d [0x4C, 0x89, 0xDE] (fun s => s.RIP = 0x110a0d) (movR64R64Effect 0x110a0d 6 11)
      [.gpr 11] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x110a0d 6 11).toInstrSpec (mov_r64_r64_effect_step 0x110a0d 0x4c 0xde (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x110a10 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x110a10) (notR64Effect 0x110a10 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x110a10 6).toInstrSpec (not_r64_effect_step 0x110a10 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x110a13 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x110a13) (movR64R64Effect 0x110a13 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x110a13 14 0).toInstrSpec (mov_r64_r64_effect_step 0x110a13 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x110a16 [0x49, 0x21, 0xF6] (fun s => s.RIP = 0x110a16) (andR64R64Effect 0x110a16 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110a16 14 6).toInstrSpec (and_r64_r64_effect_step 0x110a16 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x110a19 [0x48, 0x09, 0xC6] (fun s => s.RIP = 0x110a19) (orR64R64Effect 0x110a19 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110a19 6 0).toInstrSpec (or_r64_r64_effect_step 0x110a19 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x110a1c [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x110a1c) (andR64R64Effect 0x110a1c 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110a1c 6 2).toInstrSpec (and_r64_r64_effect_step 0x110a1c 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x110a1f [0x4C, 0x09, 0xF6] (fun s => s.RIP = 0x110a1f) (orR64R64Effect 0x110a1f 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110a1f 6 14).toInstrSpec (or_r64_r64_effect_step 0x110a1f 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x110a22 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x110a22) (shrR64Effect 0x110a22 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x110a22 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x110a22 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x110a26 [0x48, 0x89, 0x34, 0x24] (StorePre 0x110a26 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a26 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a26 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110a26 6 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110a26 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x110a2a [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x110a2a) (movR64R64Effect 0x110a2a 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110a2a 0 4).toInstrSpec (mov_r64_r64_effect_step 0x110a2a 0x48 0xe0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f20 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 83), (10, 76), (11, 71), (12, 12), (13, 13), (14, 92), (15, 15), (16, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109ee) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f21 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f21 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 83), (10, 99), (11, 71), (12, 12), (13, 13), (14, 92), (15, 15), (16, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109f2) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 103) f22 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1109f2 9 0 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 102), (10, 99), (11, 71), (12, 12), (13, 13), (14, 92), (15, 15), (16, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109f5) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 106) f23 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1109f5 8 14 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 107) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 12), (13, 13), (14, 92), (15, 15), (16, 106), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109f8) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 12), (13, 13), (14, 92), (15, 15), (16, 106), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109fd) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f25 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 109), (13, 13), (14, 92), (15, 15), (16, 106), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a00) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f26 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 92), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a04) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 1), (2, 2), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 92), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a07) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 113), (1, 1), (2, 115), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 92), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a0a) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 6), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 92), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a0d) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f30 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 119), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 92), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a10) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 121), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 92), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a13) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f32 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 121), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 123), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a16) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f33 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 121), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a19) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f34 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 127), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a1c) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f35 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 129), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a1f) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 131), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a22) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f37 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 133), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a26) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 113), (1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 133), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a2a) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(1, 1), (2, 117), (3, 97), (4, 65), (5, 5), (6, 133), (7, 7), (8, 105), (9, 102), (10, 99), (11, 71), (12, 111), (13, 13), (14, 125), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110a2d) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1109b0_2 code

theorem rest_l1109b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1109b0 bytes_l1109b0) (entryMap (live .l1109b0))
      142 0x1109b0 bytes_l1109b0 b_l1109b0 := by
  have f0 : InstrSpec 0x1109b0 [0x55] (PushPre 0x1109b0 1) (pushR64Effect 0x1109b0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1109b0 1 5).toInstrSpec (push_r64_effect_step 0x1109b0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1109b1 [0x41, 0x57] (PushPre 0x1109b1 2) (pushR64Effect 0x1109b1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1109b1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1109b1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1109b3 [0x41, 0x56] (PushPre 0x1109b3 2) (pushR64Effect 0x1109b3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1109b3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1109b3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1109b5 [0x41, 0x55] (PushPre 0x1109b5 2) (pushR64Effect 0x1109b5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1109b5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1109b5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1109b7 [0x41, 0x54] (PushPre 0x1109b7 2) (pushR64Effect 0x1109b7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1109b7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1109b7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1109b9 [0x53] (PushPre 0x1109b9 1) (pushR64Effect 0x1109b9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1109b9 1 3).toInstrSpec (push_r64_effect_step 0x1109b9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1109ba [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x1109ba) (subR64Imm8Effect 0x1109ba 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1109ba 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x1109ba 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1109be [0x4C, 0x8B, 0x1A] (LoadPre 0x1109be (fun s => AddrMode.addr (.base 2 .none) s (0x1109be + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1109be 11 (.base 2 .none))
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1109be 11 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1109be 0x4c (by decide) 3 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1109c1 [0x4C, 0x8B, 0x4A, 0x10] (LoadPre 0x1109c1 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1109c1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109c1 9 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1109c1 9 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1109c1 0x4c (by decide) 1 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1109c5 [0x4C, 0x03, 0x1E] (LoadPre 0x1109c5 (fun s => AddrMode.addr (.base 6 .none) s (0x1109c5 + BitVec.ofNat 64 3)) 8) (addR64M64Effect 0x1109c5 11 (.base 6 .none))
      [.gpr 11, .gpr 6] [] [.reg 11, .flags, .rip] :=
    (addR64M64Effect_footprint 0x1109c5 11 (.base 6 .none)).toInstrSpec (add_r64_m64_effect_step 0x1109c5 0x4c (by decide) 3 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1109c8 [0x4C, 0x8B, 0x56, 0x08] (LoadPre 0x1109c8 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1109c8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109c8 10 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1109c8 10 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1109c8 0x4c (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1109cc [0x49, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x1109cc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1109cc 10 0x0))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1109cc 10 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1109cc 0x49 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f12 : InstrSpec 0x1109d0 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x1109d0) (atFlags (condHolds 2) (setccR8Effect 0x1109d0 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1109d0 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1109d0 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f13 : InstrSpec 0x1109d3 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1109d3) (xorR32R32Effect 0x1109d3 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1109d3 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1109d3 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1109d6 [0x4C, 0x03, 0x4E, 0x10] (LoadPre 0x1109d6 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1109d6 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109d6 9 (.base 6 (.d8 0x10)))
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (addR64M64Effect_footprint 0x1109d6 9 (.base 6 (.d8 0x10))).toInstrSpec (add_r64_m64_effect_step 0x1109d6 0x4c (by decide) 1 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1109da [0x41, 0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x1109da) (atFlags (condHolds 2) (setccR8Effect 0x1109da 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x1109da 4 8 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1109da 2 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f16 : InstrSpec 0x1109de [0x4C, 0x8B, 0x72, 0x18] (LoadPre 0x1109de (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1109de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109de 14 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1109de 14 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1109de 0x4c (by decide) 6 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1109e2 [0x31, 0xDB] (fun s => s.RIP = 0x1109e2) (xorR32R32Effect 0x1109e2 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1109e2 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x1109e2 0xdb (by decide)) pre_rip
  have f18 : InstrSpec 0x1109e4 [0x4C, 0x03, 0x76, 0x18] (LoadPre 0x1109e4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1109e4 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109e4 14 (.base 6 (.d8 0x18)))
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (addR64M64Effect_footprint 0x1109e4 14 (.base 6 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x1109e4 0x4c (by decide) 6 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1109e8 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x1109e8) (movzxR32R8Effect 0x1109e8 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x1109e8 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x1109e8 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109c1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109c5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109c8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 74), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109cc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 77) f11 .CF (fun _ => rfl) (adcR64Imm8Effect_fresh 0x1109cc 10 0x0 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 76), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (16, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109d0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 76), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (16, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109d3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 81), (9, 69), (10, 76), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109d6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f14 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 85) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 81), (9, 83), (10, 76), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (16, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109da) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 83), (10, 76), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (16, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109de) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f16 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 83), (10, 76), (11, 71), (12, 12), (13, 13), (14, 88), (15, 15), (16, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109e2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f17 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 83), (10, 76), (11, 71), (12, 12), (13, 13), (14, 88), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109e4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 93) f18 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 94) (ρ' := [(0, 79), (1, 1), (2, 2), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 83), (10, 76), (11, 71), (12, 12), (13, 13), (14, 92), (15, 15), (16, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109e8) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 83), (10, 76), (11, 71), (12, 12), (13, 13), (14, 92), (15, 15), (16, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109eb) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1109b0_1 code

theorem block_l1109b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1109b0 :=
  Rest.liftedBlock (rest_l1109b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1109b0 x hx)

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

theorem_by block_l1109b0_eval :
    program.runBlock (dialect code) ⟨.l1109b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
