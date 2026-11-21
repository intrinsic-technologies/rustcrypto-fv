import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l102bd0_30 [Bindings] (code : CodeMap) :
    Rest (n := 1242) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 1228), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1240), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x10347e bytes_l102bd0_30 b_l102bd0_30 := by
  have f600 : InstrSpec 0x10347e [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x10347e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10347e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10347e 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10347e 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10347e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f601 : InstrSpec 0x103483 [0x48, 0x89, 0x41, 0x18] (StorePre 0x103483 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x103483 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103483 0 (.base 1 (.d8 0x18)))
      [.gpr 0, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x103483 0 (.base 1 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x103483 0x48 (by decide) 0 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f602 : InstrSpec 0x103487 [0x4C, 0x89, 0x69, 0x10] (StorePre 0x103487 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x103487 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103487 13 (.base 1 (.d8 0x10)))
      [.gpr 13, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x103487 13 (.base 1 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103487 0x4c (by decide) 5 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f603 : InstrSpec 0x10348b [0x48, 0x83, 0xC4, 0x50] (fun s => s.RIP = 0x10348b) (addR64Imm8Effect 0x10348b 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10348b 4 0x50).toInstrSpec (add_r64_imm8_effect_step 0x10348b 0x48 0xc4 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f604 : InstrSpec 0x10348f [0x5B] (PopPre 0x10348f) (popR64Effect 0x10348f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10348f 1 3).toInstrSpec (pop_r64_effect_step 0x10348f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f605 : InstrSpec 0x103490 [0x41, 0x5C] (PopPre 0x103490) (popR64Effect 0x103490 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103490 2 12).toInstrSpec (pop_r64_rex_effect_step 0x103490 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f606 : InstrSpec 0x103492 [0x41, 0x5D] (PopPre 0x103492) (popR64Effect 0x103492 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103492 2 13).toInstrSpec (pop_r64_rex_effect_step 0x103492 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f607 : InstrSpec 0x103494 [0x41, 0x5E] (PopPre 0x103494) (popR64Effect 0x103494 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103494 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103494 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f608 : InstrSpec 0x103496 [0x41, 0x5F] (PopPre 0x103496) (popR64Effect 0x103496 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103496 2 15).toInstrSpec (pop_r64_rex_effect_step 0x103496 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f609 : InstrSpec 0x103498 [0x5D] (PopPre 0x103498) (popR64Effect 0x103498 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103498 1 5).toInstrSpec (pop_r64_effect_step 0x103498 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f610 : InstrSpec 0x103499 [0xC3] (RetPre 0x103499) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103499).toInstrSpec (ret_effect_step 0x103499) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 1242) (RestInside.out (n := 1242) f600 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1243) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1240), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103483) f600 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1244) (RestInside.exec (n := 1244) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1240), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103487) f601 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1245) (RestInside.exec (n := 1245) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1240), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10348b) f602 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1246) (RestInside.out (n := 1246) f603 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1247) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1074), (4, 1246), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1240), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10348f) f603 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1248) (RestInside.out (n := 1248) f604 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1249) f604 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1250) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1248), (4, 1249), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1240), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103490) f604 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1251) (RestInside.out (n := 1251) f605 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1252) f605 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1253) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1248), (4, 1252), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1251), (13, 1240), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103492) f605 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1254) (RestInside.out (n := 1254) f606 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1255) f606 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1256) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1248), (4, 1255), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1251), (13, 1254), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103494) f606 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1257) (RestInside.out (n := 1257) f607 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1258) f607 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1259) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1248), (4, 1258), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1251), (13, 1254), (14, 1257), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103496) f607 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1260) (RestInside.out (n := 1260) f608 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1261) f608 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1262) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1248), (4, 1261), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1251), (13, 1254), (14, 1257), (15, 1260), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103498) f608 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1263) (RestInside.out (n := 1263) f609 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1264) f609 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1265) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1248), (4, 1264), (5, 1263), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1251), (13, 1254), (14, 1257), (15, 1260), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103499) f609 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1266) (RestInside.out (n := 1266) f610 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1267) f610 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 1268) (ρ' := [(0, 1228), (1, 1242), (2, 1032), (3, 1248), (4, 1267), (5, 1263), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1251), (13, 1254), (14, 1257), (15, 1260), (22, 22), (39, 39), (50, 50), (51, 51)]) f610 (by decide) rfl rfl rfl (by decide)

theorem rest_l102bd0_29 [Bindings] (code : CodeMap) :
    Rest (n := 1202) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1156), (11, 1164), (12, 1024), (13, 1200), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]
      31 0x10343d bytes_l102bd0_29 b_l102bd0_29 := by
  have f580 : InstrSpec 0x10343d [0x4D, 0x31, 0xD5] (fun s => s.RIP = 0x10343d) (xorR64R64Effect 0x10343d 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10343d 13 10).toInstrSpec (xor_r64_r64_effect_step 0x10343d 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f581 : InstrSpec 0x103440 [0x48, 0xD1, 0xE9] (fun s => s.RIP = 0x103440) (shrR64Effect 0x103440 3 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x103440 3 1 1).toInstrSpec (shr_r64_one_effect_step 0x103440 0x48 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f582 : InstrSpec 0x103443 [0x49, 0xC1, 0xEA, 0x07] (fun s => s.RIP = 0x103443) (shrR64Effect 0x103443 4 10 7)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x103443 4 10 7).toInstrSpec (shr_r64_imm8_effect_step 0x103443 0x49 0xea 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f583 : InstrSpec 0x103447 [0x49, 0x31, 0xFA] (fun s => s.RIP = 0x103447) (xorR64R64Effect 0x103447 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103447 10 7).toInstrSpec (xor_r64_r64_effect_step 0x103447 0x49 0xfa (by decide) (by decide)) pre_rip
  have f584 : InstrSpec 0x10344a [0x49, 0x31, 0xCA] (fun s => s.RIP = 0x10344a) (xorR64R64Effect 0x10344a 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10344a 10 1).toInstrSpec (xor_r64_r64_effect_step 0x10344a 0x49 0xca (by decide) (by decide)) pre_rip
  have f585 : InstrSpec 0x10344d [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x10344d) (movR64R64Effect 0x10344d 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10344d 1 8).toInstrSpec (mov_r64_r64_effect_step 0x10344d 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f586 : InstrSpec 0x103450 [0x48, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x103450) (shrR64Effect 0x103450 4 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x103450 4 1 2).toInstrSpec (shr_r64_imm8_effect_step 0x103450 0x48 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f587 : InstrSpec 0x103454 [0x4C, 0x89, 0xC7] (fun s => s.RIP = 0x103454) (movR64R64Effect 0x103454 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103454 7 8).toInstrSpec (mov_r64_r64_effect_step 0x103454 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f588 : InstrSpec 0x103457 [0x48, 0xC1, 0xEF, 0x07] (fun s => s.RIP = 0x103457) (shrR64Effect 0x103457 4 7 7)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x103457 4 7 7).toInstrSpec (shr_r64_imm8_effect_step 0x103457 0x48 0xef 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f589 : InstrSpec 0x10345b [0x48, 0x31, 0xCF] (fun s => s.RIP = 0x10345b) (xorR64R64Effect 0x10345b 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10345b 7 1).toInstrSpec (xor_r64_r64_effect_step 0x10345b 0x48 0xcf (by decide) (by decide)) pre_rip
  have f590 : InstrSpec 0x10345e [0x4C, 0x31, 0xC0] (fun s => s.RIP = 0x10345e) (xorR64R64Effect 0x10345e 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10345e 0 8).toInstrSpec (xor_r64_r64_effect_step 0x10345e 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f591 : InstrSpec 0x103461 [0x48, 0xD1, 0xE8] (fun s => s.RIP = 0x103461) (shrR64Effect 0x103461 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x103461 3 0 1).toInstrSpec (shr_r64_one_effect_step 0x103461 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f592 : InstrSpec 0x103464 [0x48, 0x31, 0xF8] (fun s => s.RIP = 0x103464) (xorR64R64Effect 0x103464 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103464 0 7).toInstrSpec (xor_r64_r64_effect_step 0x103464 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f593 : InstrSpec 0x103467 [0x4C, 0x31, 0xC0] (fun s => s.RIP = 0x103467) (xorR64R64Effect 0x103467 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103467 0 8).toInstrSpec (xor_r64_r64_effect_step 0x103467 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f594 : InstrSpec 0x10346a [0x48, 0xC1, 0xE6, 0x3F] (fun s => s.RIP = 0x10346a) (shlR64Effect 0x10346a 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x10346a 4 6 63).toInstrSpec (shl_r64_imm8_effect_step 0x10346a 0x48 0xe6 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f595 : InstrSpec 0x10346e [0x49, 0xC1, 0xE1, 0x3E] (fun s => s.RIP = 0x10346e) (shlR64Effect 0x10346e 4 9 62)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x10346e 4 9 62).toInstrSpec (shl_r64_imm8_effect_step 0x10346e 0x49 0xe1 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f596 : InstrSpec 0x103472 [0x49, 0x31, 0xF1] (fun s => s.RIP = 0x103472) (xorR64R64Effect 0x103472 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103472 9 6).toInstrSpec (xor_r64_r64_effect_step 0x103472 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f597 : InstrSpec 0x103475 [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x103475) (xorR64R64Effect 0x103475 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103475 9 10).toInstrSpec (xor_r64_r64_effect_step 0x103475 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f598 : InstrSpec 0x103478 [0x4D, 0x31, 0xDD] (fun s => s.RIP = 0x103478) (xorR64R64Effect 0x103478 13 11)
      [.gpr 13, .gpr 11] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103478 13 11).toInstrSpec (xor_r64_r64_effect_step 0x103478 0x4d 0xdd (by decide) (by decide)) pre_rip
  have f599 : InstrSpec 0x10347b [0x4D, 0x31, 0xCD] (fun s => s.RIP = 0x10347b) (xorR64R64Effect 0x10347b 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10347b 13 9).toInstrSpec (xor_r64_r64_effect_step 0x10347b 0x4d 0xcd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1202) (RestInside.out (n := 1202) f580 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1203) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1156), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103440) f580 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1204) (RestInside.out (n := 1204) f581 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1205) (ρ' := [(0, 1120), (1, 1204), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1156), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103443) f581 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1206) (RestInside.out (n := 1206) f582 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1207) (ρ' := [(0, 1120), (1, 1204), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1206), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103447) f582 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1208) (RestInside.out (n := 1208) f583 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1209) (ρ' := [(0, 1120), (1, 1204), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1208), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10344a) f583 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1210) (RestInside.out (n := 1210) f584 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1211) (ρ' := [(0, 1120), (1, 1204), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10344d) f584 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1212) (RestInside.out (n := 1212) f585 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1213) (ρ' := [(0, 1120), (1, 1212), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103450) f585 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1214) (RestInside.out (n := 1214) f586 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1215) (ρ' := [(0, 1120), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103454) f586 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1216) (RestInside.out (n := 1216) f587 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1217) (ρ' := [(0, 1120), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1216), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103457) f587 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1218) (RestInside.out (n := 1218) f588 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1219) (ρ' := [(0, 1120), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1218), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10345b) f588 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1220) (RestInside.out (n := 1220) f589 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1221) (ρ' := [(0, 1120), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1220), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10345e) f589 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1222) (RestInside.out (n := 1222) f590 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1223) (ρ' := [(0, 1222), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1220), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103461) f590 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1224) (RestInside.out (n := 1224) f591 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1225) (ρ' := [(0, 1224), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1220), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103464) f591 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1226) (RestInside.out (n := 1226) f592 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1227) (ρ' := [(0, 1226), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1220), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103467) f592 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1228) (RestInside.out (n := 1228) f593 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1229) (ρ' := [(0, 1228), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1220), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10346a) f593 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1230) (RestInside.out (n := 1230) f594 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1231) (ρ' := [(0, 1228), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1198), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10346e) f594 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1232) (RestInside.out (n := 1232) f595 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1233) (ρ' := [(0, 1228), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1232), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103472) f595 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1234) (RestInside.out (n := 1234) f596 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1235) (ρ' := [(0, 1228), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1234), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103475) f596 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1236) (RestInside.out (n := 1236) f597 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1237) (ρ' := [(0, 1228), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1202), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103478) f597 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1238) (RestInside.out (n := 1238) f598 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1239) (ρ' := [(0, 1228), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1238), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10347b) f598 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1240) (RestInside.out (n := 1240) f599 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1241) (ρ' := [(0, 1228), (1, 1214), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1024), (13, 1240), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10347e) f599 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_30 code

theorem rest_l102bd0_28 [Bindings] (code : CodeMap) :
    Rest (n := 1162) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1158), (8, 1142), (9, 1154), (10, 1156), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]
      51 0x1033f8 bytes_l102bd0_28 b_l102bd0_28 := by
  have f560 : InstrSpec 0x1033f8 [0x4D, 0x31, 0xD5] (fun s => s.RIP = 0x1033f8) (xorR64R64Effect 0x1033f8 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1033f8 13 10).toInstrSpec (xor_r64_r64_effect_step 0x1033f8 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f561 : InstrSpec 0x1033fb [0x4C, 0x8B, 0x5C, 0x24, 0x28] (LoadPre 0x1033fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1033fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1033fb 11 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1033fb 11 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1033fb 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f562 : InstrSpec 0x103400 [0x4D, 0x31, 0xDD] (fun s => s.RIP = 0x103400) (xorR64R64Effect 0x103400 13 11)
      [.gpr 13, .gpr 11] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103400 13 11).toInstrSpec (xor_r64_r64_effect_step 0x103400 0x4d 0xdd (by decide) (by decide)) pre_rip
  have f563 : InstrSpec 0x103403 [0x49, 0x31, 0xFD] (fun s => s.RIP = 0x103403) (xorR64R64Effect 0x103403 13 7)
      [.gpr 13, .gpr 7] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103403 13 7).toInstrSpec (xor_r64_r64_effect_step 0x103403 0x49 0xfd (by decide) (by decide)) pre_rip
  have f564 : InstrSpec 0x103406 [0x4C, 0x89, 0xD7] (fun s => s.RIP = 0x103406) (movR64R64Effect 0x103406 7 10)
      [.gpr 10] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103406 7 10).toInstrSpec (mov_r64_r64_effect_step 0x103406 0x4c 0xd7 (by decide) (by decide)) pre_rip
  have f565 : InstrSpec 0x103409 [0x4C, 0x89, 0xD6] (fun s => s.RIP = 0x103409) (movR64R64Effect 0x103409 6 10)
      [.gpr 10] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103409 6 10).toInstrSpec (mov_r64_r64_effect_step 0x103409 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f566 : InstrSpec 0x10340c [0x48, 0xD1, 0xEE] (fun s => s.RIP = 0x10340c) (shrR64Effect 0x10340c 3 6 1)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10340c 3 6 1).toInstrSpec (shr_r64_one_effect_step 0x10340c 0x48 0xee (by decide) (by decide) (by decide)) pre_rip
  have f567 : InstrSpec 0x10340f [0x48, 0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x10340f) (shrR64Effect 0x10340f 4 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x10340f 4 7 2).toInstrSpec (shr_r64_imm8_effect_step 0x10340f 0x48 0xef 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f568 : InstrSpec 0x103413 [0x48, 0x31, 0xF7] (fun s => s.RIP = 0x103413) (xorR64R64Effect 0x103413 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103413 7 6).toInstrSpec (xor_r64_r64_effect_step 0x103413 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f569 : InstrSpec 0x103416 [0x4D, 0x89, 0xD0] (fun s => s.RIP = 0x103416) (movR64R64Effect 0x103416 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x103416 8 10).toInstrSpec (mov_r64_r64_effect_step 0x103416 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f570 : InstrSpec 0x103419 [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x103419 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103419 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103419 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103419 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x103419 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f571 : InstrSpec 0x10341e [0x48, 0xC1, 0xE6, 0x3F] (fun s => s.RIP = 0x10341e) (shlR64Effect 0x10341e 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x10341e 4 6 63).toInstrSpec (shl_r64_imm8_effect_step 0x10341e 0x48 0xe6 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f572 : InstrSpec 0x103422 [0x49, 0xC1, 0xE1, 0x3E] (fun s => s.RIP = 0x103422) (shlR64Effect 0x103422 4 9 62)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x103422 4 9 62).toInstrSpec (shl_r64_imm8_effect_step 0x103422 0x49 0xe1 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f573 : InstrSpec 0x103426 [0x49, 0x31, 0xF1] (fun s => s.RIP = 0x103426) (xorR64R64Effect 0x103426 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103426 9 6).toInstrSpec (xor_r64_r64_effect_step 0x103426 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f574 : InstrSpec 0x103429 [0x49, 0xC1, 0xE0, 0x39] (fun s => s.RIP = 0x103429) (shlR64Effect 0x103429 4 8 57)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x103429 4 8 57).toInstrSpec (shl_r64_imm8_effect_step 0x103429 0x49 0xe0 0x39 (by decide) (by decide) (by decide)) pre_rip
  have f575 : InstrSpec 0x10342d [0x4D, 0x31, 0xC8] (fun s => s.RIP = 0x10342d) (xorR64R64Effect 0x10342d 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10342d 8 9).toInstrSpec (xor_r64_r64_effect_step 0x10342d 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f576 : InstrSpec 0x103430 [0x4D, 0x31, 0xE8] (fun s => s.RIP = 0x103430) (xorR64R64Effect 0x103430 8 13)
      [.gpr 8, .gpr 13] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103430 8 13).toInstrSpec (xor_r64_r64_effect_step 0x103430 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f577 : InstrSpec 0x103433 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x103433) (movR64R64Effect 0x103433 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103433 6 13).toInstrSpec (mov_r64_r64_effect_step 0x103433 0x4c 0xee (by decide) (by decide)) pre_rip
  have f578 : InstrSpec 0x103436 [0x4D, 0x89, 0xE9] (fun s => s.RIP = 0x103436) (movR64R64Effect 0x103436 9 13)
      [.gpr 13] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x103436 9 13).toInstrSpec (mov_r64_r64_effect_step 0x103436 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f579 : InstrSpec 0x103439 [0x49, 0xC1, 0xE5, 0x39] (fun s => s.RIP = 0x103439) (shlR64Effect 0x103439 4 13 57)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR64Effect_footprint 0x103439 4 13 57).toInstrSpec (shl_r64_imm8_effect_step 0x103439 0x49 0xe5 0x39 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1162) (RestInside.out (n := 1162) f560 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1163) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1158), (8, 1142), (9, 1154), (10, 1156), (11, 1050), (12, 1024), (13, 1162), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033fb) f560 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1164) (RestInside.out (n := 1164) f561 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1165) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1158), (8, 1142), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1162), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103400) f561 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1166) (RestInside.out (n := 1166) f562 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1167) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1158), (8, 1142), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1166), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103403) f562 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1168) (RestInside.out (n := 1168) f563 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1169) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1158), (8, 1142), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103406) f563 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1170) (RestInside.out (n := 1170) f564 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1171) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1170), (8, 1142), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103409) f564 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1172) (RestInside.out (n := 1172) f565 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1173) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1172), (7, 1170), (8, 1142), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10340c) f565 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1174) (RestInside.out (n := 1174) f566 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1175) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1174), (7, 1170), (8, 1142), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10340f) f566 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1176) (RestInside.out (n := 1176) f567 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1177) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1174), (7, 1176), (8, 1142), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103413) f567 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1178) (RestInside.out (n := 1178) f568 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1179) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1174), (7, 1178), (8, 1142), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103416) f568 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1180) (RestInside.out (n := 1180) f569 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1181) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1174), (7, 1178), (8, 1180), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103419) f569 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1182) (RestInside.out (n := 1182) f570 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1183) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1182), (7, 1178), (8, 1180), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10341e) f570 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1184) (RestInside.out (n := 1184) f571 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1185) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1184), (7, 1178), (8, 1180), (9, 1154), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103422) f571 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1186) (RestInside.out (n := 1186) f572 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1187) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1184), (7, 1178), (8, 1180), (9, 1186), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103426) f572 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1188) (RestInside.out (n := 1188) f573 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1189) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1184), (7, 1178), (8, 1180), (9, 1188), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103429) f573 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1190) (RestInside.out (n := 1190) f574 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1191) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1184), (7, 1178), (8, 1190), (9, 1188), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10342d) f574 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1192) (RestInside.out (n := 1192) f575 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1193) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1184), (7, 1178), (8, 1192), (9, 1188), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103430) f575 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1194) (RestInside.out (n := 1194) f576 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1195) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1184), (7, 1178), (8, 1194), (9, 1188), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103433) f576 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1196) (RestInside.out (n := 1196) f577 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1197) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1188), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103436) f577 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1198) (RestInside.out (n := 1198) f578 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1199) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1156), (11, 1164), (12, 1024), (13, 1168), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103439) f578 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1200) (RestInside.out (n := 1200) f579 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1201) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1196), (7, 1178), (8, 1194), (9, 1198), (10, 1156), (11, 1164), (12, 1024), (13, 1200), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10343d) f579 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_29 code

theorem rest_l102bd0_27 [Bindings] (code : CodeMap) :
    Rest (n := 1122) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 1120), (1, 1112), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]
      71 0x1033b3 bytes_l102bd0_27 b_l102bd0_27 := by
  have f540 : InstrSpec 0x1033b3 [0x49, 0x0F, 0xC8] (fun s => s.RIP = 0x1033b3) (bswapR64Effect 0x1033b3 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR64Effect_footprint 0x1033b3 3 8).toInstrSpec (bswap_r64_effect_step 0x1033b3 0x49 (by decide) 0xc8 (by decide)) pre_rip
  have f541 : InstrSpec 0x1033b6 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x1033b6) (movR64R64Effect 0x1033b6 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1033b6 1 8).toInstrSpec (mov_r64_r64_effect_step 0x1033b6 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f542 : InstrSpec 0x1033b9 [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x1033b9) (shrR64Effect 0x1033b9 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1033b9 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x1033b9 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f543 : InstrSpec 0x1033bd [0x4C, 0x21, 0xD9] (fun s => s.RIP = 0x1033bd) (andR64R64Effect 0x1033bd 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1033bd 1 11).toInstrSpec (and_r64_r64_effect_step 0x1033bd 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f544 : InstrSpec 0x1033c0 [0x4D, 0x21, 0xD8] (fun s => s.RIP = 0x1033c0) (andR64R64Effect 0x1033c0 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1033c0 8 11).toInstrSpec (and_r64_r64_effect_step 0x1033c0 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f545 : InstrSpec 0x1033c3 [0x49, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x1033c3) (shlR64Effect 0x1033c3 4 8 4)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x1033c3 4 8 4).toInstrSpec (shl_r64_imm8_effect_step 0x1033c3 0x49 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f546 : InstrSpec 0x1033c7 [0x49, 0x09, 0xC8] (fun s => s.RIP = 0x1033c7) (orR64R64Effect 0x1033c7 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1033c7 8 1).toInstrSpec (or_r64_r64_effect_step 0x1033c7 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f547 : InstrSpec 0x1033ca [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x1033ca) (movR64R64Effect 0x1033ca 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1033ca 1 8).toInstrSpec (mov_r64_r64_effect_step 0x1033ca 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f548 : InstrSpec 0x1033cd [0x4C, 0x21, 0xD1] (fun s => s.RIP = 0x1033cd) (andR64R64Effect 0x1033cd 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1033cd 1 10).toInstrSpec (and_r64_r64_effect_step 0x1033cd 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f549 : InstrSpec 0x1033d0 [0x49, 0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x1033d0) (shrR64Effect 0x1033d0 4 8 2)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1033d0 4 8 2).toInstrSpec (shr_r64_imm8_effect_step 0x1033d0 0x49 0xe8 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f550 : InstrSpec 0x1033d4 [0x4D, 0x21, 0xD0] (fun s => s.RIP = 0x1033d4) (andR64R64Effect 0x1033d4 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1033d4 8 10).toInstrSpec (and_r64_r64_effect_step 0x1033d4 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f551 : InstrSpec 0x1033d7 [0x49, 0x8D, 0x0C, 0x88] (fun s => s.RIP = 0x1033d7) (leaR64Effect 0x1033d7 1 (.sib 8 (some 1) 2 .none))
      [.gpr 8, .gpr 1] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1033d7 1 (.sib 8 (some 1) 2 .none)).toInstrSpec (lea_r64_effect_step 0x1033d7 0x49 (by decide) 1 (.sib 8 (some 1) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f552 : InstrSpec 0x1033db [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x1033db) (andR64R64Effect 0x1033db 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1033db 6 1).toInstrSpec (and_r64_r64_effect_step 0x1033db 0x48 0xce (by decide) (by decide)) pre_rip
  have f553 : InstrSpec 0x1033de [0x48, 0xD1, 0xE9] (fun s => s.RIP = 0x1033de) (shrR64Effect 0x1033de 3 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1033de 3 1 1).toInstrSpec (shr_r64_one_effect_step 0x1033de 0x48 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f554 : InstrSpec 0x1033e1 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x1033e1) (andR64R64Effect 0x1033e1 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1033e1 1 9).toInstrSpec (and_r64_r64_effect_step 0x1033e1 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f555 : InstrSpec 0x1033e4 [0x4C, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x1033e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1033e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1033e4 10 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1033e4 10 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1033e4 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f556 : InstrSpec 0x1033e9 [0x4C, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x1033e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1033e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1033e9 9 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1033e9 9 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1033e9 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f557 : InstrSpec 0x1033ee [0x4D, 0x09, 0xCA] (fun s => s.RIP = 0x1033ee) (orR64R64Effect 0x1033ee 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1033ee 10 9).toInstrSpec (or_r64_r64_effect_step 0x1033ee 0x4d 0xca (by decide) (by decide)) pre_rip
  have f558 : InstrSpec 0x1033f1 [0x48, 0xD1, 0xEF] (fun s => s.RIP = 0x1033f1) (shrR64Effect 0x1033f1 3 7 1)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x1033f1 3 7 1).toInstrSpec (shr_r64_one_effect_step 0x1033f1 0x48 0xef (by decide) (by decide) (by decide)) pre_rip
  have f559 : InstrSpec 0x1033f4 [0x48, 0x8D, 0x0C, 0x71] (fun s => s.RIP = 0x1033f4) (leaR64Effect 0x1033f4 1 (.sib 1 (some 6) 1 .none))
      [.gpr 1, .gpr 6] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1033f4 1 (.sib 1 (some 6) 1 .none)).toInstrSpec (lea_r64_effect_step 0x1033f4 0x48 (by decide) 1 (.sib 1 (some 6) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1122) (RestInside.out (n := 1122) f540 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1123) (ρ' := [(0, 1120), (1, 1112), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1122), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033b6) f540 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1124) (RestInside.out (n := 1124) f541 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1125) (ρ' := [(0, 1120), (1, 1124), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1122), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033b9) f541 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1126) (RestInside.out (n := 1126) f542 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1127) (ρ' := [(0, 1120), (1, 1126), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1122), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033bd) f542 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1128) (RestInside.out (n := 1128) f543 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1129) (ρ' := [(0, 1120), (1, 1128), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1122), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033c0) f543 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1130) (RestInside.out (n := 1130) f544 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1131) (ρ' := [(0, 1120), (1, 1128), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1130), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033c3) f544 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1132) (RestInside.out (n := 1132) f545 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1133) (ρ' := [(0, 1120), (1, 1128), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1132), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033c7) f545 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1134) (RestInside.out (n := 1134) f546 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1135) (ρ' := [(0, 1120), (1, 1128), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1134), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ca) f546 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1136) (RestInside.out (n := 1136) f547 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1137) (ρ' := [(0, 1120), (1, 1136), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1134), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033cd) f547 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1138) (RestInside.out (n := 1138) f548 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1139) (ρ' := [(0, 1120), (1, 1138), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1134), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033d0) f548 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1140) (RestInside.out (n := 1140) f549 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1141) (ρ' := [(0, 1120), (1, 1138), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1140), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033d4) f549 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1142) (RestInside.out (n := 1142) f550 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1143) (ρ' := [(0, 1120), (1, 1138), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1142), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033d7) f550 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1144) (RestInside.out (n := 1144) f551 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1145) (ρ' := [(0, 1120), (1, 1144), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1142), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033db) f551 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1146) (RestInside.out (n := 1146) f552 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1147) (ρ' := [(0, 1120), (1, 1144), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1084), (8, 1142), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033de) f552 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1148) (RestInside.out (n := 1148) f553 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1149) (ρ' := [(0, 1120), (1, 1148), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1084), (8, 1142), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033e1) f553 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1150) (RestInside.out (n := 1150) f554 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1151) (ρ' := [(0, 1120), (1, 1150), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1084), (8, 1142), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033e4) f554 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1152) (RestInside.out (n := 1152) f555 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1153) (ρ' := [(0, 1120), (1, 1150), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1084), (8, 1142), (9, 1080), (10, 1152), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033e9) f555 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1154) (RestInside.out (n := 1154) f556 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1155) (ρ' := [(0, 1120), (1, 1150), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1084), (8, 1142), (9, 1154), (10, 1152), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ee) f556 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1156) (RestInside.out (n := 1156) f557 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1157) (ρ' := [(0, 1120), (1, 1150), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1084), (8, 1142), (9, 1154), (10, 1156), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033f1) f557 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1158) (RestInside.out (n := 1158) f558 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1159) (ρ' := [(0, 1120), (1, 1150), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1158), (8, 1142), (9, 1154), (10, 1156), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033f4) f558 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1160) (RestInside.out (n := 1160) f559 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1161) (ρ' := [(0, 1120), (1, 1160), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1146), (7, 1158), (8, 1142), (9, 1154), (10, 1156), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033f8) f559 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_28 code

theorem rest_l102bd0_26 [Bindings] (code : CodeMap) :
    Rest (n := 1082) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 1078), (1, 908), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1036), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]
      91 0x103371 bytes_l102bd0_26 b_l102bd0_26 := by
  have f520 : InstrSpec 0x103371 [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x103371) (andR64R64Effect 0x103371 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103371 0 9).toInstrSpec (and_r64_r64_effect_step 0x103371 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f521 : InstrSpec 0x103374 [0x48, 0x8D, 0x3C, 0x70] (fun s => s.RIP = 0x103374) (leaR64Effect 0x103374 7 (.sib 0 (some 6) 1 .none))
      [.gpr 0, .gpr 6] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103374 7 (.sib 0 (some 6) 1 .none)).toInstrSpec (lea_r64_effect_step 0x103374 0x48 (by decide) 7 (.sib 0 (some 6) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f522 : InstrSpec 0x103378 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x103378) (bswapR64Effect 0x103378 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x103378 3 1).toInstrSpec (bswap_r64_effect_step 0x103378 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f523 : InstrSpec 0x10337b [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x10337b) (movR64R64Effect 0x10337b 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10337b 0 1).toInstrSpec (mov_r64_r64_effect_step 0x10337b 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f524 : InstrSpec 0x10337e [0x48, 0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x10337e) (shrR64Effect 0x10337e 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10337e 4 0 4).toInstrSpec (shr_r64_imm8_effect_step 0x10337e 0x48 0xe8 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f525 : InstrSpec 0x103382 [0x4C, 0x21, 0xD8] (fun s => s.RIP = 0x103382) (andR64R64Effect 0x103382 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103382 0 11).toInstrSpec (and_r64_r64_effect_step 0x103382 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f526 : InstrSpec 0x103385 [0x4C, 0x21, 0xD9] (fun s => s.RIP = 0x103385) (andR64R64Effect 0x103385 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103385 1 11).toInstrSpec (and_r64_r64_effect_step 0x103385 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f527 : InstrSpec 0x103388 [0x48, 0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x103388) (shlR64Effect 0x103388 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x103388 4 1 4).toInstrSpec (shl_r64_imm8_effect_step 0x103388 0x48 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f528 : InstrSpec 0x10338c [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x10338c) (orR64R64Effect 0x10338c 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10338c 1 0).toInstrSpec (or_r64_r64_effect_step 0x10338c 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f529 : InstrSpec 0x10338f [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x10338f) (movR64R64Effect 0x10338f 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10338f 0 1).toInstrSpec (mov_r64_r64_effect_step 0x10338f 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f530 : InstrSpec 0x103392 [0x4C, 0x21, 0xD0] (fun s => s.RIP = 0x103392) (andR64R64Effect 0x103392 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103392 0 10).toInstrSpec (and_r64_r64_effect_step 0x103392 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f531 : InstrSpec 0x103395 [0x48, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x103395) (shrR64Effect 0x103395 4 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x103395 4 1 2).toInstrSpec (shr_r64_imm8_effect_step 0x103395 0x48 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f532 : InstrSpec 0x103399 [0x4C, 0x21, 0xD1] (fun s => s.RIP = 0x103399) (andR64R64Effect 0x103399 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103399 1 10).toInstrSpec (and_r64_r64_effect_step 0x103399 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f533 : InstrSpec 0x10339c [0x48, 0x8D, 0x04, 0x81] (fun s => s.RIP = 0x10339c) (leaR64Effect 0x10339c 0 (.sib 1 (some 0) 2 .none))
      [.gpr 1, .gpr 0] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10339c 0 (.sib 1 (some 0) 2 .none)).toInstrSpec (lea_r64_effect_step 0x10339c 0x48 (by decide) 0 (.sib 1 (some 0) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f534 : InstrSpec 0x1033a0 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1033a0) (movR64R64Effect 0x1033a0 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1033a0 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1033a0 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f535 : InstrSpec 0x1033a3 [0x48, 0x21, 0xD9] (fun s => s.RIP = 0x1033a3) (andR64R64Effect 0x1033a3 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1033a3 1 3).toInstrSpec (and_r64_r64_effect_step 0x1033a3 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f536 : InstrSpec 0x1033a6 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1033a6) (movR64R64Effect 0x1033a6 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1033a6 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1033a6 0x48 0xde (by decide) (by decide)) pre_rip
  have f537 : InstrSpec 0x1033a9 [0x48, 0xD1, 0xE8] (fun s => s.RIP = 0x1033a9) (shrR64Effect 0x1033a9 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1033a9 3 0 1).toInstrSpec (shr_r64_one_effect_step 0x1033a9 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f538 : InstrSpec 0x1033ac [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x1033ac) (andR64R64Effect 0x1033ac 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1033ac 0 9).toInstrSpec (and_r64_r64_effect_step 0x1033ac 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f539 : InstrSpec 0x1033af [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x1033af) (leaR64Effect 0x1033af 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1033af 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x1033af 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1082) (RestInside.out (n := 1082) f520 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1083) (ρ' := [(0, 1082), (1, 908), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1036), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103374) f520 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1084) (RestInside.out (n := 1084) f521 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1085) (ρ' := [(0, 1082), (1, 908), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103378) f521 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1086) (RestInside.out (n := 1086) f522 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1087) (ρ' := [(0, 1082), (1, 1086), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10337b) f522 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1088) (RestInside.out (n := 1088) f523 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1089) (ρ' := [(0, 1088), (1, 1086), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10337e) f523 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1090) (RestInside.out (n := 1090) f524 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1091) (ρ' := [(0, 1090), (1, 1086), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103382) f524 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1092) (RestInside.out (n := 1092) f525 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1093) (ρ' := [(0, 1092), (1, 1086), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103385) f525 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1094) (RestInside.out (n := 1094) f526 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1095) (ρ' := [(0, 1092), (1, 1094), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103388) f526 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1096) (RestInside.out (n := 1096) f527 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1097) (ρ' := [(0, 1092), (1, 1096), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10338c) f527 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1098) (RestInside.out (n := 1098) f528 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1099) (ρ' := [(0, 1092), (1, 1098), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10338f) f528 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1100) (RestInside.out (n := 1100) f529 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1101) (ρ' := [(0, 1100), (1, 1098), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103392) f529 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1102) (RestInside.out (n := 1102) f530 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1103) (ρ' := [(0, 1102), (1, 1098), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103395) f530 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1104) (RestInside.out (n := 1104) f531 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1105) (ρ' := [(0, 1102), (1, 1104), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103399) f531 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1106) (RestInside.out (n := 1106) f532 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1107) (ρ' := [(0, 1102), (1, 1106), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10339c) f532 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1108) (RestInside.out (n := 1108) f533 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1109) (ρ' := [(0, 1108), (1, 1106), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033a0) f533 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1110) (RestInside.out (n := 1110) f534 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1111) (ρ' := [(0, 1108), (1, 1110), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033a3) f534 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1112) (RestInside.out (n := 1112) f535 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1113) (ρ' := [(0, 1108), (1, 1112), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033a6) f535 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1114) (RestInside.out (n := 1114) f536 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1115) (ρ' := [(0, 1108), (1, 1112), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033a9) f536 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1116) (RestInside.out (n := 1116) f537 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1117) (ρ' := [(0, 1116), (1, 1112), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ac) f537 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1118) (RestInside.out (n := 1118) f538 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1119) (ρ' := [(0, 1118), (1, 1112), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033af) f538 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1120) (RestInside.out (n := 1120) f539 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1121) (ρ' := [(0, 1120), (1, 1112), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1114), (7, 1084), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033b3) f539 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_27 code

theorem rest_l102bd0_25 [Bindings] (code : CodeMap) :
    Rest (n := 1042) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 774), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1036), (8, 1040), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]
      111 0x103315 bytes_l102bd0_25 b_l102bd0_25 := by
  have f500 : InstrSpec 0x103315 [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x103315) (bswapR64Effect 0x103315 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x103315 3 0).toInstrSpec (bswap_r64_effect_step 0x103315 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f501 : InstrSpec 0x103318 [0x49, 0x31, 0xF8] (fun s => s.RIP = 0x103318) (xorR64R64Effect 0x103318 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103318 8 7).toInstrSpec (xor_r64_r64_effect_step 0x103318 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f502 : InstrSpec 0x10331b [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10331b) (movR64R64Effect 0x10331b 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10331b 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10331b 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f503 : InstrSpec 0x10331e [0x48, 0xC1, 0xEE, 0x04] (fun s => s.RIP = 0x10331e) (shrR64Effect 0x10331e 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10331e 4 6 4).toInstrSpec (shr_r64_imm8_effect_step 0x10331e 0x48 0xee 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f504 : InstrSpec 0x103322 [0x49, 0xBB, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F] (fun s => s.RIP = 0x103322) (movR64Imm64Effect 0x103322 11 0xf0f0f0f0f0f0f0f)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x103322 11 0xf0f0f0f0f0f0f0f).toInstrSpec (mov_r64_imm64_effect_step 0x103322 0x49 0xbb (by decide) (by decide) 0xf0f0f0f0f0f0f0f) pre_rip
  have f505 : InstrSpec 0x10332c [0x4C, 0x21, 0xDE] (fun s => s.RIP = 0x10332c) (andR64R64Effect 0x10332c 6 11)
      [.gpr 6, .gpr 11] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10332c 6 11).toInstrSpec (and_r64_r64_effect_step 0x10332c 0x4c 0xde (by decide) (by decide)) pre_rip
  have f506 : InstrSpec 0x10332f [0x4C, 0x21, 0xD8] (fun s => s.RIP = 0x10332f) (andR64R64Effect 0x10332f 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10332f 0 11).toInstrSpec (and_r64_r64_effect_step 0x10332f 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f507 : InstrSpec 0x103332 [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x103332) (shlR64Effect 0x103332 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x103332 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x103332 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f508 : InstrSpec 0x103336 [0x48, 0x09, 0xF0] (fun s => s.RIP = 0x103336) (orR64R64Effect 0x103336 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103336 0 6).toInstrSpec (or_r64_r64_effect_step 0x103336 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f509 : InstrSpec 0x103339 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x103339) (movR64R64Effect 0x103339 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103339 6 0).toInstrSpec (mov_r64_r64_effect_step 0x103339 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f510 : InstrSpec 0x10333c [0x49, 0xBA, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33] (fun s => s.RIP = 0x10333c) (movR64Imm64Effect 0x10333c 10 0x3333333333333333)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x10333c 10 0x3333333333333333).toInstrSpec (mov_r64_imm64_effect_step 0x10333c 0x49 0xba (by decide) (by decide) 0x3333333333333333) pre_rip
  have f511 : InstrSpec 0x103346 [0x4C, 0x21, 0xD6] (fun s => s.RIP = 0x103346) (andR64R64Effect 0x103346 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103346 6 10).toInstrSpec (and_r64_r64_effect_step 0x103346 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f512 : InstrSpec 0x103349 [0x48, 0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x103349) (shrR64Effect 0x103349 4 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x103349 4 0 2).toInstrSpec (shr_r64_imm8_effect_step 0x103349 0x48 0xe8 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f513 : InstrSpec 0x10334d [0x4C, 0x21, 0xD0] (fun s => s.RIP = 0x10334d) (andR64R64Effect 0x10334d 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10334d 0 10).toInstrSpec (and_r64_r64_effect_step 0x10334d 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f514 : InstrSpec 0x103350 [0x48, 0x8D, 0x04, 0xB0] (fun s => s.RIP = 0x103350) (leaR64Effect 0x103350 0 (.sib 0 (some 6) 2 .none))
      [.gpr 0, .gpr 6] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103350 0 (.sib 0 (some 6) 2 .none)).toInstrSpec (lea_r64_effect_step 0x103350 0x48 (by decide) 0 (.sib 0 (some 6) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f515 : InstrSpec 0x103354 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x103354) (movR64R64Effect 0x103354 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103354 6 0).toInstrSpec (mov_r64_r64_effect_step 0x103354 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f516 : InstrSpec 0x103357 [0x48, 0xBB, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55] (fun s => s.RIP = 0x103357) (movR64Imm64Effect 0x103357 3 0x5555555555555555)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x103357 3 0x5555555555555555).toInstrSpec (mov_r64_imm64_effect_step 0x103357 0x48 0xbb (by decide) (by decide) 0x5555555555555555) pre_rip
  have f517 : InstrSpec 0x103361 [0x48, 0x21, 0xDE] (fun s => s.RIP = 0x103361) (andR64R64Effect 0x103361 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103361 6 3).toInstrSpec (and_r64_r64_effect_step 0x103361 0x48 0xde (by decide) (by decide)) pre_rip
  have f518 : InstrSpec 0x103364 [0x48, 0xD1, 0xE8] (fun s => s.RIP = 0x103364) (shrR64Effect 0x103364 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x103364 3 0 1).toInstrSpec (shr_r64_one_effect_step 0x103364 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f519 : InstrSpec 0x103367 [0x49, 0xB9, 0x54, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55] (fun s => s.RIP = 0x103367) (movR64Imm64Effect 0x103367 9 0x5555555555555554)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x103367 9 0x5555555555555554).toInstrSpec (mov_r64_imm64_effect_step 0x103367 0x49 0xb9 (by decide) (by decide) 0x5555555555555554) pre_rip
  refine Rest.ofInside (n := 1042) (RestInside.out (n := 1042) f500 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1043) (ρ' := [(0, 1042), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1036), (8, 1040), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103318) f500 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1044) (RestInside.out (n := 1044) f501 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1045) (ρ' := [(0, 1042), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10331b) f501 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1046) (RestInside.out (n := 1046) f502 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1047) (ρ' := [(0, 1042), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1046), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10331e) f502 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1048) (RestInside.out (n := 1048) f503 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1049) (ρ' := [(0, 1042), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1048), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103322) f503 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1050) (RestInside.out (n := 1050) f504 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1051) (ρ' := [(0, 1042), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1048), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10332c) f504 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1052) (RestInside.out (n := 1052) f505 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1053) (ρ' := [(0, 1042), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1052), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10332f) f505 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1054) (RestInside.out (n := 1054) f506 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1055) (ρ' := [(0, 1054), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1052), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103332) f506 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1056) (RestInside.out (n := 1056) f507 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1057) (ρ' := [(0, 1056), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1052), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103336) f507 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1058) (RestInside.out (n := 1058) f508 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1059) (ρ' := [(0, 1058), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1052), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103339) f508 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1060) (RestInside.out (n := 1060) f509 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1061) (ρ' := [(0, 1058), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1060), (7, 1036), (8, 1044), (9, 1000), (10, 972), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10333c) f509 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1062) (RestInside.out (n := 1062) f510 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1063) (ρ' := [(0, 1058), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1060), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103346) f510 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1064) (RestInside.out (n := 1064) f511 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1065) (ρ' := [(0, 1058), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1064), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103349) f511 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1066) (RestInside.out (n := 1066) f512 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1067) (ρ' := [(0, 1066), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1064), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10334d) f512 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1068) (RestInside.out (n := 1068) f513 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1069) (ρ' := [(0, 1068), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1064), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103350) f513 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1070) (RestInside.out (n := 1070) f514 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1071) (ρ' := [(0, 1070), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1064), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103354) f514 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1072) (RestInside.out (n := 1072) f515 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1073) (ρ' := [(0, 1070), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 1072), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103357) f515 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1074) (RestInside.out (n := 1074) f516 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1075) (ρ' := [(0, 1070), (1, 908), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1072), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103361) f516 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1076) (RestInside.out (n := 1076) f517 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1077) (ρ' := [(0, 1070), (1, 908), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103364) f517 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1078) (RestInside.out (n := 1078) f518 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1079) (ρ' := [(0, 1078), (1, 908), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1036), (8, 1044), (9, 1000), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103367) f518 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1080) (RestInside.out (n := 1080) f519 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1081) (ρ' := [(0, 1078), (1, 908), (2, 1032), (3, 1074), (4, 65), (5, 998), (6, 1076), (7, 1036), (8, 1044), (9, 1080), (10, 1062), (11, 1050), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103371) f519 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_26 code

theorem rest_l102bd0_24 [Bindings] (code : CodeMap) :
    Rest (n := 1002) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 922), (8, 994), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 988), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]
      131 0x1032bb bytes_l102bd0_24 b_l102bd0_24 := by
  have f480 : InstrSpec 0x1032bb [0x4C, 0x0F, 0xAF, 0xFF] (fun s => s.RIP = 0x1032bb) (imulR64R64Effect 0x1032bb 4 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1032bb 4 15 7).toInstrSpec (imul_r64_r64_effect_step 0x1032bb 0x4c (by decide) 0xff (by decide)) pre_rip
  have f481 : InstrSpec 0x1032bf [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x1032bf) (xorR64R64Effect 0x1032bf 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1032bf 14 15).toInstrSpec (xor_r64_r64_effect_step 0x1032bf 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f482 : InstrSpec 0x1032c2 [0x49, 0x31, 0xEE] (fun s => s.RIP = 0x1032c2) (xorR64R64Effect 0x1032c2 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1032c2 14 5).toInstrSpec (xor_r64_r64_effect_step 0x1032c2 0x49 0xee (by decide) (by decide)) pre_rip
  have f483 : InstrSpec 0x1032c5 [0x49, 0x31, 0xF0] (fun s => s.RIP = 0x1032c5) (xorR64R64Effect 0x1032c5 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1032c5 8 6).toInstrSpec (xor_r64_r64_effect_step 0x1032c5 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f484 : InstrSpec 0x1032c8 [0x48, 0x0F, 0xAF, 0xFA] (fun s => s.RIP = 0x1032c8) (imulR64R64Effect 0x1032c8 4 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1032c8 4 7 2).toInstrSpec (imul_r64_r64_effect_step 0x1032c8 0x48 (by decide) 0xfa (by decide)) pre_rip
  have f485 : InstrSpec 0x1032cc [0x4C, 0x31, 0xCF] (fun s => s.RIP = 0x1032cc) (xorR64R64Effect 0x1032cc 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1032cc 7 9).toInstrSpec (xor_r64_r64_effect_step 0x1032cc 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f486 : InstrSpec 0x1032cf [0x4C, 0x31, 0xC7] (fun s => s.RIP = 0x1032cf) (xorR64R64Effect 0x1032cf 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1032cf 7 8).toInstrSpec (xor_r64_r64_effect_step 0x1032cf 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f487 : InstrSpec 0x1032d2 [0x48, 0xBA, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11] (fun s => s.RIP = 0x1032d2) (movR64Imm64Effect 0x1032d2 2 0x1111111111111111)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1032d2 2 0x1111111111111111).toInstrSpec (mov_r64_imm64_effect_step 0x1032d2 0x48 0xba (by decide) (by decide) 0x1111111111111111) pre_rip
  have f488 : InstrSpec 0x1032dc [0x48, 0x21, 0xD3] (fun s => s.RIP = 0x1032dc) (andR64R64Effect 0x1032dc 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1032dc 3 2).toInstrSpec (and_r64_r64_effect_step 0x1032dc 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f489 : InstrSpec 0x1032df [0x48, 0xBA, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22] (fun s => s.RIP = 0x1032df) (movR64Imm64Effect 0x1032df 2 0x2222222222222222)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1032df 2 0x2222222222222222).toInstrSpec (mov_r64_imm64_effect_step 0x1032df 0x48 0xba (by decide) (by decide) 0x2222222222222222) pre_rip
  have f490 : InstrSpec 0x1032e9 [0x49, 0x21, 0xD4] (fun s => s.RIP = 0x1032e9) (andR64R64Effect 0x1032e9 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1032e9 12 2).toInstrSpec (and_r64_r64_effect_step 0x1032e9 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f491 : InstrSpec 0x1032ec [0x49, 0x09, 0xDC] (fun s => s.RIP = 0x1032ec) (orR64R64Effect 0x1032ec 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1032ec 12 3).toInstrSpec (or_r64_r64_effect_step 0x1032ec 0x49 0xdc (by decide) (by decide)) pre_rip
  have f492 : InstrSpec 0x1032ef [0x48, 0xBA, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x1032ef) (movR64Imm64Effect 0x1032ef 2 0x4444444444444444)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1032ef 2 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x1032ef 0x48 0xba (by decide) (by decide) 0x4444444444444444) pre_rip
  have f493 : InstrSpec 0x1032f9 [0x49, 0x21, 0xD6] (fun s => s.RIP = 0x1032f9) (andR64R64Effect 0x1032f9 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1032f9 14 2).toInstrSpec (and_r64_r64_effect_step 0x1032f9 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f494 : InstrSpec 0x1032fc [0x4D, 0x09, 0xE6] (fun s => s.RIP = 0x1032fc) (orR64R64Effect 0x1032fc 14 12)
      [.gpr 14, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1032fc 14 12).toInstrSpec (or_r64_r64_effect_step 0x1032fc 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f495 : InstrSpec 0x1032ff [0x48, 0xBA, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88] (fun s => s.RIP = 0x1032ff) (movR64Imm64Effect 0x1032ff 2 0x8888888888888888)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1032ff 2 0x8888888888888888).toInstrSpec (mov_r64_imm64_effect_step 0x1032ff 0x48 0xba (by decide) (by decide) 0x8888888888888888) pre_rip
  have f496 : InstrSpec 0x103309 [0x48, 0x21, 0xD7] (fun s => s.RIP = 0x103309) (andR64R64Effect 0x103309 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103309 7 2).toInstrSpec (and_r64_r64_effect_step 0x103309 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f497 : InstrSpec 0x10330c [0x4C, 0x09, 0xF7] (fun s => s.RIP = 0x10330c) (orR64R64Effect 0x10330c 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10330c 7 14).toInstrSpec (or_r64_r64_effect_step 0x10330c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f498 : InstrSpec 0x10330f [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x10330f) (movR64R64Effect 0x10330f 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10330f 8 0).toInstrSpec (mov_r64_r64_effect_step 0x10330f 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f499 : InstrSpec 0x103312 [0x49, 0x31, 0xC8] (fun s => s.RIP = 0x103312) (xorR64R64Effect 0x103312 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103312 8 1).toInstrSpec (xor_r64_r64_effect_step 0x103312 0x49 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1002) (RestInside.out (n := 1002) f480 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1003) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 922), (8, 994), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 988), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032bf) f480 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1004) (RestInside.out (n := 1004) f481 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1005) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 922), (8, 994), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1004), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032c2) f481 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1006) (RestInside.out (n := 1006) f482 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1007) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 922), (8, 994), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032c5) f482 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1008) (RestInside.out (n := 1008) f483 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1009) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 922), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032c8) f483 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1010) (RestInside.out (n := 1010) f484 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1011) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 1010), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032cc) f484 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1012) (RestInside.out (n := 1012) f485 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1013) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 1012), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032cf) f485 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1014) (RestInside.out (n := 1014) f486 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1015) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032d2) f486 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1016) (RestInside.out (n := 1016) f487 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1017) (ρ' := [(0, 774), (1, 908), (2, 1016), (3, 962), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032dc) f487 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1018) (RestInside.out (n := 1018) f488 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1019) (ρ' := [(0, 774), (1, 908), (2, 1016), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032df) f488 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1020) (RestInside.out (n := 1020) f489 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1021) (ρ' := [(0, 774), (1, 908), (2, 1020), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032e9) f489 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1022) (RestInside.out (n := 1022) f490 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1023) (ρ' := [(0, 774), (1, 908), (2, 1020), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 1022), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032ec) f490 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1024) (RestInside.out (n := 1024) f491 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1025) (ρ' := [(0, 774), (1, 908), (2, 1020), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032ef) f491 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1026) (RestInside.out (n := 1026) f492 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1027) (ρ' := [(0, 774), (1, 908), (2, 1026), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1006), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032f9) f492 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1028) (RestInside.out (n := 1028) f493 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1029) (ρ' := [(0, 774), (1, 908), (2, 1026), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1028), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032fc) f493 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1030) (RestInside.out (n := 1030) f494 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1031) (ρ' := [(0, 774), (1, 908), (2, 1026), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032ff) f494 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1032) (RestInside.out (n := 1032) f495 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1033) (ρ' := [(0, 774), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1014), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103309) f495 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1034) (RestInside.out (n := 1034) f496 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1035) (ρ' := [(0, 774), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1034), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10330c) f496 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1036) (RestInside.out (n := 1036) f497 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1037) (ρ' := [(0, 774), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1036), (8, 1008), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10330f) f497 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1038) (RestInside.out (n := 1038) f498 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1039) (ρ' := [(0, 774), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1036), (8, 1038), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103312) f498 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1040) (RestInside.out (n := 1040) f499 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1041) (ρ' := [(0, 774), (1, 908), (2, 1032), (3, 1018), (4, 65), (5, 998), (6, 990), (7, 1036), (8, 1040), (9, 1000), (10, 972), (11, 992), (12, 1024), (13, 627), (14, 1030), (15, 1002), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103315) f499 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_25 code

theorem rest_l102bd0_23 [Bindings] (code : CodeMap) :
    Rest (n := 962) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 774), (1, 908), (2, 946), (3, 960), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 954), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]
      151 0x103275 bytes_l102bd0_23 b_l102bd0_23 := by
  have f460 : InstrSpec 0x103275 [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x103275) (xorR64R64Effect 0x103275 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103275 3 14).toInstrSpec (xor_r64_r64_effect_step 0x103275 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f461 : InstrSpec 0x103278 [0x4D, 0x89, 0xDE] (fun s => s.RIP = 0x103278) (movR64R64Effect 0x103278 14 11)
      [.gpr 11] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103278 14 11).toInstrSpec (mov_r64_r64_effect_step 0x103278 0x4d 0xde (by decide) (by decide)) pre_rip
  have f462 : InstrSpec 0x10327b [0x4D, 0x0F, 0xAF, 0xF1] (fun s => s.RIP = 0x10327b) (imulR64R64Effect 0x10327b 4 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10327b 4 14 9).toInstrSpec (imul_r64_r64_effect_step 0x10327b 0x4d (by decide) 0xf1 (by decide)) pre_rip
  have f463 : InstrSpec 0x10327f [0x49, 0x89, 0xEA] (fun s => s.RIP = 0x10327f) (movR64R64Effect 0x10327f 10 5)
      [.gpr 5] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10327f 10 5).toInstrSpec (mov_r64_r64_effect_step 0x10327f 0x49 0xea (by decide) (by decide)) pre_rip
  have f464 : InstrSpec 0x103282 [0x4C, 0x0F, 0xAF, 0xD7] (fun s => s.RIP = 0x103282) (imulR64R64Effect 0x103282 4 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103282 4 10 7).toInstrSpec (imul_r64_r64_effect_step 0x103282 0x4c (by decide) 0xd7 (by decide)) pre_rip
  have f465 : InstrSpec 0x103286 [0x4D, 0x31, 0xF2] (fun s => s.RIP = 0x103286) (xorR64R64Effect 0x103286 10 14)
      [.gpr 10, .gpr 14] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103286 10 14).toInstrSpec (xor_r64_r64_effect_step 0x103286 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f466 : InstrSpec 0x103289 [0x4D, 0x89, 0xFE] (fun s => s.RIP = 0x103289) (movR64R64Effect 0x103289 14 15)
      [.gpr 15] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103289 14 15).toInstrSpec (mov_r64_r64_effect_step 0x103289 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f467 : InstrSpec 0x10328c [0x4C, 0x0F, 0xAF, 0xF6] (fun s => s.RIP = 0x10328c) (imulR64R64Effect 0x10328c 4 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10328c 4 14 6).toInstrSpec (imul_r64_r64_effect_step 0x10328c 0x4c (by decide) 0xf6 (by decide)) pre_rip
  have f468 : InstrSpec 0x103290 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x103290) (movR64R64Effect 0x103290 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x103290 12 2).toInstrSpec (mov_r64_r64_effect_step 0x103290 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f469 : InstrSpec 0x103293 [0x4D, 0x0F, 0xAF, 0xE0] (fun s => s.RIP = 0x103293) (imulR64R64Effect 0x103293 4 12 8)
      [.gpr 12, .gpr 8] [] [.reg 12, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103293 4 12 8).toInstrSpec (imul_r64_r64_effect_step 0x103293 0x4d (by decide) 0xe0 (by decide)) pre_rip
  have f470 : InstrSpec 0x103297 [0x4D, 0x31, 0xF4] (fun s => s.RIP = 0x103297) (xorR64R64Effect 0x103297 12 14)
      [.gpr 12, .gpr 14] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103297 12 14).toInstrSpec (xor_r64_r64_effect_step 0x103297 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f471 : InstrSpec 0x10329a [0x4D, 0x31, 0xD4] (fun s => s.RIP = 0x10329a) (xorR64R64Effect 0x10329a 12 10)
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10329a 12 10).toInstrSpec (xor_r64_r64_effect_step 0x10329a 0x4d 0xd4 (by decide) (by decide)) pre_rip
  have f472 : InstrSpec 0x10329d [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x10329d) (movR64R64Effect 0x10329d 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10329d 14 2).toInstrSpec (mov_r64_r64_effect_step 0x10329d 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f473 : InstrSpec 0x1032a0 [0x4C, 0x0F, 0xAF, 0xF6] (fun s => s.RIP = 0x1032a0) (imulR64R64Effect 0x1032a0 4 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1032a0 4 14 6).toInstrSpec (imul_r64_r64_effect_step 0x1032a0 0x4c (by decide) 0xf6 (by decide)) pre_rip
  have f474 : InstrSpec 0x1032a4 [0x49, 0x0F, 0xAF, 0xF3] (fun s => s.RIP = 0x1032a4) (imulR64R64Effect 0x1032a4 4 6 11)
      [.gpr 6, .gpr 11] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1032a4 4 6 11).toInstrSpec (imul_r64_r64_effect_step 0x1032a4 0x49 (by decide) 0xf3 (by decide)) pre_rip
  have f475 : InstrSpec 0x1032a8 [0x4D, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x1032a8) (imulR64R64Effect 0x1032a8 4 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1032a8 4 11 8).toInstrSpec (imul_r64_r64_effect_step 0x1032a8 0x4d (by decide) 0xd8 (by decide)) pre_rip
  have f476 : InstrSpec 0x1032ac [0x4C, 0x0F, 0xAF, 0xC5] (fun s => s.RIP = 0x1032ac) (imulR64R64Effect 0x1032ac 4 8 5)
      [.gpr 8, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1032ac 4 8 5).toInstrSpec (imul_r64_r64_effect_step 0x1032ac 0x4c (by decide) 0xc5 (by decide)) pre_rip
  have f477 : InstrSpec 0x1032b0 [0x49, 0x0F, 0xAF, 0xE9] (fun s => s.RIP = 0x1032b0) (imulR64R64Effect 0x1032b0 4 5 9)
      [.gpr 5, .gpr 9] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1032b0 4 5 9).toInstrSpec (imul_r64_r64_effect_step 0x1032b0 0x49 (by decide) 0xe9 (by decide)) pre_rip
  have f478 : InstrSpec 0x1032b4 [0x4C, 0x31, 0xDD] (fun s => s.RIP = 0x1032b4) (xorR64R64Effect 0x1032b4 5 11)
      [.gpr 5, .gpr 11] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1032b4 5 11).toInstrSpec (xor_r64_r64_effect_step 0x1032b4 0x4c 0xdd (by decide) (by decide)) pre_rip
  have f479 : InstrSpec 0x1032b7 [0x4D, 0x0F, 0xAF, 0xCF] (fun s => s.RIP = 0x1032b7) (imulR64R64Effect 0x1032b7 4 9 15)
      [.gpr 9, .gpr 15] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1032b7 4 9 15).toInstrSpec (imul_r64_r64_effect_step 0x1032b7 0x4d (by decide) 0xcf (by decide)) pre_rip
  refine Rest.ofInside (n := 962) (RestInside.out (n := 962) f460 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 963) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 954), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103278) f460 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 964) (RestInside.out (n := 964) f461 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 965) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 954), (13, 627), (14, 964), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10327b) f461 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 966) (RestInside.out (n := 966) f462 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 967) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 954), (13, 627), (14, 966), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10327f) f462 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 968) (RestInside.out (n := 968) f463 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 969) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 968), (11, 914), (12, 954), (13, 627), (14, 966), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103282) f463 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 970) (RestInside.out (n := 970) f464 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 971) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 970), (11, 914), (12, 954), (13, 627), (14, 966), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103286) f464 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 972) (RestInside.out (n := 972) f465 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 973) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 954), (13, 627), (14, 966), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103289) f465 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 974) (RestInside.out (n := 974) f466 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 975) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 954), (13, 627), (14, 974), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10328c) f466 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 976) (RestInside.out (n := 976) f467 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 977) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 954), (13, 627), (14, 976), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103290) f467 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 978) (RestInside.out (n := 978) f468 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 979) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 978), (13, 627), (14, 976), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103293) f468 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 980) (RestInside.out (n := 980) f469 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 981) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 980), (13, 627), (14, 976), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103297) f469 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 982) (RestInside.out (n := 982) f470 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 983) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 982), (13, 627), (14, 976), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10329a) f470 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 984) (RestInside.out (n := 984) f471 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 985) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 984), (13, 627), (14, 976), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10329d) f471 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 986) (RestInside.out (n := 986) f472 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 987) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 984), (13, 627), (14, 986), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032a0) f472 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 988) (RestInside.out (n := 988) f473 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 989) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 984), (13, 627), (14, 988), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032a4) f473 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 990) (RestInside.out (n := 990) f474 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 991) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 990), (7, 922), (8, 950), (9, 948), (10, 972), (11, 914), (12, 984), (13, 627), (14, 988), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032a8) f474 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 992) (RestInside.out (n := 992) f475 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 993) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 990), (7, 922), (8, 950), (9, 948), (10, 972), (11, 992), (12, 984), (13, 627), (14, 988), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032ac) f475 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 994) (RestInside.out (n := 994) f476 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 995) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 918), (6, 990), (7, 922), (8, 994), (9, 948), (10, 972), (11, 992), (12, 984), (13, 627), (14, 988), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032b0) f476 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 996) (RestInside.out (n := 996) f477 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 997) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 996), (6, 990), (7, 922), (8, 994), (9, 948), (10, 972), (11, 992), (12, 984), (13, 627), (14, 988), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032b4) f477 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 998) (RestInside.out (n := 998) f478 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 999) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 922), (8, 994), (9, 948), (10, 972), (11, 992), (12, 984), (13, 627), (14, 988), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032b7) f478 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1000) (RestInside.out (n := 1000) f479 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1001) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 962), (4, 65), (5, 998), (6, 990), (7, 922), (8, 994), (9, 1000), (10, 972), (11, 992), (12, 984), (13, 627), (14, 988), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032bb) f479 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_24 code

theorem rest_l102bd0_22 [Bindings] (code : CodeMap) :
    Rest (n := 922) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 918), (6, 633), (7, 920), (8, 888), (9, 870), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]
      171 0x10322e bytes_l102bd0_22 b_l102bd0_22 := by
  have f440 : InstrSpec 0x10322e [0x4C, 0x21, 0xC7] (fun s => s.RIP = 0x10322e) (andR64R64Effect 0x10322e 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10322e 7 8).toInstrSpec (and_r64_r64_effect_step 0x10322e 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f441 : InstrSpec 0x103231 [0x49, 0x89, 0xF1] (fun s => s.RIP = 0x103231) (movR64R64Effect 0x103231 9 6)
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x103231 9 6).toInstrSpec (mov_r64_r64_effect_step 0x103231 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f442 : InstrSpec 0x103234 [0x49, 0x89, 0xF0] (fun s => s.RIP = 0x103234) (movR64R64Effect 0x103234 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x103234 8 6).toInstrSpec (mov_r64_r64_effect_step 0x103234 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f443 : InstrSpec 0x103237 [0x4C, 0x21, 0xD6] (fun s => s.RIP = 0x103237) (andR64R64Effect 0x103237 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103237 6 10).toInstrSpec (and_r64_r64_effect_step 0x103237 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f444 : InstrSpec 0x10323a [0x4C, 0x89, 0xDB] (fun s => s.RIP = 0x10323a) (movR64R64Effect 0x10323a 3 11)
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10323a 3 11).toInstrSpec (mov_r64_r64_effect_step 0x10323a 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f445 : InstrSpec 0x10323d [0x48, 0x0F, 0xAF, 0xDF] (fun s => s.RIP = 0x10323d) (imulR64R64Effect 0x10323d 4 3 7)
      [.gpr 3, .gpr 7] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10323d 4 3 7).toInstrSpec (imul_r64_r64_effect_step 0x10323d 0x48 (by decide) 0xdf (by decide)) pre_rip
  have f446 : InstrSpec 0x103241 [0x49, 0x89, 0xEE] (fun s => s.RIP = 0x103241) (movR64R64Effect 0x103241 14 5)
      [.gpr 5] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103241 14 5).toInstrSpec (mov_r64_r64_effect_step 0x103241 0x49 0xee (by decide) (by decide)) pre_rip
  have f447 : InstrSpec 0x103244 [0x4C, 0x0F, 0xAF, 0xF6] (fun s => s.RIP = 0x103244) (imulR64R64Effect 0x103244 4 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103244 4 14 6).toInstrSpec (imul_r64_r64_effect_step 0x103244 0x4c (by decide) 0xf6 (by decide)) pre_rip
  have f448 : InstrSpec 0x103248 [0x49, 0x31, 0xDE] (fun s => s.RIP = 0x103248) (xorR64R64Effect 0x103248 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103248 14 3).toInstrSpec (xor_r64_r64_effect_step 0x103248 0x49 0xde (by decide) (by decide)) pre_rip
  have f449 : InstrSpec 0x10324b [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x10324b) (movR64R64Effect 0x10324b 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10324b 15 2).toInstrSpec (mov_r64_r64_effect_step 0x10324b 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f450 : InstrSpec 0x10324e [0x48, 0xBB, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x10324e) (movR64Imm64Effect 0x10324e 3 0x4444444444444444)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x10324e 3 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x10324e 0x48 0xbb (by decide) (by decide) 0x4444444444444444) pre_rip
  have f451 : InstrSpec 0x103258 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x103258) (andR64R64Effect 0x103258 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103258 15 3).toInstrSpec (and_r64_r64_effect_step 0x103258 0x49 0xdf (by decide) (by decide)) pre_rip
  have f452 : InstrSpec 0x10325b [0x4C, 0x21, 0xD2] (fun s => s.RIP = 0x10325b) (andR64R64Effect 0x10325b 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10325b 2 10).toInstrSpec (and_r64_r64_effect_step 0x10325b 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f453 : InstrSpec 0x10325e [0x4D, 0x21, 0xE1] (fun s => s.RIP = 0x10325e) (andR64R64Effect 0x10325e 9 12)
      [.gpr 9, .gpr 12] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10325e 9 12).toInstrSpec (and_r64_r64_effect_step 0x10325e 0x4d 0xe1 (by decide) (by decide)) pre_rip
  have f454 : InstrSpec 0x103261 [0x49, 0x21, 0xD8] (fun s => s.RIP = 0x103261) (andR64R64Effect 0x103261 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103261 8 3).toInstrSpec (and_r64_r64_effect_step 0x103261 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f455 : InstrSpec 0x103264 [0x4D, 0x89, 0xFC] (fun s => s.RIP = 0x103264) (movR64R64Effect 0x103264 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x103264 12 15).toInstrSpec (mov_r64_r64_effect_step 0x103264 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f456 : InstrSpec 0x103267 [0x4D, 0x0F, 0xAF, 0xE0] (fun s => s.RIP = 0x103267) (imulR64R64Effect 0x103267 4 12 8)
      [.gpr 12, .gpr 8] [] [.reg 12, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103267 4 12 8).toInstrSpec (imul_r64_r64_effect_step 0x103267 0x4d (by decide) 0xe0 (by decide)) pre_rip
  have f457 : InstrSpec 0x10326b [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x10326b) (movR64R64Effect 0x10326b 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10326b 3 2).toInstrSpec (mov_r64_r64_effect_step 0x10326b 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f458 : InstrSpec 0x10326e [0x49, 0x0F, 0xAF, 0xD9] (fun s => s.RIP = 0x10326e) (imulR64R64Effect 0x10326e 4 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10326e 4 3 9).toInstrSpec (imul_r64_r64_effect_step 0x10326e 0x49 (by decide) 0xd9 (by decide)) pre_rip
  have f459 : InstrSpec 0x103272 [0x4C, 0x31, 0xE3] (fun s => s.RIP = 0x103272) (xorR64R64Effect 0x103272 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103272 3 12).toInstrSpec (xor_r64_r64_effect_step 0x103272 0x4c 0xe3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 922) (RestInside.out (n := 922) f440 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 923) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 918), (6, 633), (7, 922), (8, 888), (9, 870), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103231) f440 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 924) (RestInside.out (n := 924) f441 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 925) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 918), (6, 633), (7, 922), (8, 888), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103234) f441 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 926) (RestInside.out (n := 926) f442 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 927) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 918), (6, 633), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103237) f442 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 928) (RestInside.out (n := 928) f443 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 929) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10323a) f443 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 930) (RestInside.out (n := 930) f444 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 931) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 930), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10323d) f444 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 932) (RestInside.out (n := 932) f445 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 933) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 932), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103241) f445 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 934) (RestInside.out (n := 934) f446 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 935) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 932), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 934), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103244) f446 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 936) (RestInside.out (n := 936) f447 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 937) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 932), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 936), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103248) f447 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 938) (RestInside.out (n := 938) f448 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 939) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 932), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 938), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10324b) f448 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 940) (RestInside.out (n := 940) f449 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 941) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 932), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 938), (15, 940), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10324e) f449 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 942) (RestInside.out (n := 942) f450 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 943) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 942), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 938), (15, 940), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103258) f450 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 944) (RestInside.out (n := 944) f451 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 945) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 942), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10325b) f451 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 946) (RestInside.out (n := 946) f452 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 947) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 942), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 924), (10, 904), (11, 914), (12, 892), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10325e) f452 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 948) (RestInside.out (n := 948) f453 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 949) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 942), (4, 65), (5, 918), (6, 928), (7, 922), (8, 926), (9, 948), (10, 904), (11, 914), (12, 892), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103261) f453 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 950) (RestInside.out (n := 950) f454 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 951) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 942), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 892), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103264) f454 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 952) (RestInside.out (n := 952) f455 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 953) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 942), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 952), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103267) f455 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 954) (RestInside.out (n := 954) f456 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 955) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 942), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 954), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10326b) f456 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 956) (RestInside.out (n := 956) f457 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 957) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 956), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 954), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10326e) f457 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 958) (RestInside.out (n := 958) f458 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 959) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 958), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 954), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103272) f458 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 960) (RestInside.out (n := 960) f459 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 961) (ρ' := [(0, 774), (1, 908), (2, 946), (3, 960), (4, 65), (5, 918), (6, 928), (7, 922), (8, 950), (9, 948), (10, 904), (11, 914), (12, 954), (13, 627), (14, 938), (15, 944), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103275) f459 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_23 code

theorem rest_l102bd0_21 [Bindings] (code : CodeMap) :
    Rest (n := 882) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 774), (1, 792), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]
      191 0x1031d4 bytes_l102bd0_21 b_l102bd0_21 := by
  have f420 : InstrSpec 0x1031d4 [0x48, 0x0F, 0xAF, 0xCA] (fun s => s.RIP = 0x1031d4) (imulR64R64Effect 0x1031d4 4 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1031d4 4 1 2).toInstrSpec (imul_r64_r64_effect_step 0x1031d4 0x48 (by decide) 0xca (by decide)) pre_rip
  have f421 : InstrSpec 0x1031d8 [0x4C, 0x31, 0xC1] (fun s => s.RIP = 0x1031d8) (xorR64R64Effect 0x1031d8 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1031d8 1 8).toInstrSpec (xor_r64_r64_effect_step 0x1031d8 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f422 : InstrSpec 0x1031db [0x48, 0x31, 0xF9] (fun s => s.RIP = 0x1031db) (xorR64R64Effect 0x1031db 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1031db 1 7).toInstrSpec (xor_r64_r64_effect_step 0x1031db 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f423 : InstrSpec 0x1031de [0x49, 0xB8, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11] (fun s => s.RIP = 0x1031de) (movR64Imm64Effect 0x1031de 8 0x1111111111111111)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x1031de 8 0x1111111111111111).toInstrSpec (mov_r64_imm64_effect_step 0x1031de 0x49 0xb8 (by decide) (by decide) 0x1111111111111111) pre_rip
  have f424 : InstrSpec 0x1031e8 [0x4D, 0x21, 0xC3] (fun s => s.RIP = 0x1031e8) (andR64R64Effect 0x1031e8 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1031e8 11 8).toInstrSpec (and_r64_r64_effect_step 0x1031e8 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f425 : InstrSpec 0x1031eb [0x49, 0xBC, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22] (fun s => s.RIP = 0x1031eb) (movR64Imm64Effect 0x1031eb 12 0x2222222222222222)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x1031eb 12 0x2222222222222222).toInstrSpec (mov_r64_imm64_effect_step 0x1031eb 0x49 0xbc (by decide) (by decide) 0x2222222222222222) pre_rip
  have f426 : InstrSpec 0x1031f5 [0x4D, 0x21, 0xE7] (fun s => s.RIP = 0x1031f5) (andR64R64Effect 0x1031f5 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1031f5 15 12).toInstrSpec (and_r64_r64_effect_step 0x1031f5 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f427 : InstrSpec 0x1031f8 [0x4D, 0x09, 0xDF] (fun s => s.RIP = 0x1031f8) (orR64R64Effect 0x1031f8 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1031f8 15 11).toInstrSpec (or_r64_r64_effect_step 0x1031f8 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f428 : InstrSpec 0x1031fb [0x48, 0xBA, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x1031fb) (movR64Imm64Effect 0x1031fb 2 0x4444444444444444)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1031fb 2 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x1031fb 0x48 0xba (by decide) (by decide) 0x4444444444444444) pre_rip
  have f429 : InstrSpec 0x103205 [0x49, 0x21, 0xD6] (fun s => s.RIP = 0x103205) (andR64R64Effect 0x103205 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103205 14 2).toInstrSpec (and_r64_r64_effect_step 0x103205 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f430 : InstrSpec 0x103208 [0x4D, 0x09, 0xFE] (fun s => s.RIP = 0x103208) (orR64R64Effect 0x103208 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103208 14 15).toInstrSpec (or_r64_r64_effect_step 0x103208 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f431 : InstrSpec 0x10320b [0x49, 0xBA, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88] (fun s => s.RIP = 0x10320b) (movR64Imm64Effect 0x10320b 10 0x8888888888888888)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x10320b 10 0x8888888888888888).toInstrSpec (mov_r64_imm64_effect_step 0x10320b 0x49 0xba (by decide) (by decide) 0x8888888888888888) pre_rip
  have f432 : InstrSpec 0x103215 [0x4C, 0x21, 0xD1] (fun s => s.RIP = 0x103215) (andR64R64Effect 0x103215 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103215 1 10).toInstrSpec (and_r64_r64_effect_step 0x103215 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f433 : InstrSpec 0x103218 [0x4C, 0x09, 0xF1] (fun s => s.RIP = 0x103218) (orR64R64Effect 0x103218 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103218 1 14).toInstrSpec (or_r64_r64_effect_step 0x103218 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f434 : InstrSpec 0x10321b [0x48, 0x8B, 0x14, 0x24] (LoadPre 0x10321b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10321b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10321b 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10321b 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10321b 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f435 : InstrSpec 0x10321f [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x10321f) (movR64R64Effect 0x10321f 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10321f 11 2).toInstrSpec (mov_r64_r64_effect_step 0x10321f 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f436 : InstrSpec 0x103222 [0x4D, 0x21, 0xC3] (fun s => s.RIP = 0x103222) (andR64R64Effect 0x103222 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103222 11 8).toInstrSpec (and_r64_r64_effect_step 0x103222 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f437 : InstrSpec 0x103225 [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x103225) (movR64R64Effect 0x103225 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103225 5 2).toInstrSpec (mov_r64_r64_effect_step 0x103225 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f438 : InstrSpec 0x103228 [0x4C, 0x21, 0xE5] (fun s => s.RIP = 0x103228) (andR64R64Effect 0x103228 5 12)
      [.gpr 5, .gpr 12] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103228 5 12).toInstrSpec (and_r64_r64_effect_step 0x103228 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f439 : InstrSpec 0x10322b [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x10322b) (movR64R64Effect 0x10322b 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10322b 7 6).toInstrSpec (mov_r64_r64_effect_step 0x10322b 0x48 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 882) (RestInside.out (n := 882) f420 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 883) (ρ' := [(0, 774), (1, 882), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031d8) f420 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 884) (RestInside.out (n := 884) f421 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 885) (ρ' := [(0, 774), (1, 884), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031db) f421 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 886) (RestInside.out (n := 886) f422 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 887) (ρ' := [(0, 774), (1, 886), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031de) f422 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 888) (RestInside.out (n := 888) f423 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 889) (ρ' := [(0, 774), (1, 886), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031e8) f423 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 890) (RestInside.out (n := 890) f424 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 891) (ρ' := [(0, 774), (1, 886), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 864), (11, 890), (12, 844), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031eb) f424 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 892) (RestInside.out (n := 892) f425 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 893) (ρ' := [(0, 774), (1, 886), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 864), (11, 890), (12, 892), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031f5) f425 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 894) (RestInside.out (n := 894) f426 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 895) (ρ' := [(0, 774), (1, 886), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 864), (11, 890), (12, 892), (13, 627), (14, 878), (15, 894), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031f8) f426 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 896) (RestInside.out (n := 896) f427 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 897) (ρ' := [(0, 774), (1, 886), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 864), (11, 890), (12, 892), (13, 627), (14, 878), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031fb) f427 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 898) (RestInside.out (n := 898) f428 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 899) (ρ' := [(0, 774), (1, 886), (2, 898), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 864), (11, 890), (12, 892), (13, 627), (14, 878), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103205) f428 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 900) (RestInside.out (n := 900) f429 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 901) (ρ' := [(0, 774), (1, 886), (2, 898), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 864), (11, 890), (12, 892), (13, 627), (14, 900), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103208) f429 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 902) (RestInside.out (n := 902) f430 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 903) (ρ' := [(0, 774), (1, 886), (2, 898), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 864), (11, 890), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10320b) f430 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 904) (RestInside.out (n := 904) f431 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 905) (ρ' := [(0, 774), (1, 886), (2, 898), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 904), (11, 890), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103215) f431 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 906) (RestInside.out (n := 906) f432 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 907) (ρ' := [(0, 774), (1, 906), (2, 898), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 904), (11, 890), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103218) f432 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 908) (RestInside.out (n := 908) f433 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 909) (ρ' := [(0, 774), (1, 908), (2, 898), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 904), (11, 890), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10321b) f433 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 910) (RestInside.out (n := 910) f434 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 911) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 904), (11, 890), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10321f) f434 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 912) (RestInside.out (n := 912) f435 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 913) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 904), (11, 912), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103222) f435 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 914) (RestInside.out (n := 914) f436 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 915) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 888), (9, 870), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103225) f436 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 916) (RestInside.out (n := 916) f437 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 917) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 916), (6, 633), (7, 880), (8, 888), (9, 870), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103228) f437 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 918) (RestInside.out (n := 918) f438 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 919) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 918), (6, 633), (7, 880), (8, 888), (9, 870), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10322b) f438 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 920) (RestInside.out (n := 920) f439 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 921) (ρ' := [(0, 774), (1, 908), (2, 910), (3, 874), (4, 65), (5, 918), (6, 633), (7, 920), (8, 888), (9, 870), (10, 904), (11, 914), (12, 892), (13, 627), (14, 902), (15, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10322e) f439 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_22 code

theorem rest_l102bd0_20 [Bindings] (code : CodeMap) :
    Rest (n := 842) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 840), (13, 627), (14, 838), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]
      211 0x10318e bytes_l102bd0_20 b_l102bd0_20 := by
  have f400 : InstrSpec 0x10318e [0x4C, 0x0F, 0xAF, 0xE1] (fun s => s.RIP = 0x10318e) (imulR64R64Effect 0x10318e 4 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10318e 4 12 1).toInstrSpec (imul_r64_r64_effect_step 0x10318e 0x4c (by decide) 0xe1 (by decide)) pre_rip
  have f401 : InstrSpec 0x103192 [0x4D, 0x31, 0xF4] (fun s => s.RIP = 0x103192) (xorR64R64Effect 0x103192 12 14)
      [.gpr 12, .gpr 14] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103192 12 14).toInstrSpec (xor_r64_r64_effect_step 0x103192 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f402 : InstrSpec 0x103195 [0x49, 0x89, 0xDE] (fun s => s.RIP = 0x103195) (movR64R64Effect 0x103195 14 3)
      [.gpr 3] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103195 14 3).toInstrSpec (mov_r64_r64_effect_step 0x103195 0x49 0xde (by decide) (by decide)) pre_rip
  have f403 : InstrSpec 0x103198 [0x4C, 0x0F, 0xAF, 0xF5] (fun s => s.RIP = 0x103198) (imulR64R64Effect 0x103198 4 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103198 4 14 5).toInstrSpec (imul_r64_r64_effect_step 0x103198 0x4c (by decide) 0xf5 (by decide)) pre_rip
  have f404 : InstrSpec 0x10319c [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x10319c) (movR64R64Effect 0x10319c 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10319c 15 2).toInstrSpec (mov_r64_r64_effect_step 0x10319c 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f405 : InstrSpec 0x10319f [0x4C, 0x0F, 0xAF, 0xFF] (fun s => s.RIP = 0x10319f) (imulR64R64Effect 0x10319f 4 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10319f 4 15 7).toInstrSpec (imul_r64_r64_effect_step 0x10319f 0x4c (by decide) 0xff (by decide)) pre_rip
  have f406 : InstrSpec 0x1031a3 [0x4D, 0x31, 0xF7] (fun s => s.RIP = 0x1031a3) (xorR64R64Effect 0x1031a3 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1031a3 15 14).toInstrSpec (xor_r64_r64_effect_step 0x1031a3 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f407 : InstrSpec 0x1031a6 [0x4D, 0x31, 0xE7] (fun s => s.RIP = 0x1031a6) (xorR64R64Effect 0x1031a6 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1031a6 15 12).toInstrSpec (xor_r64_r64_effect_step 0x1031a6 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f408 : InstrSpec 0x1031a9 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x1031a9) (movR64R64Effect 0x1031a9 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1031a9 14 2).toInstrSpec (mov_r64_r64_effect_step 0x1031a9 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f409 : InstrSpec 0x1031ac [0x4C, 0x0F, 0xAF, 0xF5] (fun s => s.RIP = 0x1031ac) (imulR64R64Effect 0x1031ac 4 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1031ac 4 14 5).toInstrSpec (imul_r64_r64_effect_step 0x1031ac 0x4c (by decide) 0xf5 (by decide)) pre_rip
  have f410 : InstrSpec 0x1031b0 [0x49, 0x0F, 0xAF, 0xEA] (fun s => s.RIP = 0x1031b0) (imulR64R64Effect 0x1031b0 4 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1031b0 4 5 10).toInstrSpec (imul_r64_r64_effect_step 0x1031b0 0x49 (by decide) 0xea (by decide)) pre_rip
  have f411 : InstrSpec 0x1031b4 [0x4C, 0x0F, 0xAF, 0xD7] (fun s => s.RIP = 0x1031b4) (imulR64R64Effect 0x1031b4 4 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1031b4 4 10 7).toInstrSpec (imul_r64_r64_effect_step 0x1031b4 0x4c (by decide) 0xd7 (by decide)) pre_rip
  have f412 : InstrSpec 0x1031b8 [0x49, 0x0F, 0xAF, 0xF9] (fun s => s.RIP = 0x1031b8) (imulR64R64Effect 0x1031b8 4 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1031b8 4 7 9).toInstrSpec (imul_r64_r64_effect_step 0x1031b8 0x49 (by decide) 0xf9 (by decide)) pre_rip
  have f413 : InstrSpec 0x1031bc [0x4D, 0x0F, 0xAF, 0xC8] (fun s => s.RIP = 0x1031bc) (imulR64R64Effect 0x1031bc 4 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1031bc 4 9 8).toInstrSpec (imul_r64_r64_effect_step 0x1031bc 0x4d (by decide) 0xc8 (by decide)) pre_rip
  have f414 : InstrSpec 0x1031c0 [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x1031c0) (xorR64R64Effect 0x1031c0 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1031c0 9 10).toInstrSpec (xor_r64_r64_effect_step 0x1031c0 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f415 : InstrSpec 0x1031c3 [0x4C, 0x0F, 0xAF, 0xC3] (fun s => s.RIP = 0x1031c3) (imulR64R64Effect 0x1031c3 4 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1031c3 4 8 3).toInstrSpec (imul_r64_r64_effect_step 0x1031c3 0x4c (by decide) 0xc3 (by decide)) pre_rip
  have f416 : InstrSpec 0x1031c7 [0x48, 0x0F, 0xAF, 0xD9] (fun s => s.RIP = 0x1031c7) (imulR64R64Effect 0x1031c7 4 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1031c7 4 3 1).toInstrSpec (imul_r64_r64_effect_step 0x1031c7 0x48 (by decide) 0xd9 (by decide)) pre_rip
  have f417 : InstrSpec 0x1031cb [0x49, 0x31, 0xDE] (fun s => s.RIP = 0x1031cb) (xorR64R64Effect 0x1031cb 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1031cb 14 3).toInstrSpec (xor_r64_r64_effect_step 0x1031cb 0x49 0xde (by decide) (by decide)) pre_rip
  have f418 : InstrSpec 0x1031ce [0x4D, 0x31, 0xCE] (fun s => s.RIP = 0x1031ce) (xorR64R64Effect 0x1031ce 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1031ce 14 9).toInstrSpec (xor_r64_r64_effect_step 0x1031ce 0x4d 0xce (by decide) (by decide)) pre_rip
  have f419 : InstrSpec 0x1031d1 [0x48, 0x31, 0xEF] (fun s => s.RIP = 0x1031d1) (xorR64R64Effect 0x1031d1 7 5)
      [.gpr 7, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1031d1 7 5).toInstrSpec (xor_r64_r64_effect_step 0x1031d1 0x48 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 842) (RestInside.out (n := 842) f400 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 843) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 842), (13, 627), (14, 838), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103192) f400 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 844) (RestInside.out (n := 844) f401 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 845) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 838), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103195) f401 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 846) (RestInside.out (n := 846) f402 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 847) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 846), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103198) f402 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 848) (RestInside.out (n := 848) f403 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 849) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 848), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10319c) f403 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 850) (RestInside.out (n := 850) f404 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 851) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 848), (15, 850), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10319f) f404 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 852) (RestInside.out (n := 852) f405 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 853) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 848), (15, 852), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a3) f405 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 854) (RestInside.out (n := 854) f406 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 855) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 848), (15, 854), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a6) f406 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 856) (RestInside.out (n := 856) f407 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 857) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 848), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a9) f407 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 858) (RestInside.out (n := 858) f408 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 859) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 858), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031ac) f408 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 860) (RestInside.out (n := 860) f409 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 861) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 860), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b0) f409 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 862) (RestInside.out (n := 862) f410 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 863) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 862), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 844), (13, 627), (14, 860), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b4) f410 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 864) (RestInside.out (n := 864) f411 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 865) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 862), (6, 633), (7, 822), (8, 820), (9, 784), (10, 864), (11, 834), (12, 844), (13, 627), (14, 860), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b8) f411 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 866) (RestInside.out (n := 866) f412 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 867) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 862), (6, 633), (7, 866), (8, 820), (9, 784), (10, 864), (11, 834), (12, 844), (13, 627), (14, 860), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031bc) f412 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 868) (RestInside.out (n := 868) f413 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 869) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 862), (6, 633), (7, 866), (8, 820), (9, 868), (10, 864), (11, 834), (12, 844), (13, 627), (14, 860), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031c0) f413 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 870) (RestInside.out (n := 870) f414 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 871) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 862), (6, 633), (7, 866), (8, 820), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 860), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031c3) f414 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 872) (RestInside.out (n := 872) f415 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 873) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 862), (6, 633), (7, 866), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 860), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031c7) f415 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 874) (RestInside.out (n := 874) f416 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 875) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 866), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 860), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031cb) f416 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 876) (RestInside.out (n := 876) f417 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 877) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 866), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 876), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031ce) f417 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 878) (RestInside.out (n := 878) f418 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 879) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 866), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031d1) f418 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 880) (RestInside.out (n := 880) f419 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 881) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 874), (4, 65), (5, 862), (6, 633), (7, 880), (8, 872), (9, 870), (10, 864), (11, 834), (12, 844), (13, 627), (14, 878), (15, 856), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031d4) f419 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_21 code

theorem rest_l102bd0_19 [Bindings] (code : CodeMap) :
    Rest (n := 802) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 774), (1, 792), (2, 782), (3, 798), (4, 65), (5, 684), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 800), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]
      231 0x103146 bytes_l102bd0_19 b_l102bd0_19 := by
  have f380 : InstrSpec 0x103146 [0x4C, 0x0F, 0xAF, 0xD9] (fun s => s.RIP = 0x103146) (imulR64R64Effect 0x103146 4 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103146 4 11 1).toInstrSpec (imul_r64_r64_effect_step 0x103146 0x4c (by decide) 0xd9 (by decide)) pre_rip
  have f381 : InstrSpec 0x10314a [0x4D, 0x89, 0xCE] (fun s => s.RIP = 0x10314a) (movR64R64Effect 0x10314a 14 9)
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10314a 14 9).toInstrSpec (mov_r64_r64_effect_step 0x10314a 0x4d 0xce (by decide) (by decide)) pre_rip
  have f382 : InstrSpec 0x10314d [0x4C, 0x0F, 0xAF, 0xF3] (fun s => s.RIP = 0x10314d) (imulR64R64Effect 0x10314d 4 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10314d 4 14 3).toInstrSpec (imul_r64_r64_effect_step 0x10314d 0x4c (by decide) 0xf3 (by decide)) pre_rip
  have f383 : InstrSpec 0x103151 [0x48, 0x89, 0xDD] (fun s => s.RIP = 0x103151) (movR64R64Effect 0x103151 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103151 5 3).toInstrSpec (mov_r64_r64_effect_step 0x103151 0x48 0xdd (by decide) (by decide)) pre_rip
  have f384 : InstrSpec 0x103154 [0x4D, 0x31, 0xDE] (fun s => s.RIP = 0x103154) (xorR64R64Effect 0x103154 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103154 14 11).toInstrSpec (xor_r64_r64_effect_step 0x103154 0x4d 0xde (by decide) (by decide)) pre_rip
  have f385 : InstrSpec 0x103157 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x103157) (movR64R64Effect 0x103157 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103157 3 2).toInstrSpec (mov_r64_r64_effect_step 0x103157 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f386 : InstrSpec 0x10315a [0x49, 0xBB, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x10315a) (movR64Imm64Effect 0x10315a 11 0x4444444444444444)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x10315a 11 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x10315a 0x49 0xbb (by decide) (by decide) 0x4444444444444444) pre_rip
  have f387 : InstrSpec 0x103164 [0x4C, 0x21, 0xDB] (fun s => s.RIP = 0x103164) (andR64R64Effect 0x103164 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103164 3 11).toInstrSpec (and_r64_r64_effect_step 0x103164 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f388 : InstrSpec 0x103167 [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x103167) (andR64R64Effect 0x103167 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103167 2 15).toInstrSpec (and_r64_r64_effect_step 0x103167 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f389 : InstrSpec 0x10316a [0x4D, 0x21, 0xE0] (fun s => s.RIP = 0x10316a) (andR64R64Effect 0x10316a 8 12)
      [.gpr 8, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10316a 8 12).toInstrSpec (and_r64_r64_effect_step 0x10316a 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f390 : InstrSpec 0x10316d [0x4C, 0x21, 0xDF] (fun s => s.RIP = 0x10316d) (andR64R64Effect 0x10316d 7 11)
      [.gpr 7, .gpr 11] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10316d 7 11).toInstrSpec (and_r64_r64_effect_step 0x10316d 0x4c 0xdf (by decide) (by decide)) pre_rip
  have f391 : InstrSpec 0x103170 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x103170) (movR64R64Effect 0x103170 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x103170 15 3).toInstrSpec (mov_r64_r64_effect_step 0x103170 0x49 0xdf (by decide) (by decide)) pre_rip
  have f392 : InstrSpec 0x103173 [0x4C, 0x0F, 0xAF, 0xFF] (fun s => s.RIP = 0x103173) (imulR64R64Effect 0x103173 4 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103173 4 15 7).toInstrSpec (imul_r64_r64_effect_step 0x103173 0x4c (by decide) 0xff (by decide)) pre_rip
  have f393 : InstrSpec 0x103177 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x103177) (movR64R64Effect 0x103177 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x103177 11 2).toInstrSpec (mov_r64_r64_effect_step 0x103177 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f394 : InstrSpec 0x10317a [0x4D, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x10317a) (imulR64R64Effect 0x10317a 4 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10317a 4 11 8).toInstrSpec (imul_r64_r64_effect_step 0x10317a 0x4d (by decide) 0xd8 (by decide)) pre_rip
  have f395 : InstrSpec 0x10317e [0x4D, 0x31, 0xFB] (fun s => s.RIP = 0x10317e) (xorR64R64Effect 0x10317e 11 15)
      [.gpr 11, .gpr 15] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10317e 11 15).toInstrSpec (xor_r64_r64_effect_step 0x10317e 0x4d 0xfb (by decide) (by decide)) pre_rip
  have f396 : InstrSpec 0x103181 [0x4D, 0x31, 0xF3] (fun s => s.RIP = 0x103181) (xorR64R64Effect 0x103181 11 14)
      [.gpr 11, .gpr 14] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103181 11 14).toInstrSpec (xor_r64_r64_effect_step 0x103181 0x4d 0xf3 (by decide) (by decide)) pre_rip
  have f397 : InstrSpec 0x103184 [0x4D, 0x89, 0xD6] (fun s => s.RIP = 0x103184) (movR64R64Effect 0x103184 14 10)
      [.gpr 10] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103184 14 10).toInstrSpec (mov_r64_r64_effect_step 0x103184 0x4d 0xd6 (by decide) (by decide)) pre_rip
  have f398 : InstrSpec 0x103187 [0x4D, 0x0F, 0xAF, 0xF0] (fun s => s.RIP = 0x103187) (imulR64R64Effect 0x103187 4 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103187 4 14 8).toInstrSpec (imul_r64_r64_effect_step 0x103187 0x4d (by decide) 0xf0 (by decide)) pre_rip
  have f399 : InstrSpec 0x10318b [0x4D, 0x89, 0xCC] (fun s => s.RIP = 0x10318b) (movR64R64Effect 0x10318b 12 9)
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10318b 12 9).toInstrSpec (mov_r64_r64_effect_step 0x10318b 0x4d 0xcc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 802) (RestInside.out (n := 802) f380 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 803) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 798), (4, 65), (5, 684), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 802), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10314a) f380 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 804) (RestInside.out (n := 804) f381 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 805) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 798), (4, 65), (5, 684), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 802), (12, 786), (13, 627), (14, 804), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10314d) f381 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 806) (RestInside.out (n := 806) f382 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 807) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 798), (4, 65), (5, 684), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 802), (12, 786), (13, 627), (14, 806), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103151) f382 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 808) (RestInside.out (n := 808) f383 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 809) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 798), (4, 65), (5, 808), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 802), (12, 786), (13, 627), (14, 806), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103154) f383 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 810) (RestInside.out (n := 810) f384 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 811) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 798), (4, 65), (5, 808), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 802), (12, 786), (13, 627), (14, 810), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103157) f384 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 812) (RestInside.out (n := 812) f385 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 813) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 812), (4, 65), (5, 808), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 802), (12, 786), (13, 627), (14, 810), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10315a) f385 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 814) (RestInside.out (n := 814) f386 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 815) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 812), (4, 65), (5, 808), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 814), (12, 786), (13, 627), (14, 810), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103164) f386 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 816) (RestInside.out (n := 816) f387 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 817) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 816), (4, 65), (5, 808), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 814), (12, 786), (13, 627), (14, 810), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103167) f387 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 818) (RestInside.out (n := 818) f388 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 819) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 814), (12, 786), (13, 627), (14, 810), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10316a) f388 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 820) (RestInside.out (n := 820) f389 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 821) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 796), (8, 820), (9, 784), (10, 778), (11, 814), (12, 786), (13, 627), (14, 810), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10316d) f389 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 822) (RestInside.out (n := 822) f390 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 823) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 814), (12, 786), (13, 627), (14, 810), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103170) f390 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 824) (RestInside.out (n := 824) f391 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 825) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 814), (12, 786), (13, 627), (14, 810), (15, 824), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103173) f391 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 826) (RestInside.out (n := 826) f392 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 827) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 814), (12, 786), (13, 627), (14, 810), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103177) f392 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 828) (RestInside.out (n := 828) f393 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 829) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 828), (12, 786), (13, 627), (14, 810), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10317a) f393 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 830) (RestInside.out (n := 830) f394 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 831) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 830), (12, 786), (13, 627), (14, 810), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10317e) f394 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 832) (RestInside.out (n := 832) f395 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 833) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 832), (12, 786), (13, 627), (14, 810), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103181) f395 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 834) (RestInside.out (n := 834) f396 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 835) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 786), (13, 627), (14, 810), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103184) f396 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 836) (RestInside.out (n := 836) f397 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 837) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 786), (13, 627), (14, 836), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103187) f397 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 838) (RestInside.out (n := 838) f398 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 839) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 786), (13, 627), (14, 838), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10318b) f398 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 840) (RestInside.out (n := 840) f399 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 841) (ρ' := [(0, 774), (1, 792), (2, 818), (3, 816), (4, 65), (5, 808), (6, 633), (7, 822), (8, 820), (9, 784), (10, 778), (11, 834), (12, 840), (13, 627), (14, 838), (15, 826), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10318e) f399 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_20 code

theorem rest_l102bd0_18 [Bindings] (code : CodeMap) :
    Rest (n := 762) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 752), (1, 758), (2, 728), (3, 760), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]
      251 0x1030fa bytes_l102bd0_18 b_l102bd0_18 := by
  have f360 : InstrSpec 0x1030fa [0x4C, 0x09, 0xD3] (fun s => s.RIP = 0x1030fa) (orR64R64Effect 0x1030fa 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1030fa 3 10).toInstrSpec (or_r64_r64_effect_step 0x1030fa 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f361 : InstrSpec 0x1030fd [0x48, 0xBA, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x1030fd) (movR64Imm64Effect 0x1030fd 2 0x4444444444444444)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1030fd 2 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x1030fd 0x48 0xba (by decide) (by decide) 0x4444444444444444) pre_rip
  have f362 : InstrSpec 0x103107 [0x49, 0x21, 0xD6] (fun s => s.RIP = 0x103107) (andR64R64Effect 0x103107 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103107 14 2).toInstrSpec (and_r64_r64_effect_step 0x103107 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f363 : InstrSpec 0x10310a [0x49, 0x09, 0xDE] (fun s => s.RIP = 0x10310a) (orR64R64Effect 0x10310a 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10310a 14 3).toInstrSpec (or_r64_r64_effect_step 0x10310a 0x49 0xde (by decide) (by decide)) pre_rip
  have f364 : InstrSpec 0x10310d [0x49, 0xBF, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88] (fun s => s.RIP = 0x10310d) (movR64Imm64Effect 0x10310d 15 0x8888888888888888)
      [] [] [.reg 15, .rip] :=
    (movR64Imm64Effect_footprint 0x10310d 15 0x8888888888888888).toInstrSpec (mov_r64_imm64_effect_step 0x10310d 0x49 0xbf (by decide) (by decide) 0x8888888888888888) pre_rip
  have f365 : InstrSpec 0x103117 [0x4C, 0x21, 0xF8] (fun s => s.RIP = 0x103117) (andR64R64Effect 0x103117 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103117 0 15).toInstrSpec (and_r64_r64_effect_step 0x103117 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f366 : InstrSpec 0x10311a [0x4C, 0x09, 0xF0] (fun s => s.RIP = 0x10311a) (orR64R64Effect 0x10311a 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10311a 0 14).toInstrSpec (or_r64_r64_effect_step 0x10311a 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f367 : InstrSpec 0x10311d [0x4D, 0x89, 0xE2] (fun s => s.RIP = 0x10311d) (movR64R64Effect 0x10311d 10 12)
      [.gpr 12] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10311d 10 12).toInstrSpec (mov_r64_r64_effect_step 0x10311d 0x4d 0xe2 (by decide) (by decide)) pre_rip
  have f368 : InstrSpec 0x103120 [0x49, 0x21, 0xFA] (fun s => s.RIP = 0x103120) (andR64R64Effect 0x103120 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103120 10 7).toInstrSpec (and_r64_r64_effect_step 0x103120 0x49 0xfa (by decide) (by decide)) pre_rip
  have f369 : InstrSpec 0x103123 [0x4D, 0x89, 0xE1] (fun s => s.RIP = 0x103123) (movR64R64Effect 0x103123 9 12)
      [.gpr 12] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x103123 9 12).toInstrSpec (mov_r64_r64_effect_step 0x103123 0x4d 0xe1 (by decide) (by decide)) pre_rip
  have f370 : InstrSpec 0x103126 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x103126) (movR64R64Effect 0x103126 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103126 2 12).toInstrSpec (mov_r64_r64_effect_step 0x103126 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f371 : InstrSpec 0x103129 [0x49, 0x21, 0xC9] (fun s => s.RIP = 0x103129) (andR64R64Effect 0x103129 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103129 9 1).toInstrSpec (and_r64_r64_effect_step 0x103129 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f372 : InstrSpec 0x10312c [0x49, 0x89, 0xCC] (fun s => s.RIP = 0x10312c) (movR64R64Effect 0x10312c 12 1)
      [.gpr 1] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10312c 12 1).toInstrSpec (mov_r64_r64_effect_step 0x10312c 0x49 0xcc (by decide) (by decide)) pre_rip
  have f373 : InstrSpec 0x10312f [0x48, 0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x10312f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10312f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10312f 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10312f 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10312f 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f374 : InstrSpec 0x103134 [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x103134) (movR64R64Effect 0x103134 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103134 1 3).toInstrSpec (mov_r64_r64_effect_step 0x103134 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f375 : InstrSpec 0x103137 [0x48, 0x21, 0xF9] (fun s => s.RIP = 0x103137) (andR64R64Effect 0x103137 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103137 1 7).toInstrSpec (and_r64_r64_effect_step 0x103137 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f376 : InstrSpec 0x10313a [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x10313a) (movR64R64Effect 0x10313a 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10313a 8 3).toInstrSpec (mov_r64_r64_effect_step 0x10313a 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f377 : InstrSpec 0x10313d [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10313d) (movR64R64Effect 0x10313d 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10313d 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10313d 0x48 0xdf (by decide) (by decide)) pre_rip
  have f378 : InstrSpec 0x103140 [0x4C, 0x21, 0xFB] (fun s => s.RIP = 0x103140) (andR64R64Effect 0x103140 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103140 3 15).toInstrSpec (and_r64_r64_effect_step 0x103140 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f379 : InstrSpec 0x103143 [0x4D, 0x89, 0xD3] (fun s => s.RIP = 0x103143) (movR64R64Effect 0x103143 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x103143 11 10).toInstrSpec (mov_r64_r64_effect_step 0x103143 0x4d 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 762) (RestInside.out (n := 762) f360 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 763) (ρ' := [(0, 752), (1, 758), (2, 728), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030fd) f360 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 764) (RestInside.out (n := 764) f361 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 765) (ρ' := [(0, 752), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103107) f361 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 766) (RestInside.out (n := 766) f362 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 767) (ρ' := [(0, 752), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 766), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10310a) f362 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 768) (RestInside.out (n := 768) f363 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 769) (ρ' := [(0, 752), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 768), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10310d) f363 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 770) (RestInside.out (n := 770) f364 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 771) (ρ' := [(0, 752), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103117) f364 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 772) (RestInside.out (n := 772) f365 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 773) (ρ' := [(0, 772), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10311a) f365 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 774) (RestInside.out (n := 774) f366 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 775) (ρ' := [(0, 774), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10311d) f366 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 776) (RestInside.out (n := 776) f367 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 777) (ρ' := [(0, 774), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 776), (11, 740), (12, 671), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103120) f367 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 778) (RestInside.out (n := 778) f368 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 779) (ρ' := [(0, 774), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 778), (11, 740), (12, 671), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103123) f368 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 780) (RestInside.out (n := 780) f369 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 781) (ρ' := [(0, 774), (1, 758), (2, 764), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 780), (10, 778), (11, 740), (12, 671), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103126) f369 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 782) (RestInside.out (n := 782) f370 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 783) (ρ' := [(0, 774), (1, 758), (2, 782), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 780), (10, 778), (11, 740), (12, 671), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103129) f370 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 784) (RestInside.out (n := 784) f371 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 785) (ρ' := [(0, 774), (1, 758), (2, 782), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 784), (10, 778), (11, 740), (12, 671), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10312c) f371 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 786) (RestInside.out (n := 786) f372 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 787) (ρ' := [(0, 774), (1, 758), (2, 782), (3, 762), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 784), (10, 778), (11, 740), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10312f) f372 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 788) (RestInside.out (n := 788) f373 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 789) (ρ' := [(0, 774), (1, 758), (2, 782), (3, 788), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 784), (10, 778), (11, 740), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103134) f373 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 790) (RestInside.out (n := 790) f374 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 791) (ρ' := [(0, 774), (1, 790), (2, 782), (3, 788), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 784), (10, 778), (11, 740), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103137) f374 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 792) (RestInside.out (n := 792) f375 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 793) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 788), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 784), (10, 778), (11, 740), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10313a) f375 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 794) (RestInside.out (n := 794) f376 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 795) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 788), (4, 65), (5, 684), (6, 633), (7, 754), (8, 794), (9, 784), (10, 778), (11, 740), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10313d) f376 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 796) (RestInside.out (n := 796) f377 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 797) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 788), (4, 65), (5, 684), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 740), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103140) f377 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 798) (RestInside.out (n := 798) f378 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 799) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 798), (4, 65), (5, 684), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 740), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103143) f378 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 800) (RestInside.out (n := 800) f379 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 801) (ρ' := [(0, 774), (1, 792), (2, 782), (3, 798), (4, 65), (5, 684), (6, 633), (7, 796), (8, 794), (9, 784), (10, 778), (11, 800), (12, 786), (13, 627), (14, 768), (15, 770), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103146) f379 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_19 code

theorem rest_l102bd0_17 [Bindings] (code : CodeMap) :
    Rest (n := 722) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 653), (1, 688), (2, 659), (3, 720), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 710), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]
      271 0x1030a8 bytes_l102bd0_17 b_l102bd0_17 := by
  have f340 : InstrSpec 0x1030a8 [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x1030a8) (xorR64R64Effect 0x1030a8 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1030a8 3 14).toInstrSpec (xor_r64_r64_effect_step 0x1030a8 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f341 : InstrSpec 0x1030ab [0x49, 0x89, 0xEE] (fun s => s.RIP = 0x1030ab) (movR64R64Effect 0x1030ab 14 5)
      [.gpr 5] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1030ab 14 5).toInstrSpec (mov_r64_r64_effect_step 0x1030ab 0x49 0xee (by decide) (by decide)) pre_rip
  have f342 : InstrSpec 0x1030ae [0x4C, 0x0F, 0xAF, 0xF2] (fun s => s.RIP = 0x1030ae) (imulR64R64Effect 0x1030ae 4 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030ae 4 14 2).toInstrSpec (imul_r64_r64_effect_step 0x1030ae 0x4c (by decide) 0xf2 (by decide)) pre_rip
  have f343 : InstrSpec 0x1030b2 [0x49, 0x0F, 0xAF, 0xD1] (fun s => s.RIP = 0x1030b2) (imulR64R64Effect 0x1030b2 4 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030b2 4 2 9).toInstrSpec (imul_r64_r64_effect_step 0x1030b2 0x49 (by decide) 0xd1 (by decide)) pre_rip
  have f344 : InstrSpec 0x1030b6 [0x4C, 0x0F, 0xAF, 0xC9] (fun s => s.RIP = 0x1030b6) (imulR64R64Effect 0x1030b6 4 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030b6 4 9 1).toInstrSpec (imul_r64_r64_effect_step 0x1030b6 0x4c (by decide) 0xc9 (by decide)) pre_rip
  have f345 : InstrSpec 0x1030ba [0x48, 0x0F, 0xAF, 0xCF] (fun s => s.RIP = 0x1030ba) (imulR64R64Effect 0x1030ba 4 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030ba 4 1 7).toInstrSpec (imul_r64_r64_effect_step 0x1030ba 0x48 (by decide) 0xcf (by decide)) pre_rip
  have f346 : InstrSpec 0x1030be [0x49, 0x0F, 0xAF, 0xF8] (fun s => s.RIP = 0x1030be) (imulR64R64Effect 0x1030be 4 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030be 4 7 8).toInstrSpec (imul_r64_r64_effect_step 0x1030be 0x49 (by decide) 0xf8 (by decide)) pre_rip
  have f347 : InstrSpec 0x1030c2 [0x4C, 0x31, 0xCF] (fun s => s.RIP = 0x1030c2) (xorR64R64Effect 0x1030c2 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1030c2 7 9).toInstrSpec (xor_r64_r64_effect_step 0x1030c2 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f348 : InstrSpec 0x1030c5 [0x4D, 0x0F, 0xAF, 0xC3] (fun s => s.RIP = 0x1030c5) (imulR64R64Effect 0x1030c5 4 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030c5 4 8 11).toInstrSpec (imul_r64_r64_effect_step 0x1030c5 0x4d (by decide) 0xc3 (by decide)) pre_rip
  have f349 : InstrSpec 0x1030c9 [0x4C, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x1030c9) (imulR64R64Effect 0x1030c9 4 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030c9 4 11 0).toInstrSpec (imul_r64_r64_effect_step 0x1030c9 0x4c (by decide) 0xd8 (by decide)) pre_rip
  have f350 : InstrSpec 0x1030cd [0x4D, 0x31, 0xDE] (fun s => s.RIP = 0x1030cd) (xorR64R64Effect 0x1030cd 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1030cd 14 11).toInstrSpec (xor_r64_r64_effect_step 0x1030cd 0x4d 0xde (by decide) (by decide)) pre_rip
  have f351 : InstrSpec 0x1030d0 [0x49, 0x31, 0xFE] (fun s => s.RIP = 0x1030d0) (xorR64R64Effect 0x1030d0 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1030d0 14 7).toInstrSpec (xor_r64_r64_effect_step 0x1030d0 0x49 0xfe (by decide) (by decide)) pre_rip
  have f352 : InstrSpec 0x1030d3 [0x48, 0x31, 0xD1] (fun s => s.RIP = 0x1030d3) (xorR64R64Effect 0x1030d3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1030d3 1 2).toInstrSpec (xor_r64_r64_effect_step 0x1030d3 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f353 : InstrSpec 0x1030d6 [0x48, 0x0F, 0xAF, 0xC5] (fun s => s.RIP = 0x1030d6) (imulR64R64Effect 0x1030d6 4 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030d6 4 0 5).toInstrSpec (imul_r64_r64_effect_step 0x1030d6 0x48 (by decide) 0xc5 (by decide)) pre_rip
  have f354 : InstrSpec 0x1030da [0x4C, 0x31, 0xC0] (fun s => s.RIP = 0x1030da) (xorR64R64Effect 0x1030da 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1030da 0 8).toInstrSpec (xor_r64_r64_effect_step 0x1030da 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f355 : InstrSpec 0x1030dd [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x1030dd) (xorR64R64Effect 0x1030dd 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1030dd 0 1).toInstrSpec (xor_r64_r64_effect_step 0x1030dd 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f356 : InstrSpec 0x1030e0 [0x48, 0xBF, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11] (fun s => s.RIP = 0x1030e0) (movR64Imm64Effect 0x1030e0 7 0x1111111111111111)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x1030e0 7 0x1111111111111111).toInstrSpec (mov_r64_imm64_effect_step 0x1030e0 0x48 0xbf (by decide) (by decide) 0x1111111111111111) pre_rip
  have f357 : InstrSpec 0x1030ea [0x49, 0x21, 0xFA] (fun s => s.RIP = 0x1030ea) (andR64R64Effect 0x1030ea 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1030ea 10 7).toInstrSpec (and_r64_r64_effect_step 0x1030ea 0x49 0xfa (by decide) (by decide)) pre_rip
  have f358 : InstrSpec 0x1030ed [0x48, 0xB9, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22] (fun s => s.RIP = 0x1030ed) (movR64Imm64Effect 0x1030ed 1 0x2222222222222222)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1030ed 1 0x2222222222222222).toInstrSpec (mov_r64_imm64_effect_step 0x1030ed 0x48 0xb9 (by decide) (by decide) 0x2222222222222222) pre_rip
  have f359 : InstrSpec 0x1030f7 [0x48, 0x21, 0xCB] (fun s => s.RIP = 0x1030f7) (andR64R64Effect 0x1030f7 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1030f7 3 1).toInstrSpec (and_r64_r64_effect_step 0x1030f7 0x48 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 722) (RestInside.out (n := 722) f340 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 723) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 722), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 710), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030ab) f340 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 724) (RestInside.out (n := 724) f341 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 725) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 722), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 724), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030ae) f341 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 726) (RestInside.out (n := 726) f342 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 727) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 722), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 726), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030b2) f342 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 728) (RestInside.out (n := 728) f343 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 729) (ρ' := [(0, 653), (1, 688), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 726), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030b6) f343 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 730) (RestInside.out (n := 730) f344 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 731) (ρ' := [(0, 653), (1, 688), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 730), (10, 700), (11, 682), (12, 671), (13, 627), (14, 726), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030ba) f344 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 732) (RestInside.out (n := 732) f345 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 733) (ρ' := [(0, 653), (1, 732), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 730), (10, 700), (11, 682), (12, 671), (13, 627), (14, 726), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030be) f345 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 734) (RestInside.out (n := 734) f346 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 735) (ρ' := [(0, 653), (1, 732), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 734), (8, 686), (9, 730), (10, 700), (11, 682), (12, 671), (13, 627), (14, 726), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030c2) f346 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 736) (RestInside.out (n := 736) f347 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 737) (ρ' := [(0, 653), (1, 732), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 686), (9, 730), (10, 700), (11, 682), (12, 671), (13, 627), (14, 726), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030c5) f347 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 738) (RestInside.out (n := 738) f348 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 739) (ρ' := [(0, 653), (1, 732), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 738), (9, 730), (10, 700), (11, 682), (12, 671), (13, 627), (14, 726), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030c9) f348 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 740) (RestInside.out (n := 740) f349 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 741) (ρ' := [(0, 653), (1, 732), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 738), (9, 730), (10, 700), (11, 740), (12, 671), (13, 627), (14, 726), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030cd) f349 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 742) (RestInside.out (n := 742) f350 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 743) (ρ' := [(0, 653), (1, 732), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 738), (9, 730), (10, 700), (11, 740), (12, 671), (13, 627), (14, 742), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030d0) f350 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 744) (RestInside.out (n := 744) f351 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 745) (ρ' := [(0, 653), (1, 732), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 738), (9, 730), (10, 700), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030d3) f351 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 746) (RestInside.out (n := 746) f352 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 747) (ρ' := [(0, 653), (1, 746), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 738), (9, 730), (10, 700), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030d6) f352 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 748) (RestInside.out (n := 748) f353 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 749) (ρ' := [(0, 748), (1, 746), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 738), (9, 730), (10, 700), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030da) f353 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 750) (RestInside.out (n := 750) f354 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 751) (ρ' := [(0, 750), (1, 746), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 738), (9, 730), (10, 700), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030dd) f354 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 752) (RestInside.out (n := 752) f355 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 753) (ρ' := [(0, 752), (1, 746), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 736), (8, 738), (9, 730), (10, 700), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030e0) f355 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 754) (RestInside.out (n := 754) f356 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 755) (ρ' := [(0, 752), (1, 746), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 700), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030ea) f356 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 756) (RestInside.out (n := 756) f357 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 757) (ρ' := [(0, 752), (1, 746), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030ed) f357 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 758) (RestInside.out (n := 758) f358 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 759) (ρ' := [(0, 752), (1, 758), (2, 728), (3, 722), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030f7) f358 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 760) (RestInside.out (n := 760) f359 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 761) (ρ' := [(0, 752), (1, 758), (2, 728), (3, 760), (4, 65), (5, 684), (6, 633), (7, 754), (8, 738), (9, 730), (10, 756), (11, 740), (12, 671), (13, 627), (14, 744), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030fa) f359 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_18 code

theorem rest_l102bd0_16 [Bindings] (code : CodeMap) :
    Rest (n := 682) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 680), (11, 678), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]
      291 0x103066 bytes_l102bd0_16 b_l102bd0_16 := by
  have f320 : InstrSpec 0x103066 [0x4D, 0x21, 0xD3] (fun s => s.RIP = 0x103066) (andR64R64Effect 0x103066 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103066 11 10).toInstrSpec (and_r64_r64_effect_step 0x103066 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f321 : InstrSpec 0x103069 [0x4C, 0x21, 0xF5] (fun s => s.RIP = 0x103069) (andR64R64Effect 0x103069 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103069 5 14).toInstrSpec (and_r64_r64_effect_step 0x103069 0x4c 0xf5 (by decide) (by decide)) pre_rip
  have f322 : InstrSpec 0x10306c [0x4D, 0x21, 0xF8] (fun s => s.RIP = 0x10306c) (andR64R64Effect 0x10306c 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10306c 8 15).toInstrSpec (and_r64_r64_effect_step 0x10306c 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f323 : InstrSpec 0x10306f [0x4C, 0x21, 0xD1] (fun s => s.RIP = 0x10306f) (andR64R64Effect 0x10306f 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10306f 1 10).toInstrSpec (and_r64_r64_effect_step 0x10306f 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f324 : InstrSpec 0x103072 [0x4D, 0x89, 0xDE] (fun s => s.RIP = 0x103072) (movR64R64Effect 0x103072 14 11)
      [.gpr 11] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103072 14 11).toInstrSpec (mov_r64_r64_effect_step 0x103072 0x4d 0xde (by decide) (by decide)) pre_rip
  have f325 : InstrSpec 0x103075 [0x4C, 0x0F, 0xAF, 0xF1] (fun s => s.RIP = 0x103075) (imulR64R64Effect 0x103075 4 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103075 4 14 1).toInstrSpec (imul_r64_r64_effect_step 0x103075 0x4c (by decide) 0xf1 (by decide)) pre_rip
  have f326 : InstrSpec 0x103079 [0x49, 0x89, 0xEA] (fun s => s.RIP = 0x103079) (movR64R64Effect 0x103079 10 5)
      [.gpr 5] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x103079 10 5).toInstrSpec (mov_r64_r64_effect_step 0x103079 0x49 0xea (by decide) (by decide)) pre_rip
  have f327 : InstrSpec 0x10307c [0x4D, 0x0F, 0xAF, 0xD0] (fun s => s.RIP = 0x10307c) (imulR64R64Effect 0x10307c 4 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10307c 4 10 8).toInstrSpec (imul_r64_r64_effect_step 0x10307c 0x4d (by decide) 0xd0 (by decide)) pre_rip
  have f328 : InstrSpec 0x103080 [0x4D, 0x31, 0xF2] (fun s => s.RIP = 0x103080) (xorR64R64Effect 0x103080 10 14)
      [.gpr 10, .gpr 14] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103080 10 14).toInstrSpec (xor_r64_r64_effect_step 0x103080 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f329 : InstrSpec 0x103083 [0x49, 0x31, 0xDA] (fun s => s.RIP = 0x103083) (xorR64R64Effect 0x103083 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103083 10 3).toInstrSpec (xor_r64_r64_effect_step 0x103083 0x49 0xda (by decide) (by decide)) pre_rip
  have f330 : InstrSpec 0x103086 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x103086) (movR64R64Effect 0x103086 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103086 3 9).toInstrSpec (mov_r64_r64_effect_step 0x103086 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f331 : InstrSpec 0x103089 [0x49, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x103089) (imulR64R64Effect 0x103089 4 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103089 4 3 8).toInstrSpec (imul_r64_r64_effect_step 0x103089 0x49 (by decide) 0xd8 (by decide)) pre_rip
  have f332 : InstrSpec 0x10308d [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x10308d) (movR64R64Effect 0x10308d 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10308d 14 7).toInstrSpec (mov_r64_r64_effect_step 0x10308d 0x49 0xfe (by decide) (by decide)) pre_rip
  have f333 : InstrSpec 0x103090 [0x4C, 0x0F, 0xAF, 0xF0] (fun s => s.RIP = 0x103090) (imulR64R64Effect 0x103090 4 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103090 4 14 0).toInstrSpec (imul_r64_r64_effect_step 0x103090 0x4c (by decide) 0xf0 (by decide)) pre_rip
  have f334 : InstrSpec 0x103094 [0x49, 0x31, 0xDE] (fun s => s.RIP = 0x103094) (xorR64R64Effect 0x103094 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103094 14 3).toInstrSpec (xor_r64_r64_effect_step 0x103094 0x49 0xde (by decide) (by decide)) pre_rip
  have f335 : InstrSpec 0x103097 [0x4D, 0x89, 0xDF] (fun s => s.RIP = 0x103097) (movR64R64Effect 0x103097 15 11)
      [.gpr 11] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x103097 15 11).toInstrSpec (mov_r64_r64_effect_step 0x103097 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f336 : InstrSpec 0x10309a [0x4C, 0x0F, 0xAF, 0xFA] (fun s => s.RIP = 0x10309a) (imulR64R64Effect 0x10309a 4 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10309a 4 15 2).toInstrSpec (imul_r64_r64_effect_step 0x10309a 0x4c (by decide) 0xfa (by decide)) pre_rip
  have f337 : InstrSpec 0x10309e [0x48, 0x89, 0xEB] (fun s => s.RIP = 0x10309e) (movR64R64Effect 0x10309e 3 5)
      [.gpr 5] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10309e 3 5).toInstrSpec (mov_r64_r64_effect_step 0x10309e 0x48 0xeb (by decide) (by decide)) pre_rip
  have f338 : InstrSpec 0x1030a1 [0x48, 0x0F, 0xAF, 0xD9] (fun s => s.RIP = 0x1030a1) (imulR64R64Effect 0x1030a1 4 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1030a1 4 3 1).toInstrSpec (imul_r64_r64_effect_step 0x1030a1 0x48 (by decide) 0xd9 (by decide)) pre_rip
  have f339 : InstrSpec 0x1030a5 [0x4C, 0x31, 0xFB] (fun s => s.RIP = 0x1030a5) (xorR64R64Effect 0x1030a5 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1030a5 3 15).toInstrSpec (xor_r64_r64_effect_step 0x1030a5 0x4c 0xfb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 682) (RestInside.out (n := 682) f320 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 683) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 680), (11, 682), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103069) f320 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 684) (RestInside.out (n := 684) f321 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 685) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 655), (9, 641), (10, 680), (11, 682), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10306c) f321 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 686) (RestInside.out (n := 686) f322 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 687) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 680), (11, 682), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10306f) f322 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 688) (RestInside.out (n := 688) f323 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 689) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 680), (11, 682), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103072) f323 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 690) (RestInside.out (n := 690) f324 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 691) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 680), (11, 682), (12, 671), (13, 627), (14, 690), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103075) f324 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 692) (RestInside.out (n := 692) f325 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 693) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 680), (11, 682), (12, 671), (13, 627), (14, 692), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103079) f325 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 694) (RestInside.out (n := 694) f326 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 695) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 694), (11, 682), (12, 671), (13, 627), (14, 692), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10307c) f326 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 696) (RestInside.out (n := 696) f327 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 697) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 696), (11, 682), (12, 671), (13, 627), (14, 692), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103080) f327 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 698) (RestInside.out (n := 698) f328 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 699) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 698), (11, 682), (12, 671), (13, 627), (14, 692), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103083) f328 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 700) (RestInside.out (n := 700) f329 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 701) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 669), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 692), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103086) f329 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 702) (RestInside.out (n := 702) f330 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 703) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 702), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 692), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103089) f330 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 704) (RestInside.out (n := 704) f331 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 705) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 704), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 692), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10308d) f331 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 706) (RestInside.out (n := 706) f332 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 707) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 704), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 706), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103090) f332 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 708) (RestInside.out (n := 708) f333 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 709) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 704), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 708), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103094) f333 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 710) (RestInside.out (n := 710) f334 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 711) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 704), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 710), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103097) f334 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 712) (RestInside.out (n := 712) f335 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 713) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 704), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 710), (15, 712), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10309a) f335 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 714) (RestInside.out (n := 714) f336 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 715) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 704), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 710), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10309e) f336 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 716) (RestInside.out (n := 716) f337 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 717) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 716), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 710), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030a1) f337 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 718) (RestInside.out (n := 718) f338 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 719) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 718), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 710), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030a5) f338 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 720) (RestInside.out (n := 720) f339 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 721) (ρ' := [(0, 653), (1, 688), (2, 659), (3, 720), (4, 65), (5, 684), (6, 633), (7, 647), (8, 686), (9, 641), (10, 700), (11, 682), (12, 671), (13, 627), (14, 710), (15, 714), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030a8) f339 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_17 code

theorem rest_l102bd0_15 [Bindings] (code : CodeMap) :
    Rest (n := 643) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 635), (1, 639), (2, 631), (3, 621), (4, 65), (5, 517), (6, 633), (7, 609), (8, 611), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]
      311 0x10301e bytes_l102bd0_15 b_l102bd0_15 := by
  have f300 : InstrSpec 0x10301e [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10301e) (movR64R64Effect 0x10301e 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10301e 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10301e 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f301 : InstrSpec 0x103021 [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x103021) (movR64R64Effect 0x103021 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103021 5 0).toInstrSpec (mov_r64_r64_effect_step 0x103021 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f302 : InstrSpec 0x103024 [0x4C, 0x21, 0xC7] (fun s => s.RIP = 0x103024) (andR64R64Effect 0x103024 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103024 7 8).toInstrSpec (and_r64_r64_effect_step 0x103024 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f303 : InstrSpec 0x103027 [0x4D, 0x89, 0xC7] (fun s => s.RIP = 0x103027) (movR64R64Effect 0x103027 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x103027 15 8).toInstrSpec (mov_r64_r64_effect_step 0x103027 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f304 : InstrSpec 0x10302a [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x10302a) (movR64R64Effect 0x10302a 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10302a 0 2).toInstrSpec (mov_r64_r64_effect_step 0x10302a 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f305 : InstrSpec 0x10302d [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10302d) (andR64R64Effect 0x10302d 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10302d 0 1).toInstrSpec (and_r64_r64_effect_step 0x10302d 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f306 : InstrSpec 0x103030 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x103030) (movR64R64Effect 0x103030 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x103030 8 2).toInstrSpec (mov_r64_r64_effect_step 0x103030 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f307 : InstrSpec 0x103033 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x103033) (movR64R64Effect 0x103033 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103033 1 2).toInstrSpec (mov_r64_r64_effect_step 0x103033 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f308 : InstrSpec 0x103036 [0x4C, 0x21, 0xF2] (fun s => s.RIP = 0x103036) (andR64R64Effect 0x103036 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103036 2 14).toInstrSpec (and_r64_r64_effect_step 0x103036 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f309 : InstrSpec 0x103039 [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x103039) (movR64R64Effect 0x103039 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x103039 10 9).toInstrSpec (mov_r64_r64_effect_step 0x103039 0x4d 0xca (by decide) (by decide)) pre_rip
  have f310 : InstrSpec 0x10303c [0x4C, 0x0F, 0xAF, 0xD0] (fun s => s.RIP = 0x10303c) (imulR64R64Effect 0x10303c 4 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x10303c 4 10 0).toInstrSpec (imul_r64_r64_effect_step 0x10303c 0x4c (by decide) 0xd0 (by decide)) pre_rip
  have f311 : InstrSpec 0x103040 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x103040) (movR64R64Effect 0x103040 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103040 3 7).toInstrSpec (mov_r64_r64_effect_step 0x103040 0x48 0xfb (by decide) (by decide)) pre_rip
  have f312 : InstrSpec 0x103043 [0x48, 0x0F, 0xAF, 0xDA] (fun s => s.RIP = 0x103043) (imulR64R64Effect 0x103043 4 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103043 4 3 2).toInstrSpec (imul_r64_r64_effect_step 0x103043 0x48 (by decide) 0xda (by decide)) pre_rip
  have f313 : InstrSpec 0x103047 [0x4C, 0x31, 0xD3] (fun s => s.RIP = 0x103047) (xorR64R64Effect 0x103047 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103047 3 10).toInstrSpec (xor_r64_r64_effect_step 0x103047 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f314 : InstrSpec 0x10304a [0x4C, 0x8B, 0x64, 0x24, 0x18] (LoadPre 0x10304a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10304a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10304a 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10304a 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10304a 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f315 : InstrSpec 0x10304f [0x4D, 0x89, 0xE2] (fun s => s.RIP = 0x10304f) (movR64R64Effect 0x10304f 10 12)
      [.gpr 12] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10304f 10 12).toInstrSpec (mov_r64_r64_effect_step 0x10304f 0x4d 0xe2 (by decide) (by decide)) pre_rip
  have f316 : InstrSpec 0x103052 [0x49, 0x31, 0xEA] (fun s => s.RIP = 0x103052) (xorR64R64Effect 0x103052 10 5)
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x103052 10 5).toInstrSpec (xor_r64_r64_effect_step 0x103052 0x49 0xea (by decide) (by decide)) pre_rip
  have f317 : InstrSpec 0x103055 [0x4C, 0x89, 0x14, 0x24] (StorePre 0x103055 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103055 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103055 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103055 10 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x103055 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f318 : InstrSpec 0x103059 [0x49, 0x89, 0xEB] (fun s => s.RIP = 0x103059) (movR64R64Effect 0x103059 11 5)
      [.gpr 5] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x103059 11 5).toInstrSpec (mov_r64_r64_effect_step 0x103059 0x49 0xeb (by decide) (by decide)) pre_rip
  have f319 : InstrSpec 0x10305c [0x49, 0xBA, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x10305c) (movR64Imm64Effect 0x10305c 10 0x4444444444444444)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x10305c 10 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x10305c 0x49 0xba (by decide) (by decide) 0x4444444444444444) pre_rip
  refine Rest.ofInside (n := 643) (RestInside.out (n := 643) f300 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 644) (ρ' := [(0, 635), (1, 639), (2, 631), (3, 621), (4, 65), (5, 517), (6, 633), (7, 643), (8, 611), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103021) f300 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 645) (RestInside.out (n := 645) f301 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 646) (ρ' := [(0, 635), (1, 639), (2, 631), (3, 621), (4, 65), (5, 645), (6, 633), (7, 643), (8, 611), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103024) f301 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 647) (RestInside.out (n := 647) f302 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 648) (ρ' := [(0, 635), (1, 639), (2, 631), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 611), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103027) f302 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 649) (RestInside.out (n := 649) f303 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 650) (ρ' := [(0, 635), (1, 639), (2, 631), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 611), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10302a) f303 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 651) (RestInside.out (n := 651) f304 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 652) (ρ' := [(0, 651), (1, 639), (2, 631), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 611), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10302d) f304 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 653) (RestInside.out (n := 653) f305 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 654) (ρ' := [(0, 653), (1, 639), (2, 631), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 611), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103030) f305 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 655) (RestInside.out (n := 655) f306 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 656) (ρ' := [(0, 653), (1, 639), (2, 631), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103033) f306 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 657) (RestInside.out (n := 657) f307 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 658) (ρ' := [(0, 653), (1, 657), (2, 631), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103036) f307 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 659) (RestInside.out (n := 659) f308 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 660) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103039) f308 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 661) (RestInside.out (n := 661) f309 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 662) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 661), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10303c) f309 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 663) (RestInside.out (n := 663) f310 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 664) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 621), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 663), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103040) f310 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 665) (RestInside.out (n := 665) f311 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 666) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 665), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 663), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103043) f311 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 667) (RestInside.out (n := 667) f312 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 668) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 667), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 663), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103047) f312 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 669) (RestInside.out (n := 669) f313 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 670) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 663), (11, 615), (12, 539), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10304a) f313 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 671) (RestInside.out (n := 671) f314 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 672) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 663), (11, 615), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10304f) f314 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 673) (RestInside.out (n := 673) f315 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 674) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 673), (11, 615), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103052) f315 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 675) (RestInside.out (n := 675) f316 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 676) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 675), (11, 615), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103055) f316 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 677) (RestInside.exec (n := 677) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 675), (11, 615), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103059) f317 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 678) (RestInside.out (n := 678) f318 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 679) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 675), (11, 678), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10305c) f318 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 680) (RestInside.out (n := 680) f319 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 681) (ρ' := [(0, 653), (1, 657), (2, 659), (3, 669), (4, 65), (5, 645), (6, 633), (7, 647), (8, 655), (9, 641), (10, 680), (11, 678), (12, 671), (13, 627), (14, 623), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103066) f319 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_16 code

theorem rest_l102bd0_14 [Bindings] (code : CodeMap) :
    Rest (n := 603) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]
      331 0x102fce bytes_l102bd0_14 b_l102bd0_14 := by
  have f280 : InstrSpec 0x102fce [0x4D, 0x0F, 0xAF, 0xEC] (fun s => s.RIP = 0x102fce) (imulR64R64Effect 0x102fce 4 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102fce 4 13 12).toInstrSpec (imul_r64_r64_effect_step 0x102fce 0x4d (by decide) 0xec (by decide)) pre_rip
  have f281 : InstrSpec 0x102fd2 [0x4D, 0x31, 0xC5] (fun s => s.RIP = 0x102fd2) (xorR64R64Effect 0x102fd2 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102fd2 13 8).toInstrSpec (xor_r64_r64_effect_step 0x102fd2 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f282 : InstrSpec 0x102fd5 [0x49, 0x31, 0xC5] (fun s => s.RIP = 0x102fd5) (xorR64R64Effect 0x102fd5 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102fd5 13 0).toInstrSpec (xor_r64_r64_effect_step 0x102fd5 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f283 : InstrSpec 0x102fd8 [0x48, 0x21, 0xEF] (fun s => s.RIP = 0x102fd8) (andR64R64Effect 0x102fd8 7 5)
      [.gpr 7, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102fd8 7 5).toInstrSpec (and_r64_r64_effect_step 0x102fd8 0x48 0xef (by decide) (by decide)) pre_rip
  have f284 : InstrSpec 0x102fdb [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x102fdb) (movR64R64Effect 0x102fdb 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x102fdb 8 2).toInstrSpec (mov_r64_r64_effect_step 0x102fdb 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f285 : InstrSpec 0x102fde [0x49, 0x21, 0xD3] (fun s => s.RIP = 0x102fde) (andR64R64Effect 0x102fde 11 2)
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102fde 11 2).toInstrSpec (and_r64_r64_effect_step 0x102fde 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f286 : InstrSpec 0x102fe1 [0x49, 0x09, 0xFB] (fun s => s.RIP = 0x102fe1) (orR64R64Effect 0x102fe1 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102fe1 11 7).toInstrSpec (or_r64_r64_effect_step 0x102fe1 0x49 0xfb (by decide) (by decide)) pre_rip
  have f287 : InstrSpec 0x102fe4 [0x48, 0xB8, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x102fe4) (movR64Imm64Effect 0x102fe4 0 0x4444444444444444)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x102fe4 0 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x102fe4 0x48 0xb8 (by decide) (by decide) 0x4444444444444444) pre_rip
  have f288 : InstrSpec 0x102fee [0x48, 0x21, 0xC3] (fun s => s.RIP = 0x102fee) (andR64R64Effect 0x102fee 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102fee 3 0).toInstrSpec (and_r64_r64_effect_step 0x102fee 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f289 : InstrSpec 0x102ff1 [0x4C, 0x09, 0xDB] (fun s => s.RIP = 0x102ff1) (orR64R64Effect 0x102ff1 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102ff1 3 11).toInstrSpec (or_r64_r64_effect_step 0x102ff1 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f290 : InstrSpec 0x102ff4 [0x49, 0xBE, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88] (fun s => s.RIP = 0x102ff4) (movR64Imm64Effect 0x102ff4 14 0x8888888888888888)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x102ff4 14 0x8888888888888888).toInstrSpec (mov_r64_imm64_effect_step 0x102ff4 0x49 0xbe (by decide) (by decide) 0x8888888888888888) pre_rip
  have f291 : InstrSpec 0x102ffe [0x4D, 0x21, 0xF5] (fun s => s.RIP = 0x102ffe) (andR64R64Effect 0x102ffe 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102ffe 13 14).toInstrSpec (and_r64_r64_effect_step 0x102ffe 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f292 : InstrSpec 0x103001 [0x49, 0x09, 0xDD] (fun s => s.RIP = 0x103001) (orR64R64Effect 0x103001 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103001 13 3).toInstrSpec (or_r64_r64_effect_step 0x103001 0x49 0xdd (by decide) (by decide)) pre_rip
  have f293 : InstrSpec 0x103004 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x103004 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103004 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103004 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103004 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x103004 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f294 : InstrSpec 0x103009 [0x48, 0x8B, 0x14, 0x24] (LoadPre 0x103009 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103009 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103009 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103009 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103009 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f295 : InstrSpec 0x10300d [0x48, 0x31, 0xD6] (fun s => s.RIP = 0x10300d) (xorR64R64Effect 0x10300d 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10300d 6 2).toInstrSpec (xor_r64_r64_effect_step 0x10300d 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f296 : InstrSpec 0x103010 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x103010 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103010 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103010 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103010 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103010 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f297 : InstrSpec 0x103015 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x103015) (movR64R64Effect 0x103015 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x103015 9 0).toInstrSpec (mov_r64_r64_effect_step 0x103015 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f298 : InstrSpec 0x103018 [0x48, 0x89, 0xE9] (fun s => s.RIP = 0x103018) (movR64R64Effect 0x103018 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x103018 1 5).toInstrSpec (mov_r64_r64_effect_step 0x103018 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f299 : InstrSpec 0x10301b [0x49, 0x21, 0xE9] (fun s => s.RIP = 0x10301b) (andR64R64Effect 0x10301b 9 5)
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10301b 9 5).toInstrSpec (and_r64_r64_effect_step 0x10301b 0x49 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 603) (RestInside.out (n := 603) f280 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 604) (ρ' := [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 603), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd2) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 605) (RestInside.out (n := 605) f281 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 606) (ρ' := [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 605), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd5) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 607) (RestInside.out (n := 607) f282 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 608) (ρ' := [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 607), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd8) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 609) (RestInside.out (n := 609) f283 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 610) (ρ' := [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 609), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 607), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fdb) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 611) (RestInside.out (n := 611) f284 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 612) (ρ' := [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 577), (12, 539), (13, 607), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fde) f284 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 613) (RestInside.out (n := 613) f285 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 614) (ρ' := [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 613), (12, 539), (13, 607), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fe1) f285 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 615) (RestInside.out (n := 615) f286 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 616) (ρ' := [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 607), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fe4) f286 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 617) (RestInside.out (n := 617) f287 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 618) (ρ' := [(0, 617), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 607), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fee) f287 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 619) (RestInside.out (n := 619) f288 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 620) (ρ' := [(0, 617), (1, 591), (2, 488), (3, 619), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 607), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ff1) f288 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 621) (RestInside.out (n := 621) f289 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 622) (ρ' := [(0, 617), (1, 591), (2, 488), (3, 621), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 607), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ff4) f289 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 623) (RestInside.out (n := 623) f290 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 624) (ρ' := [(0, 617), (1, 591), (2, 488), (3, 621), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 607), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ffe) f290 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 625) (RestInside.out (n := 625) f291 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 626) (ρ' := [(0, 617), (1, 591), (2, 488), (3, 621), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 625), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103001) f291 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 627) (RestInside.out (n := 627) f292 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 628) (ρ' := [(0, 617), (1, 591), (2, 488), (3, 621), (4, 65), (5, 517), (6, 500), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103004) f292 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 629) (RestInside.out (n := 629) f293 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 630) (ρ' := [(0, 617), (1, 591), (2, 488), (3, 621), (4, 65), (5, 517), (6, 629), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103009) f293 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 631) (RestInside.out (n := 631) f294 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 632) (ρ' := [(0, 617), (1, 591), (2, 631), (3, 621), (4, 65), (5, 517), (6, 629), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10300d) f294 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 633) (RestInside.out (n := 633) f295 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 634) (ρ' := [(0, 617), (1, 591), (2, 631), (3, 621), (4, 65), (5, 517), (6, 633), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103010) f295 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 635) (RestInside.out (n := 635) f296 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 636) (ρ' := [(0, 635), (1, 591), (2, 631), (3, 621), (4, 65), (5, 517), (6, 633), (7, 609), (8, 611), (9, 585), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103015) f296 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 637) (RestInside.out (n := 637) f297 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 638) (ρ' := [(0, 635), (1, 591), (2, 631), (3, 621), (4, 65), (5, 517), (6, 633), (7, 609), (8, 611), (9, 637), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103018) f297 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 639) (RestInside.out (n := 639) f298 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 640) (ρ' := [(0, 635), (1, 639), (2, 631), (3, 621), (4, 65), (5, 517), (6, 633), (7, 609), (8, 611), (9, 637), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10301b) f298 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 641) (RestInside.out (n := 641) f299 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 642) (ρ' := [(0, 635), (1, 639), (2, 631), (3, 621), (4, 65), (5, 517), (6, 633), (7, 609), (8, 611), (9, 641), (10, 595), (11, 615), (12, 539), (13, 627), (14, 623), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10301e) f299 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_15 code

theorem rest_l102bd0_13 [Bindings] (code : CodeMap) :
    Rest (n := 563) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 543), (1, 511), (2, 488), (3, 561), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 559), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]
      351 0x102f88 bytes_l102bd0_13 b_l102bd0_13 := by
  have f260 : InstrSpec 0x102f88 [0x49, 0x0F, 0xAF, 0xDD] (fun s => s.RIP = 0x102f88) (imulR64R64Effect 0x102f88 4 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102f88 4 3 13).toInstrSpec (imul_r64_r64_effect_step 0x102f88 0x49 (by decide) 0xdd (by decide)) pre_rip
  have f261 : InstrSpec 0x102f8c [0x4C, 0x31, 0xDB] (fun s => s.RIP = 0x102f8c) (xorR64R64Effect 0x102f8c 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102f8c 3 11).toInstrSpec (xor_r64_r64_effect_step 0x102f8c 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f262 : InstrSpec 0x102f8f [0x4D, 0x89, 0xD6] (fun s => s.RIP = 0x102f8f) (movR64R64Effect 0x102f8f 14 10)
      [.gpr 10] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102f8f 14 10).toInstrSpec (mov_r64_r64_effect_step 0x102f8f 0x4d 0xd6 (by decide) (by decide)) pre_rip
  have f263 : InstrSpec 0x102f92 [0x4D, 0x0F, 0xAF, 0xF7] (fun s => s.RIP = 0x102f92) (imulR64R64Effect 0x102f92 4 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102f92 4 14 15).toInstrSpec (imul_r64_r64_effect_step 0x102f92 0x4d (by decide) 0xf7 (by decide)) pre_rip
  have f264 : InstrSpec 0x102f96 [0x4D, 0x89, 0xE3] (fun s => s.RIP = 0x102f96) (movR64R64Effect 0x102f96 11 12)
      [.gpr 12] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x102f96 11 12).toInstrSpec (mov_r64_r64_effect_step 0x102f96 0x4d 0xe3 (by decide) (by decide)) pre_rip
  have f265 : InstrSpec 0x102f99 [0x4C, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x102f99) (imulR64R64Effect 0x102f99 4 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102f99 4 11 0).toInstrSpec (imul_r64_r64_effect_step 0x102f99 0x4c (by decide) 0xd8 (by decide)) pre_rip
  have f266 : InstrSpec 0x102f9d [0x4D, 0x31, 0xF3] (fun s => s.RIP = 0x102f9d) (xorR64R64Effect 0x102f9d 11 14)
      [.gpr 11, .gpr 14] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102f9d 11 14).toInstrSpec (xor_r64_r64_effect_step 0x102f9d 0x4d 0xf3 (by decide) (by decide)) pre_rip
  have f267 : InstrSpec 0x102fa0 [0x49, 0x31, 0xDB] (fun s => s.RIP = 0x102fa0) (xorR64R64Effect 0x102fa0 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102fa0 11 3).toInstrSpec (xor_r64_r64_effect_step 0x102fa0 0x49 0xdb (by decide) (by decide)) pre_rip
  have f268 : InstrSpec 0x102fa3 [0x4C, 0x89, 0xE3] (fun s => s.RIP = 0x102fa3) (movR64R64Effect 0x102fa3 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x102fa3 3 12).toInstrSpec (mov_r64_r64_effect_step 0x102fa3 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f269 : InstrSpec 0x102fa6 [0x49, 0x0F, 0xAF, 0xDF] (fun s => s.RIP = 0x102fa6) (imulR64R64Effect 0x102fa6 4 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102fa6 4 3 15).toInstrSpec (imul_r64_r64_effect_step 0x102fa6 0x49 (by decide) 0xdf (by decide)) pre_rip
  have f270 : InstrSpec 0x102faa [0x4D, 0x0F, 0xAF, 0xF9] (fun s => s.RIP = 0x102faa) (imulR64R64Effect 0x102faa 4 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102faa 4 15 9).toInstrSpec (imul_r64_r64_effect_step 0x102faa 0x4d (by decide) 0xf9 (by decide)) pre_rip
  have f271 : InstrSpec 0x102fae [0x4C, 0x0F, 0xAF, 0xC8] (fun s => s.RIP = 0x102fae) (imulR64R64Effect 0x102fae 4 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102fae 4 9 0).toInstrSpec (imul_r64_r64_effect_step 0x102fae 0x4c (by decide) 0xc8 (by decide)) pre_rip
  have f272 : InstrSpec 0x102fb2 [0x48, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x102fb2) (imulR64R64Effect 0x102fb2 4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102fb2 4 0 1).toInstrSpec (imul_r64_r64_effect_step 0x102fb2 0x48 (by decide) 0xc1 (by decide)) pre_rip
  have f273 : InstrSpec 0x102fb6 [0x49, 0x0F, 0xAF, 0xC8] (fun s => s.RIP = 0x102fb6) (imulR64R64Effect 0x102fb6 4 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102fb6 4 1 8).toInstrSpec (imul_r64_r64_effect_step 0x102fb6 0x49 (by decide) 0xc8 (by decide)) pre_rip
  have f274 : InstrSpec 0x102fba [0x4C, 0x31, 0xC9] (fun s => s.RIP = 0x102fba) (xorR64R64Effect 0x102fba 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102fba 1 9).toInstrSpec (xor_r64_r64_effect_step 0x102fba 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f275 : InstrSpec 0x102fbd [0x4D, 0x0F, 0xAF, 0xC2] (fun s => s.RIP = 0x102fbd) (imulR64R64Effect 0x102fbd 4 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102fbd 4 8 10).toInstrSpec (imul_r64_r64_effect_step 0x102fbd 0x4d (by decide) 0xc2 (by decide)) pre_rip
  have f276 : InstrSpec 0x102fc1 [0x4D, 0x0F, 0xAF, 0xD5] (fun s => s.RIP = 0x102fc1) (imulR64R64Effect 0x102fc1 4 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102fc1 4 10 13).toInstrSpec (imul_r64_r64_effect_step 0x102fc1 0x4d (by decide) 0xd5 (by decide)) pre_rip
  have f277 : InstrSpec 0x102fc5 [0x4C, 0x31, 0xD3] (fun s => s.RIP = 0x102fc5) (xorR64R64Effect 0x102fc5 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102fc5 3 10).toInstrSpec (xor_r64_r64_effect_step 0x102fc5 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f278 : InstrSpec 0x102fc8 [0x48, 0x31, 0xCB] (fun s => s.RIP = 0x102fc8) (xorR64R64Effect 0x102fc8 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102fc8 3 1).toInstrSpec (xor_r64_r64_effect_step 0x102fc8 0x48 0xcb (by decide) (by decide)) pre_rip
  have f279 : InstrSpec 0x102fcb [0x4C, 0x31, 0xF8] (fun s => s.RIP = 0x102fcb) (xorR64R64Effect 0x102fcb 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102fcb 0 15).toInstrSpec (xor_r64_r64_effect_step 0x102fcb 0x4c 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 563) (RestInside.out (n := 563) f260 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 564) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 563), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 559), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f8c) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 565) (RestInside.out (n := 565) f261 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 566) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 565), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 559), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f8f) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 567) (RestInside.out (n := 567) f262 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 568) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 565), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 559), (12, 539), (13, 515), (14, 567), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f92) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 569) (RestInside.out (n := 569) f263 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 570) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 565), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 559), (12, 539), (13, 515), (14, 569), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f96) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 571) (RestInside.out (n := 571) f264 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 572) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 565), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 571), (12, 539), (13, 515), (14, 569), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f99) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 573) (RestInside.out (n := 573) f265 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 574) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 565), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 573), (12, 539), (13, 515), (14, 569), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f9d) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 575) (RestInside.out (n := 575) f266 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 576) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 565), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 575), (12, 539), (13, 515), (14, 569), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fa0) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 577) (RestInside.out (n := 577) f267 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 578) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 565), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fa3) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 579) (RestInside.out (n := 579) f268 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 580) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 579), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fa6) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 581) (RestInside.out (n := 581) f269 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 582) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 581), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102faa) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 583) (RestInside.out (n := 583) f270 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 584) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 581), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fae) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 585) (RestInside.out (n := 585) f271 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 586) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 581), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 585), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fb2) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 587) (RestInside.out (n := 587) f272 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 588) (ρ' := [(0, 587), (1, 511), (2, 488), (3, 581), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 585), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fb6) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 589) (RestInside.out (n := 589) f273 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 590) (ρ' := [(0, 587), (1, 589), (2, 488), (3, 581), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 585), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fba) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 591) (RestInside.out (n := 591) f274 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 592) (ρ' := [(0, 587), (1, 591), (2, 488), (3, 581), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 585), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fbd) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 593) (RestInside.out (n := 593) f275 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 594) (ρ' := [(0, 587), (1, 591), (2, 488), (3, 581), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 537), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc1) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 595) (RestInside.out (n := 595) f276 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 596) (ρ' := [(0, 587), (1, 591), (2, 488), (3, 581), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc5) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 597) (RestInside.out (n := 597) f277 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 598) (ρ' := [(0, 587), (1, 591), (2, 488), (3, 597), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc8) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 599) (RestInside.out (n := 599) f278 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 600) (ρ' := [(0, 587), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fcb) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 601) (RestInside.out (n := 601) f279 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 602) (ρ' := [(0, 601), (1, 591), (2, 488), (3, 599), (4, 65), (5, 517), (6, 500), (7, 555), (8, 593), (9, 585), (10, 595), (11, 577), (12, 539), (13, 515), (14, 569), (15, 583), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fce) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_14 code

theorem rest_l102bd0_12 [Bindings] (code : CodeMap) :
    Rest (n := 523) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 486), (8, 519), (9, 507), (10, 444), (11, 492), (12, 503), (13, 515), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]
      371 0x102f47 bytes_l102bd0_12 b_l102bd0_12 := by
  have f240 : InstrSpec 0x102f47 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x102f47) (andR64R64Effect 0x102f47 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f47 15 3).toInstrSpec (and_r64_r64_effect_step 0x102f47 0x49 0xdf (by decide) (by decide)) pre_rip
  have f241 : InstrSpec 0x102f4a [0x4C, 0x89, 0xCF] (fun s => s.RIP = 0x102f4a) (movR64R64Effect 0x102f4a 7 9)
      [.gpr 9] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102f4a 7 9).toInstrSpec (mov_r64_r64_effect_step 0x102f4a 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f242 : InstrSpec 0x102f4d [0x49, 0x0F, 0xAF, 0xFD] (fun s => s.RIP = 0x102f4d) (imulR64R64Effect 0x102f4d 4 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102f4d 4 7 13).toInstrSpec (imul_r64_r64_effect_step 0x102f4d 0x49 (by decide) 0xfd (by decide)) pre_rip
  have f243 : InstrSpec 0x102f51 [0x49, 0x89, 0xCB] (fun s => s.RIP = 0x102f51) (movR64R64Effect 0x102f51 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x102f51 11 1).toInstrSpec (mov_r64_r64_effect_step 0x102f51 0x49 0xcb (by decide) (by decide)) pre_rip
  have f244 : InstrSpec 0x102f54 [0x4D, 0x0F, 0xAF, 0xDF] (fun s => s.RIP = 0x102f54) (imulR64R64Effect 0x102f54 4 11 15)
      [.gpr 11, .gpr 15] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102f54 4 11 15).toInstrSpec (imul_r64_r64_effect_step 0x102f54 0x4d (by decide) 0xdf (by decide)) pre_rip
  have f245 : InstrSpec 0x102f58 [0x49, 0x31, 0xFB] (fun s => s.RIP = 0x102f58) (xorR64R64Effect 0x102f58 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102f58 11 7).toInstrSpec (xor_r64_r64_effect_step 0x102f58 0x49 0xfb (by decide) (by decide)) pre_rip
  have f246 : InstrSpec 0x102f5b [0x4D, 0x89, 0xE2] (fun s => s.RIP = 0x102f5b) (movR64R64Effect 0x102f5b 10 12)
      [.gpr 12] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x102f5b 10 12).toInstrSpec (mov_r64_r64_effect_step 0x102f5b 0x4d 0xe2 (by decide) (by decide)) pre_rip
  have f247 : InstrSpec 0x102f5e [0x4D, 0x21, 0xF2] (fun s => s.RIP = 0x102f5e) (andR64R64Effect 0x102f5e 10 14)
      [.gpr 10, .gpr 14] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f5e 10 14).toInstrSpec (and_r64_r64_effect_step 0x102f5e 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f248 : InstrSpec 0x102f61 [0x49, 0x21, 0xDC] (fun s => s.RIP = 0x102f61) (andR64R64Effect 0x102f61 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f61 12 3).toInstrSpec (and_r64_r64_effect_step 0x102f61 0x49 0xdc (by decide) (by decide)) pre_rip
  have f249 : InstrSpec 0x102f64 [0x49, 0x21, 0xD0] (fun s => s.RIP = 0x102f64) (andR64R64Effect 0x102f64 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f64 8 2).toInstrSpec (and_r64_r64_effect_step 0x102f64 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f250 : InstrSpec 0x102f67 [0x4C, 0x21, 0xF0] (fun s => s.RIP = 0x102f67) (andR64R64Effect 0x102f67 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f67 0 14).toInstrSpec (and_r64_r64_effect_step 0x102f67 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f251 : InstrSpec 0x102f6a [0x4C, 0x89, 0xD3] (fun s => s.RIP = 0x102f6a) (movR64R64Effect 0x102f6a 3 10)
      [.gpr 10] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x102f6a 3 10).toInstrSpec (mov_r64_r64_effect_step 0x102f6a 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f252 : InstrSpec 0x102f6d [0x48, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x102f6d) (imulR64R64Effect 0x102f6d 4 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102f6d 4 3 0).toInstrSpec (imul_r64_r64_effect_step 0x102f6d 0x48 (by decide) 0xd8 (by decide)) pre_rip
  have f253 : InstrSpec 0x102f71 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x102f71) (movR64R64Effect 0x102f71 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102f71 7 12).toInstrSpec (mov_r64_r64_effect_step 0x102f71 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f254 : InstrSpec 0x102f74 [0x49, 0x0F, 0xAF, 0xF8] (fun s => s.RIP = 0x102f74) (imulR64R64Effect 0x102f74 4 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102f74 4 7 8).toInstrSpec (imul_r64_r64_effect_step 0x102f74 0x49 (by decide) 0xf8 (by decide)) pre_rip
  have f255 : InstrSpec 0x102f78 [0x48, 0x31, 0xDF] (fun s => s.RIP = 0x102f78) (xorR64R64Effect 0x102f78 7 3)
      [.gpr 7, .gpr 3] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102f78 7 3).toInstrSpec (xor_r64_r64_effect_step 0x102f78 0x48 0xdf (by decide) (by decide)) pre_rip
  have f256 : InstrSpec 0x102f7b [0x4C, 0x31, 0xDF] (fun s => s.RIP = 0x102f7b) (xorR64R64Effect 0x102f7b 7 11)
      [.gpr 7, .gpr 11] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102f7b 7 11).toInstrSpec (xor_r64_r64_effect_step 0x102f7b 0x4c 0xdf (by decide) (by decide)) pre_rip
  have f257 : InstrSpec 0x102f7e [0x4D, 0x89, 0xCB] (fun s => s.RIP = 0x102f7e) (movR64R64Effect 0x102f7e 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x102f7e 11 9).toInstrSpec (mov_r64_r64_effect_step 0x102f7e 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f258 : InstrSpec 0x102f81 [0x4D, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x102f81) (imulR64R64Effect 0x102f81 4 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102f81 4 11 8).toInstrSpec (imul_r64_r64_effect_step 0x102f81 0x4d (by decide) 0xd8 (by decide)) pre_rip
  have f259 : InstrSpec 0x102f85 [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x102f85) (movR64R64Effect 0x102f85 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x102f85 3 1).toInstrSpec (mov_r64_r64_effect_step 0x102f85 0x48 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 523) (RestInside.out (n := 523) f240 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 524) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 486), (8, 519), (9, 507), (10, 444), (11, 492), (12, 503), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f4a) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 525) (RestInside.out (n := 525) f241 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 526) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 525), (8, 519), (9, 507), (10, 444), (11, 492), (12, 503), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f4d) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 527) (RestInside.out (n := 527) f242 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 528) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 519), (9, 507), (10, 444), (11, 492), (12, 503), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f51) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 529) (RestInside.out (n := 529) f243 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 530) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 519), (9, 507), (10, 444), (11, 529), (12, 503), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f54) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 531) (RestInside.out (n := 531) f244 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 532) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 519), (9, 507), (10, 444), (11, 531), (12, 503), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f58) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 533) (RestInside.out (n := 533) f245 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 534) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 519), (9, 507), (10, 444), (11, 533), (12, 503), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f5b) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 535) (RestInside.out (n := 535) f246 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 536) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 519), (9, 507), (10, 535), (11, 533), (12, 503), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f5e) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 537) (RestInside.out (n := 537) f247 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 538) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 519), (9, 507), (10, 537), (11, 533), (12, 503), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f61) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 539) (RestInside.out (n := 539) f248 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 540) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 519), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f64) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 541) (RestInside.out (n := 541) f249 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 542) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 541), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f67) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 543) (RestInside.out (n := 543) f250 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 544) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 527), (8, 541), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f6a) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 545) (RestInside.out (n := 545) f251 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 546) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 545), (4, 65), (5, 517), (6, 500), (7, 527), (8, 541), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f6d) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 547) (RestInside.out (n := 547) f252 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 548) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 547), (4, 65), (5, 517), (6, 500), (7, 527), (8, 541), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f71) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 549) (RestInside.out (n := 549) f253 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 550) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 547), (4, 65), (5, 517), (6, 500), (7, 549), (8, 541), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f74) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 551) (RestInside.out (n := 551) f254 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 552) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 547), (4, 65), (5, 517), (6, 500), (7, 551), (8, 541), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f78) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 553) (RestInside.out (n := 553) f255 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 554) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 547), (4, 65), (5, 517), (6, 500), (7, 553), (8, 541), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f7b) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 555) (RestInside.out (n := 555) f256 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 556) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 547), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 533), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f7e) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 557) (RestInside.out (n := 557) f257 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 558) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 547), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 557), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f81) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 559) (RestInside.out (n := 559) f258 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 560) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 547), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 559), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f85) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 561) (RestInside.out (n := 561) f259 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 562) (ρ' := [(0, 543), (1, 511), (2, 488), (3, 561), (4, 65), (5, 517), (6, 500), (7, 555), (8, 541), (9, 507), (10, 537), (11, 559), (12, 539), (13, 515), (14, 367), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f88) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_13 code

theorem rest_l102bd0_11 [Bindings] (code : CodeMap) :
    Rest (n := 484) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 476), (1, 466), (2, 460), (3, 371), (4, 65), (5, 474), (6, 482), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]
      391 0x102ef9 bytes_l102bd0_11 b_l102bd0_11 := by
  have f220 : InstrSpec 0x102ef9 [0x48, 0xB8, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11] (fun s => s.RIP = 0x102ef9) (movR64Imm64Effect 0x102ef9 0 0x1111111111111111)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x102ef9 0 0x1111111111111111).toInstrSpec (mov_r64_imm64_effect_step 0x102ef9 0x48 0xb8 (by decide) (by decide) 0x1111111111111111) pre_rip
  have f221 : InstrSpec 0x102f03 [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x102f03) (andR64R64Effect 0x102f03 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f03 7 0).toInstrSpec (and_r64_r64_effect_step 0x102f03 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f222 : InstrSpec 0x102f06 [0x48, 0xBA, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22] (fun s => s.RIP = 0x102f06) (movR64Imm64Effect 0x102f06 2 0x2222222222222222)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x102f06 2 0x2222222222222222).toInstrSpec (mov_r64_imm64_effect_step 0x102f06 0x48 0xba (by decide) (by decide) 0x2222222222222222) pre_rip
  have f223 : InstrSpec 0x102f10 [0x49, 0x21, 0xD3] (fun s => s.RIP = 0x102f10) (andR64R64Effect 0x102f10 11 2)
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f10 11 2).toInstrSpec (and_r64_r64_effect_step 0x102f10 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f224 : InstrSpec 0x102f13 [0x49, 0x09, 0xFB] (fun s => s.RIP = 0x102f13) (orR64R64Effect 0x102f13 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102f13 11 7).toInstrSpec (or_r64_r64_effect_step 0x102f13 0x49 0xfb (by decide) (by decide)) pre_rip
  have f225 : InstrSpec 0x102f16 [0x4C, 0x21, 0xF5] (fun s => s.RIP = 0x102f16) (andR64R64Effect 0x102f16 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f16 5 14).toInstrSpec (and_r64_r64_effect_step 0x102f16 0x4c 0xf5 (by decide) (by decide)) pre_rip
  have f226 : InstrSpec 0x102f19 [0x4C, 0x09, 0xDD] (fun s => s.RIP = 0x102f19) (orR64R64Effect 0x102f19 5 11)
      [.gpr 5, .gpr 11] [] [.reg 5, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102f19 5 11).toInstrSpec (or_r64_r64_effect_step 0x102f19 0x4c 0xdd (by decide) (by decide)) pre_rip
  have f227 : InstrSpec 0x102f1c [0x48, 0x21, 0xDE] (fun s => s.RIP = 0x102f1c) (andR64R64Effect 0x102f1c 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f1c 6 3).toInstrSpec (and_r64_r64_effect_step 0x102f1c 0x48 0xde (by decide) (by decide)) pre_rip
  have f228 : InstrSpec 0x102f1f [0x48, 0x09, 0xEE] (fun s => s.RIP = 0x102f1f) (orR64R64Effect 0x102f1f 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102f1f 6 5).toInstrSpec (or_r64_r64_effect_step 0x102f1f 0x48 0xee (by decide) (by decide)) pre_rip
  have f229 : InstrSpec 0x102f22 [0x48, 0x89, 0x74, 0x24, 0x28] (StorePre 0x102f22 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102f22 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102f22 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102f22 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x102f22 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f230 : InstrSpec 0x102f27 [0x4C, 0x8B, 0x64, 0x24, 0x10] (LoadPre 0x102f27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102f27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102f27 12 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x102f27 12 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x102f27 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f231 : InstrSpec 0x102f2c [0x4D, 0x89, 0xE1] (fun s => s.RIP = 0x102f2c) (movR64R64Effect 0x102f2c 9 12)
      [.gpr 12] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x102f2c 9 12).toInstrSpec (mov_r64_r64_effect_step 0x102f2c 0x4d 0xe1 (by decide) (by decide)) pre_rip
  have f232 : InstrSpec 0x102f2f [0x49, 0x21, 0xC1] (fun s => s.RIP = 0x102f2f) (andR64R64Effect 0x102f2f 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f2f 9 0).toInstrSpec (and_r64_r64_effect_step 0x102f2f 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f233 : InstrSpec 0x102f32 [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x102f32) (movR64R64Effect 0x102f32 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102f32 1 12).toInstrSpec (mov_r64_r64_effect_step 0x102f32 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f234 : InstrSpec 0x102f35 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x102f35) (andR64R64Effect 0x102f35 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f35 1 2).toInstrSpec (and_r64_r64_effect_step 0x102f35 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f235 : InstrSpec 0x102f38 [0x4D, 0x89, 0xFD] (fun s => s.RIP = 0x102f38) (movR64R64Effect 0x102f38 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x102f38 13 15).toInstrSpec (mov_r64_r64_effect_step 0x102f38 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f236 : InstrSpec 0x102f3b [0x49, 0x21, 0xC5] (fun s => s.RIP = 0x102f3b) (andR64R64Effect 0x102f3b 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102f3b 13 0).toInstrSpec (and_r64_r64_effect_step 0x102f3b 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f237 : InstrSpec 0x102f3e [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x102f3e) (movR64R64Effect 0x102f3e 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102f3e 5 0).toInstrSpec (mov_r64_r64_effect_step 0x102f3e 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f238 : InstrSpec 0x102f41 [0x4D, 0x89, 0xF8] (fun s => s.RIP = 0x102f41) (movR64R64Effect 0x102f41 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x102f41 8 15).toInstrSpec (mov_r64_r64_effect_step 0x102f41 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f239 : InstrSpec 0x102f44 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x102f44) (movR64R64Effect 0x102f44 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102f44 0 15).toInstrSpec (mov_r64_r64_effect_step 0x102f44 0x4c 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 484) (RestInside.out (n := 484) f220 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 485) (ρ' := [(0, 484), (1, 466), (2, 460), (3, 371), (4, 65), (5, 474), (6, 482), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f03) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 486) (RestInside.out (n := 486) f221 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 487) (ρ' := [(0, 484), (1, 466), (2, 460), (3, 371), (4, 65), (5, 474), (6, 482), (7, 486), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f06) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 488) (RestInside.out (n := 488) f222 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 489) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 474), (6, 482), (7, 486), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f10) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 490) (RestInside.out (n := 490) f223 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 491) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 474), (6, 482), (7, 486), (8, 468), (9, 470), (10, 444), (11, 490), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f13) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 492) (RestInside.out (n := 492) f224 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 493) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 474), (6, 482), (7, 486), (8, 468), (9, 470), (10, 444), (11, 492), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f16) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 494) (RestInside.out (n := 494) f225 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 495) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 494), (6, 482), (7, 486), (8, 468), (9, 470), (10, 444), (11, 492), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f19) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 496) (RestInside.out (n := 496) f226 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 497) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 496), (6, 482), (7, 486), (8, 468), (9, 470), (10, 444), (11, 492), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f1c) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 498) (RestInside.out (n := 498) f227 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 499) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 496), (6, 498), (7, 486), (8, 468), (9, 470), (10, 444), (11, 492), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f1f) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 500) (RestInside.out (n := 500) f228 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 501) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 470), (10, 444), (11, 492), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f22) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 502) (RestInside.exec (n := 502) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 470), (10, 444), (11, 492), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f27) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 503) (RestInside.out (n := 503) f230 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 504) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 470), (10, 444), (11, 492), (12, 503), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f2c) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 505) (RestInside.out (n := 505) f231 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 506) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 505), (10, 444), (11, 492), (12, 503), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f2f) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 507) (RestInside.out (n := 507) f232 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 508) (ρ' := [(0, 484), (1, 466), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 507), (10, 444), (11, 492), (12, 503), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f32) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 509) (RestInside.out (n := 509) f233 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 510) (ρ' := [(0, 484), (1, 509), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 507), (10, 444), (11, 492), (12, 503), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f35) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 511) (RestInside.out (n := 511) f234 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 512) (ρ' := [(0, 484), (1, 511), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 507), (10, 444), (11, 492), (12, 503), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f38) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 513) (RestInside.out (n := 513) f235 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 514) (ρ' := [(0, 484), (1, 511), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 507), (10, 444), (11, 492), (12, 503), (13, 513), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f3b) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 515) (RestInside.out (n := 515) f236 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 516) (ρ' := [(0, 484), (1, 511), (2, 488), (3, 371), (4, 65), (5, 496), (6, 500), (7, 486), (8, 468), (9, 507), (10, 444), (11, 492), (12, 503), (13, 515), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f3e) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 517) (RestInside.out (n := 517) f237 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 518) (ρ' := [(0, 484), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 486), (8, 468), (9, 507), (10, 444), (11, 492), (12, 503), (13, 515), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f41) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 519) (RestInside.out (n := 519) f238 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 520) (ρ' := [(0, 484), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 486), (8, 519), (9, 507), (10, 444), (11, 492), (12, 503), (13, 515), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f44) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 521) (RestInside.out (n := 521) f239 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 522) (ρ' := [(0, 521), (1, 511), (2, 488), (3, 371), (4, 65), (5, 517), (6, 500), (7, 486), (8, 519), (9, 507), (10, 444), (11, 492), (12, 503), (13, 515), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102f47) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_12 code

theorem rest_l102bd0_10 [Bindings] (code : CodeMap) :
    Rest (n := 444) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 440), (6, 392), (7, 430), (8, 416), (9, 412), (10, 442), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]
      411 0x102eb3 bytes_l102bd0_10 b_l102bd0_10 := by
  have f200 : InstrSpec 0x102eb3 [0x4D, 0x0F, 0xAF, 0xD5] (fun s => s.RIP = 0x102eb3) (imulR64R64Effect 0x102eb3 4 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102eb3 4 10 13).toInstrSpec (imul_r64_r64_effect_step 0x102eb3 0x4d (by decide) 0xd5 (by decide)) pre_rip
  have f201 : InstrSpec 0x102eb7 [0x4D, 0x89, 0xE3] (fun s => s.RIP = 0x102eb7) (movR64R64Effect 0x102eb7 11 12)
      [.gpr 12] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x102eb7 11 12).toInstrSpec (mov_r64_r64_effect_step 0x102eb7 0x4d 0xe3 (by decide) (by decide)) pre_rip
  have f202 : InstrSpec 0x102eba [0x4C, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x102eba) (imulR64R64Effect 0x102eba 4 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102eba 4 11 0).toInstrSpec (imul_r64_r64_effect_step 0x102eba 0x4c (by decide) 0xd8 (by decide)) pre_rip
  have f203 : InstrSpec 0x102ebe [0x4D, 0x31, 0xD3] (fun s => s.RIP = 0x102ebe) (xorR64R64Effect 0x102ebe 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102ebe 11 10).toInstrSpec (xor_r64_r64_effect_step 0x102ebe 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f204 : InstrSpec 0x102ec1 [0x49, 0x31, 0xEB] (fun s => s.RIP = 0x102ec1) (xorR64R64Effect 0x102ec1 11 5)
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102ec1 11 5).toInstrSpec (xor_r64_r64_effect_step 0x102ec1 0x49 0xeb (by decide) (by decide)) pre_rip
  have f205 : InstrSpec 0x102ec4 [0x4C, 0x89, 0xE5] (fun s => s.RIP = 0x102ec4) (movR64R64Effect 0x102ec4 5 12)
      [.gpr 12] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102ec4 5 12).toInstrSpec (mov_r64_r64_effect_step 0x102ec4 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f206 : InstrSpec 0x102ec7 [0x49, 0x0F, 0xAF, 0xED] (fun s => s.RIP = 0x102ec7) (imulR64R64Effect 0x102ec7 4 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ec7 4 5 13).toInstrSpec (imul_r64_r64_effect_step 0x102ec7 0x49 (by decide) 0xed (by decide)) pre_rip
  have f207 : InstrSpec 0x102ecb [0x4C, 0x0F, 0xAF, 0xEA] (fun s => s.RIP = 0x102ecb) (imulR64R64Effect 0x102ecb 4 13 2)
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ecb 4 13 2).toInstrSpec (imul_r64_r64_effect_step 0x102ecb 0x4c (by decide) 0xea (by decide)) pre_rip
  have f208 : InstrSpec 0x102ecf [0x48, 0x0F, 0xAF, 0xD0] (fun s => s.RIP = 0x102ecf) (imulR64R64Effect 0x102ecf 4 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ecf 4 2 0).toInstrSpec (imul_r64_r64_effect_step 0x102ecf 0x48 (by decide) 0xd0 (by decide)) pre_rip
  have f209 : InstrSpec 0x102ed3 [0x48, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x102ed3) (imulR64R64Effect 0x102ed3 4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ed3 4 0 1).toInstrSpec (imul_r64_r64_effect_step 0x102ed3 0x48 (by decide) 0xc1 (by decide)) pre_rip
  have f210 : InstrSpec 0x102ed7 [0x49, 0x0F, 0xAF, 0xC8] (fun s => s.RIP = 0x102ed7) (imulR64R64Effect 0x102ed7 4 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ed7 4 1 8).toInstrSpec (imul_r64_r64_effect_step 0x102ed7 0x49 (by decide) 0xc8 (by decide)) pre_rip
  have f211 : InstrSpec 0x102edb [0x48, 0x31, 0xD1] (fun s => s.RIP = 0x102edb) (xorR64R64Effect 0x102edb 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102edb 1 2).toInstrSpec (xor_r64_r64_effect_step 0x102edb 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f212 : InstrSpec 0x102ede [0x4D, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x102ede) (imulR64R64Effect 0x102ede 4 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ede 4 8 9).toInstrSpec (imul_r64_r64_effect_step 0x102ede 0x4d (by decide) 0xc1 (by decide)) pre_rip
  have f213 : InstrSpec 0x102ee2 [0x4C, 0x0F, 0xAF, 0xCE] (fun s => s.RIP = 0x102ee2) (imulR64R64Effect 0x102ee2 4 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ee2 4 9 6).toInstrSpec (imul_r64_r64_effect_step 0x102ee2 0x4c (by decide) 0xce (by decide)) pre_rip
  have f214 : InstrSpec 0x102ee6 [0x4C, 0x31, 0xCD] (fun s => s.RIP = 0x102ee6) (xorR64R64Effect 0x102ee6 5 9)
      [.gpr 5, .gpr 9] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102ee6 5 9).toInstrSpec (xor_r64_r64_effect_step 0x102ee6 0x4c 0xcd (by decide) (by decide)) pre_rip
  have f215 : InstrSpec 0x102ee9 [0x48, 0x31, 0xCD] (fun s => s.RIP = 0x102ee9) (xorR64R64Effect 0x102ee9 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102ee9 5 1).toInstrSpec (xor_r64_r64_effect_step 0x102ee9 0x48 0xcd (by decide) (by decide)) pre_rip
  have f216 : InstrSpec 0x102eec [0x4C, 0x31, 0xE8] (fun s => s.RIP = 0x102eec) (xorR64R64Effect 0x102eec 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102eec 0 13).toInstrSpec (xor_r64_r64_effect_step 0x102eec 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f217 : InstrSpec 0x102eef [0x49, 0x0F, 0xAF, 0xF4] (fun s => s.RIP = 0x102eef) (imulR64R64Effect 0x102eef 4 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102eef 4 6 12).toInstrSpec (imul_r64_r64_effect_step 0x102eef 0x49 (by decide) 0xf4 (by decide)) pre_rip
  have f218 : InstrSpec 0x102ef3 [0x4C, 0x31, 0xC6] (fun s => s.RIP = 0x102ef3) (xorR64R64Effect 0x102ef3 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102ef3 6 8).toInstrSpec (xor_r64_r64_effect_step 0x102ef3 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f219 : InstrSpec 0x102ef6 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x102ef6) (xorR64R64Effect 0x102ef6 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102ef6 6 0).toInstrSpec (xor_r64_r64_effect_step 0x102ef6 0x48 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 444) (RestInside.out (n := 444) f200 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 445) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 440), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eb7) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 446) (RestInside.out (n := 446) f201 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 447) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 440), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 446), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eba) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.out (n := 448) f202 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 449) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 440), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 448), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ebe) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 450) (RestInside.out (n := 450) f203 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 451) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 440), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 450), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ec1) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 452) (RestInside.out (n := 452) f204 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 453) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 440), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 452), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ec4) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.out (n := 454) f205 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 455) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 454), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 452), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ec7) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 456) (RestInside.out (n := 456) f206 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 457) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 456), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 452), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ecb) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f207 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 456), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ecf) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.out (n := 460) f208 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 461) (ρ' := [(0, 418), (1, 386), (2, 460), (3, 371), (4, 65), (5, 456), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ed3) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 462) (RestInside.out (n := 462) f209 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 463) (ρ' := [(0, 462), (1, 386), (2, 460), (3, 371), (4, 65), (5, 456), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ed7) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 464) (RestInside.out (n := 464) f210 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 465) (ρ' := [(0, 462), (1, 464), (2, 460), (3, 371), (4, 65), (5, 456), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102edb) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.out (n := 466) f211 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 467) (ρ' := [(0, 462), (1, 466), (2, 460), (3, 371), (4, 65), (5, 456), (6, 392), (7, 430), (8, 416), (9, 412), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ede) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 468) (RestInside.out (n := 468) f212 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 469) (ρ' := [(0, 462), (1, 466), (2, 460), (3, 371), (4, 65), (5, 456), (6, 392), (7, 430), (8, 468), (9, 412), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ee2) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 470) (RestInside.out (n := 470) f213 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 471) (ρ' := [(0, 462), (1, 466), (2, 460), (3, 371), (4, 65), (5, 456), (6, 392), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ee6) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 472) (RestInside.out (n := 472) f214 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 473) (ρ' := [(0, 462), (1, 466), (2, 460), (3, 371), (4, 65), (5, 472), (6, 392), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ee9) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 474) (RestInside.out (n := 474) f215 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 475) (ρ' := [(0, 462), (1, 466), (2, 460), (3, 371), (4, 65), (5, 474), (6, 392), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eec) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f216 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 477) (ρ' := [(0, 476), (1, 466), (2, 460), (3, 371), (4, 65), (5, 474), (6, 392), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eef) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 478) (RestInside.out (n := 478) f217 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 479) (ρ' := [(0, 476), (1, 466), (2, 460), (3, 371), (4, 65), (5, 474), (6, 478), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ef3) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 480) (RestInside.out (n := 480) f218 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 481) (ρ' := [(0, 476), (1, 466), (2, 460), (3, 371), (4, 65), (5, 474), (6, 480), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ef6) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 482) (RestInside.out (n := 482) f219 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 483) (ρ' := [(0, 476), (1, 466), (2, 460), (3, 371), (4, 65), (5, 474), (6, 482), (7, 430), (8, 468), (9, 470), (10, 444), (11, 452), (12, 414), (13, 458), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ef9) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_11 code

theorem rest_l102bd0_9 [Bindings] (code : CodeMap) :
    Rest (n := 404) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 394), (9, 340), (10, 342), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]
      431 0x102e72 bytes_l102bd0_9 b_l102bd0_9 := by
  have f180 : InstrSpec 0x102e72 [0x49, 0x89, 0xCA] (fun s => s.RIP = 0x102e72) (movR64R64Effect 0x102e72 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x102e72 10 1).toInstrSpec (mov_r64_r64_effect_step 0x102e72 0x49 0xca (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x102e75 [0x4D, 0x0F, 0xAF, 0xD5] (fun s => s.RIP = 0x102e75) (imulR64R64Effect 0x102e75 4 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102e75 4 10 13).toInstrSpec (imul_r64_r64_effect_step 0x102e75 0x4d (by decide) 0xd5 (by decide)) pre_rip
  have f182 : InstrSpec 0x102e79 [0x49, 0x31, 0xFA] (fun s => s.RIP = 0x102e79) (xorR64R64Effect 0x102e79 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102e79 10 7).toInstrSpec (xor_r64_r64_effect_step 0x102e79 0x49 0xfa (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x102e7c [0x4D, 0x89, 0xE1] (fun s => s.RIP = 0x102e7c) (movR64R64Effect 0x102e7c 9 12)
      [.gpr 12] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x102e7c 9 12).toInstrSpec (mov_r64_r64_effect_step 0x102e7c 0x4d 0xe1 (by decide) (by decide)) pre_rip
  have f184 : InstrSpec 0x102e7f [0x4D, 0x21, 0xF1] (fun s => s.RIP = 0x102e7f) (andR64R64Effect 0x102e7f 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e7f 9 14).toInstrSpec (and_r64_r64_effect_step 0x102e7f 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f185 : InstrSpec 0x102e82 [0x49, 0x21, 0xDC] (fun s => s.RIP = 0x102e82) (andR64R64Effect 0x102e82 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e82 12 3).toInstrSpec (and_r64_r64_effect_step 0x102e82 0x49 0xdc (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x102e85 [0x4D, 0x21, 0xD8] (fun s => s.RIP = 0x102e85) (andR64R64Effect 0x102e85 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e85 8 11).toInstrSpec (and_r64_r64_effect_step 0x102e85 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f187 : InstrSpec 0x102e88 [0x4C, 0x21, 0xF0] (fun s => s.RIP = 0x102e88) (andR64R64Effect 0x102e88 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e88 0 14).toInstrSpec (and_r64_r64_effect_step 0x102e88 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x102e8b [0x4D, 0x89, 0xCB] (fun s => s.RIP = 0x102e8b) (movR64R64Effect 0x102e8b 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x102e8b 11 9).toInstrSpec (mov_r64_r64_effect_step 0x102e8b 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f189 : InstrSpec 0x102e8e [0x4C, 0x0F, 0xAF, 0xD8] (fun s => s.RIP = 0x102e8e) (imulR64R64Effect 0x102e8e 4 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102e8e 4 11 0).toInstrSpec (imul_r64_r64_effect_step 0x102e8e 0x4c (by decide) 0xd8 (by decide)) pre_rip
  have f190 : InstrSpec 0x102e92 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x102e92) (movR64R64Effect 0x102e92 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102e92 7 12).toInstrSpec (mov_r64_r64_effect_step 0x102e92 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x102e95 [0x49, 0x0F, 0xAF, 0xF8] (fun s => s.RIP = 0x102e95) (imulR64R64Effect 0x102e95 4 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102e95 4 7 8).toInstrSpec (imul_r64_r64_effect_step 0x102e95 0x49 (by decide) 0xf8 (by decide)) pre_rip
  have f192 : InstrSpec 0x102e99 [0x4C, 0x31, 0xDF] (fun s => s.RIP = 0x102e99) (xorR64R64Effect 0x102e99 7 11)
      [.gpr 7, .gpr 11] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102e99 7 11).toInstrSpec (xor_r64_r64_effect_step 0x102e99 0x4c 0xdf (by decide) (by decide)) pre_rip
  have f193 : InstrSpec 0x102e9c [0x4C, 0x31, 0xD7] (fun s => s.RIP = 0x102e9c) (xorR64R64Effect 0x102e9c 7 10)
      [.gpr 7, .gpr 10] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102e9c 7 10).toInstrSpec (xor_r64_r64_effect_step 0x102e9c 0x4c 0xd7 (by decide) (by decide)) pre_rip
  have f194 : InstrSpec 0x102e9f [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x102e9f) (movR64R64Effect 0x102e9f 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x102e9f 10 2).toInstrSpec (mov_r64_r64_effect_step 0x102e9f 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f195 : InstrSpec 0x102ea2 [0x4D, 0x0F, 0xAF, 0xD0] (fun s => s.RIP = 0x102ea2) (imulR64R64Effect 0x102ea2 4 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ea2 4 10 8).toInstrSpec (imul_r64_r64_effect_step 0x102ea2 0x4d (by decide) 0xd0 (by decide)) pre_rip
  have f196 : InstrSpec 0x102ea6 [0x48, 0x89, 0xCD] (fun s => s.RIP = 0x102ea6) (movR64R64Effect 0x102ea6 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102ea6 5 1).toInstrSpec (mov_r64_r64_effect_step 0x102ea6 0x48 0xcd (by decide) (by decide)) pre_rip
  have f197 : InstrSpec 0x102ea9 [0x48, 0x0F, 0xAF, 0xEE] (fun s => s.RIP = 0x102ea9) (imulR64R64Effect 0x102ea9 4 5 6)
      [.gpr 5, .gpr 6] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ea9 4 5 6).toInstrSpec (imul_r64_r64_effect_step 0x102ea9 0x48 (by decide) 0xee (by decide)) pre_rip
  have f198 : InstrSpec 0x102ead [0x4C, 0x31, 0xD5] (fun s => s.RIP = 0x102ead) (xorR64R64Effect 0x102ead 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102ead 5 10).toInstrSpec (xor_r64_r64_effect_step 0x102ead 0x4c 0xd5 (by decide) (by decide)) pre_rip
  have f199 : InstrSpec 0x102eb0 [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x102eb0) (movR64R64Effect 0x102eb0 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x102eb0 10 9).toInstrSpec (mov_r64_r64_effect_step 0x102eb0 0x4d 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f180 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 394), (9, 340), (10, 404), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e75) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f181 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 407) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 394), (9, 340), (10, 406), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e79) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 408) (RestInside.out (n := 408) f182 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 409) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 394), (9, 340), (10, 408), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e7c) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f183 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 411) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 394), (9, 410), (10, 408), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e7f) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f184 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 413) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 394), (9, 412), (10, 408), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e82) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.out (n := 414) f185 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 415) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 394), (9, 412), (10, 408), (11, 388), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e85) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f186 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 416), (9, 412), (10, 408), (11, 388), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e88) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.out (n := 418) f187 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 419) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 416), (9, 412), (10, 408), (11, 388), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e8b) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 420) (RestInside.out (n := 420) f188 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 421) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 416), (9, 412), (10, 408), (11, 420), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e8e) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 422) (RestInside.out (n := 422) f189 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 423) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 416), (9, 412), (10, 408), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e92) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 424) (RestInside.out (n := 424) f190 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 425) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 424), (8, 416), (9, 412), (10, 408), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e95) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 426) (RestInside.out (n := 426) f191 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 427) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 426), (8, 416), (9, 412), (10, 408), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e99) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f192 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 428), (8, 416), (9, 412), (10, 408), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e9c) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.out (n := 430) f193 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 431) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 430), (8, 416), (9, 412), (10, 408), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e9f) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 432) (RestInside.out (n := 432) f194 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 433) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 430), (8, 416), (9, 412), (10, 432), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ea2) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 434) (RestInside.out (n := 434) f195 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 435) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 430), (8, 416), (9, 412), (10, 434), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ea6) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 436) (RestInside.out (n := 436) f196 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 437) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 436), (6, 392), (7, 430), (8, 416), (9, 412), (10, 434), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ea9) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 438) (RestInside.out (n := 438) f197 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 439) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 438), (6, 392), (7, 430), (8, 416), (9, 412), (10, 434), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ead) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f198 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 441) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 440), (6, 392), (7, 430), (8, 416), (9, 412), (10, 434), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eb0) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.out (n := 442) f199 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 443) (ρ' := [(0, 418), (1, 386), (2, 382), (3, 371), (4, 65), (5, 440), (6, 392), (7, 430), (8, 416), (9, 412), (10, 442), (11, 422), (12, 414), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102eb3) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_10 code

theorem rest_l102bd0_8 [Bindings] (code : CodeMap) :
    Rest (n := 366) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 360), (1, 356), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 364), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]
      451 0x102e23 bytes_l102bd0_8 b_l102bd0_8 := by
  have f160 : InstrSpec 0x102e23 [0x48, 0x89, 0x7C, 0x24, 0x38] (StorePre 0x102e23 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102e23 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102e23 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102e23 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x102e23 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f161 : InstrSpec 0x102e28 [0x49, 0xBE, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x102e28) (movR64Imm64Effect 0x102e28 14 0x4444444444444444)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x102e28 14 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x102e28 0x49 0xbe (by decide) (by decide) 0x4444444444444444) pre_rip
  have f162 : InstrSpec 0x102e32 [0x4C, 0x21, 0xF5] (fun s => s.RIP = 0x102e32) (andR64R64Effect 0x102e32 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e32 5 14).toInstrSpec (and_r64_r64_effect_step 0x102e32 0x4c 0xf5 (by decide) (by decide)) pre_rip
  have f163 : InstrSpec 0x102e35 [0x48, 0xBB, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88] (fun s => s.RIP = 0x102e35) (movR64Imm64Effect 0x102e35 3 0x8888888888888888)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x102e35 3 0x8888888888888888).toInstrSpec (mov_r64_imm64_effect_step 0x102e35 0x48 0xbb (by decide) (by decide) 0x8888888888888888) pre_rip
  have f164 : InstrSpec 0x102e3f [0x49, 0x21, 0xD8] (fun s => s.RIP = 0x102e3f) (andR64R64Effect 0x102e3f 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e3f 8 3).toInstrSpec (and_r64_r64_effect_step 0x102e3f 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x102e42 [0x49, 0x09, 0xE8] (fun s => s.RIP = 0x102e42) (orR64R64Effect 0x102e42 8 5)
      [.gpr 8, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102e42 8 5).toInstrSpec (or_r64_r64_effect_step 0x102e42 0x49 0xe8 (by decide) (by decide)) pre_rip
  have f166 : InstrSpec 0x102e45 [0x4C, 0x89, 0x44, 0x24, 0x30] (StorePre 0x102e45 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x102e45 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102e45 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102e45 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x102e45 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f167 : InstrSpec 0x102e4a [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x102e4a) (movR64R64Effect 0x102e4a 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x102e4a 2 12).toInstrSpec (mov_r64_r64_effect_step 0x102e4a 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x102e4d [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x102e4d) (movR64R64Effect 0x102e4d 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102e4d 7 1).toInstrSpec (mov_r64_r64_effect_step 0x102e4d 0x48 0xcf (by decide) (by decide)) pre_rip
  have f169 : InstrSpec 0x102e50 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x102e50) (andR64R64Effect 0x102e50 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e50 2 1).toInstrSpec (and_r64_r64_effect_step 0x102e50 0x48 0xca (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x102e53 [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x102e53) (movR64R64Effect 0x102e53 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102e53 1 12).toInstrSpec (mov_r64_r64_effect_step 0x102e53 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x102e56 [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x102e56) (andR64R64Effect 0x102e56 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e56 1 0).toInstrSpec (and_r64_r64_effect_step 0x102e56 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f172 : InstrSpec 0x102e59 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x102e59) (movR64R64Effect 0x102e59 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x102e59 11 0).toInstrSpec (mov_r64_r64_effect_step 0x102e59 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f173 : InstrSpec 0x102e5c [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x102e5c) (movR64R64Effect 0x102e5c 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102e5c 6 13).toInstrSpec (mov_r64_r64_effect_step 0x102e5c 0x4c 0xee (by decide) (by decide)) pre_rip
  have f174 : InstrSpec 0x102e5f [0x48, 0x21, 0xFE] (fun s => s.RIP = 0x102e5f) (andR64R64Effect 0x102e5f 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e5f 6 7).toInstrSpec (and_r64_r64_effect_step 0x102e5f 0x48 0xfe (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x102e62 [0x4D, 0x89, 0xE8] (fun s => s.RIP = 0x102e62) (movR64R64Effect 0x102e62 8 13)
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x102e62 8 13).toInstrSpec (mov_r64_r64_effect_step 0x102e62 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f176 : InstrSpec 0x102e65 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x102e65) (movR64R64Effect 0x102e65 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102e65 0 13).toInstrSpec (mov_r64_r64_effect_step 0x102e65 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x102e68 [0x49, 0x21, 0xDD] (fun s => s.RIP = 0x102e68) (andR64R64Effect 0x102e68 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e68 13 3).toInstrSpec (and_r64_r64_effect_step 0x102e68 0x49 0xdd (by decide) (by decide)) pre_rip
  have f178 : InstrSpec 0x102e6b [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x102e6b) (movR64R64Effect 0x102e6b 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102e6b 7 2).toInstrSpec (mov_r64_r64_effect_step 0x102e6b 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f179 : InstrSpec 0x102e6e [0x48, 0x0F, 0xAF, 0xFE] (fun s => s.RIP = 0x102e6e) (imulR64R64Effect 0x102e6e 4 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102e6e 4 7 6).toInstrSpec (imul_r64_r64_effect_step 0x102e6e 0x48 (by decide) 0xfe (by decide)) pre_rip
  refine Rest.ofInside (n := 366) (RestInside.exec (n := 366) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 364), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e28) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f161 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 364), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e32) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f162 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 370) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 251), (4, 65), (5, 369), (6, 348), (7, 364), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e35) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f163 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 371), (4, 65), (5, 369), (6, 348), (7, 364), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e3f) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f164 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 371), (4, 65), (5, 369), (6, 348), (7, 364), (8, 373), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e42) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f165 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 376) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 371), (4, 65), (5, 369), (6, 348), (7, 364), (8, 375), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e45) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 377) (RestInside.exec (n := 377) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 371), (4, 65), (5, 369), (6, 348), (7, 364), (8, 375), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e4a) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f167 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 360), (1, 356), (2, 378), (3, 371), (4, 65), (5, 369), (6, 348), (7, 364), (8, 375), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e4d) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f168 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 360), (1, 356), (2, 378), (3, 371), (4, 65), (5, 369), (6, 348), (7, 380), (8, 375), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e50) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f169 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 360), (1, 356), (2, 382), (3, 371), (4, 65), (5, 369), (6, 348), (7, 380), (8, 375), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e53) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.out (n := 384) f170 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 385) (ρ' := [(0, 360), (1, 384), (2, 382), (3, 371), (4, 65), (5, 369), (6, 348), (7, 380), (8, 375), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e56) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 386) (RestInside.out (n := 386) f171 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 387) (ρ' := [(0, 360), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 348), (7, 380), (8, 375), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e59) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.out (n := 388) f172 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 389) (ρ' := [(0, 360), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 348), (7, 380), (8, 375), (9, 340), (10, 342), (11, 388), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e5c) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 390) (RestInside.out (n := 390) f173 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 391) (ρ' := [(0, 360), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 390), (7, 380), (8, 375), (9, 340), (10, 342), (11, 388), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e5f) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 392) (RestInside.out (n := 392) f174 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 393) (ρ' := [(0, 360), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 380), (8, 375), (9, 340), (10, 342), (11, 388), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e62) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.out (n := 394) f175 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 395) (ρ' := [(0, 360), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 380), (8, 394), (9, 340), (10, 342), (11, 388), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e65) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 396) (RestInside.out (n := 396) f176 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 397) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 380), (8, 394), (9, 340), (10, 342), (11, 388), (12, 158), (13, 71), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e68) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f177 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 380), (8, 394), (9, 340), (10, 342), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e6b) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.out (n := 400) f178 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 401) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 400), (8, 394), (9, 340), (10, 342), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e6e) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 402) (RestInside.out (n := 402) f179 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 403) (ρ' := [(0, 396), (1, 386), (2, 382), (3, 371), (4, 65), (5, 369), (6, 392), (7, 402), (8, 394), (9, 340), (10, 342), (11, 388), (12, 158), (13, 398), (14, 367), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e72) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_9 code

theorem rest_l102bd0_7 [Bindings] (code : CodeMap) :
    Rest (n := 326) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 316), (6, 261), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]
      471 0x102dd1 bytes_l102bd0_7 b_l102bd0_7 := by
  have f140 : InstrSpec 0x102dd1 [0x48, 0x89, 0xDD] (fun s => s.RIP = 0x102dd1) (movR64R64Effect 0x102dd1 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102dd1 5 3).toInstrSpec (mov_r64_r64_effect_step 0x102dd1 0x48 0xdd (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x102dd4 [0x49, 0x0F, 0xAF, 0xEE] (fun s => s.RIP = 0x102dd4) (imulR64R64Effect 0x102dd4 4 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102dd4 4 5 14).toInstrSpec (imul_r64_r64_effect_step 0x102dd4 0x49 (by decide) 0xee (by decide)) pre_rip
  have f142 : InstrSpec 0x102dd8 [0x4C, 0x0F, 0xAF, 0xF0] (fun s => s.RIP = 0x102dd8) (imulR64R64Effect 0x102dd8 4 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102dd8 4 14 0).toInstrSpec (imul_r64_r64_effect_step 0x102dd8 0x4c (by decide) 0xf0 (by decide)) pre_rip
  have f143 : InstrSpec 0x102ddc [0x48, 0x0F, 0xAF, 0xC6] (fun s => s.RIP = 0x102ddc) (imulR64R64Effect 0x102ddc 4 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102ddc 4 0 6).toInstrSpec (imul_r64_r64_effect_step 0x102ddc 0x48 (by decide) 0xc6 (by decide)) pre_rip
  have f144 : InstrSpec 0x102de0 [0x48, 0x0F, 0xAF, 0xF2] (fun s => s.RIP = 0x102de0) (imulR64R64Effect 0x102de0 4 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102de0 4 6 2).toInstrSpec (imul_r64_r64_effect_step 0x102de0 0x48 (by decide) 0xf2 (by decide)) pre_rip
  have f145 : InstrSpec 0x102de4 [0x49, 0x0F, 0xAF, 0xD1] (fun s => s.RIP = 0x102de4) (imulR64R64Effect 0x102de4 4 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102de4 4 2 9).toInstrSpec (imul_r64_r64_effect_step 0x102de4 0x49 (by decide) 0xd1 (by decide)) pre_rip
  have f146 : InstrSpec 0x102de8 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x102de8) (xorR64R64Effect 0x102de8 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102de8 2 0).toInstrSpec (xor_r64_r64_effect_step 0x102de8 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f147 : InstrSpec 0x102deb [0x4D, 0x0F, 0xAF, 0xCA] (fun s => s.RIP = 0x102deb) (imulR64R64Effect 0x102deb 4 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102deb 4 9 10).toInstrSpec (imul_r64_r64_effect_step 0x102deb 0x4d (by decide) 0xca (by decide)) pre_rip
  have f148 : InstrSpec 0x102def [0x4D, 0x0F, 0xAF, 0xD0] (fun s => s.RIP = 0x102def) (imulR64R64Effect 0x102def 4 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102def 4 10 8).toInstrSpec (imul_r64_r64_effect_step 0x102def 0x4d (by decide) 0xd0 (by decide)) pre_rip
  have f149 : InstrSpec 0x102df3 [0x4C, 0x31, 0xD5] (fun s => s.RIP = 0x102df3) (xorR64R64Effect 0x102df3 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102df3 5 10).toInstrSpec (xor_r64_r64_effect_step 0x102df3 0x4c 0xd5 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x102df6 [0x48, 0x31, 0xD5] (fun s => s.RIP = 0x102df6) (xorR64R64Effect 0x102df6 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102df6 5 2).toInstrSpec (xor_r64_r64_effect_step 0x102df6 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x102df9 [0x4C, 0x31, 0xF6] (fun s => s.RIP = 0x102df9) (xorR64R64Effect 0x102df9 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102df9 6 14).toInstrSpec (xor_r64_r64_effect_step 0x102df9 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x102dfc [0x4C, 0x0F, 0xAF, 0xC3] (fun s => s.RIP = 0x102dfc) (imulR64R64Effect 0x102dfc 4 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102dfc 4 8 3).toInstrSpec (imul_r64_r64_effect_step 0x102dfc 0x4c (by decide) 0xc3 (by decide)) pre_rip
  have f153 : InstrSpec 0x102e00 [0x4D, 0x31, 0xC8] (fun s => s.RIP = 0x102e00) (xorR64R64Effect 0x102e00 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102e00 8 9).toInstrSpec (xor_r64_r64_effect_step 0x102e00 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x102e03 [0x49, 0x31, 0xF0] (fun s => s.RIP = 0x102e03) (xorR64R64Effect 0x102e03 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102e03 8 6).toInstrSpec (xor_r64_r64_effect_step 0x102e03 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x102e06 [0x48, 0xB9, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11] (fun s => s.RIP = 0x102e06) (movR64Imm64Effect 0x102e06 1 0x1111111111111111)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x102e06 1 0x1111111111111111).toInstrSpec (mov_r64_imm64_effect_step 0x102e06 0x48 0xb9 (by decide) (by decide) 0x1111111111111111) pre_rip
  have f156 : InstrSpec 0x102e10 [0x49, 0x21, 0xCB] (fun s => s.RIP = 0x102e10) (andR64R64Effect 0x102e10 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e10 11 1).toInstrSpec (and_r64_r64_effect_step 0x102e10 0x49 0xcb (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x102e13 [0x48, 0xB8, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22] (fun s => s.RIP = 0x102e13) (movR64Imm64Effect 0x102e13 0 0x2222222222222222)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x102e13 0 0x2222222222222222).toInstrSpec (mov_r64_imm64_effect_step 0x102e13 0x48 0xb8 (by decide) (by decide) 0x2222222222222222) pre_rip
  have f158 : InstrSpec 0x102e1d [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x102e1d) (andR64R64Effect 0x102e1d 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102e1d 7 0).toInstrSpec (and_r64_r64_effect_step 0x102e1d 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x102e20 [0x4C, 0x09, 0xDF] (fun s => s.RIP = 0x102e20) (orR64R64Effect 0x102e20 7 11)
      [.gpr 7, .gpr 11] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102e20 7 11).toInstrSpec (or_r64_r64_effect_step 0x102e20 0x4c 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f140 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 326), (6, 261), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd4) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f141 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 329) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 328), (6, 261), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd8) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f142 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 328), (6, 261), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ddc) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f143 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 332), (1, 312), (2, 281), (3, 251), (4, 65), (5, 328), (6, 261), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102de0) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f144 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 332), (1, 312), (2, 281), (3, 251), (4, 65), (5, 328), (6, 334), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102de4) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f145 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 332), (1, 312), (2, 336), (3, 251), (4, 65), (5, 328), (6, 334), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102de8) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f146 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 339) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 328), (6, 334), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102deb) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 340) (RestInside.out (n := 340) f147 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 341) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 328), (6, 334), (7, 324), (8, 285), (9, 340), (10, 243), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102def) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f148 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 343) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 328), (6, 334), (7, 324), (8, 285), (9, 340), (10, 342), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102df3) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f149 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 344), (6, 334), (7, 324), (8, 285), (9, 340), (10, 342), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102df6) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f150 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 346), (6, 334), (7, 324), (8, 285), (9, 340), (10, 342), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102df9) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f151 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 324), (8, 285), (9, 340), (10, 342), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dfc) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f152 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 351) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 324), (8, 350), (9, 340), (10, 342), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e00) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 352) (RestInside.out (n := 352) f153 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 353) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 324), (8, 352), (9, 340), (10, 342), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e03) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 354) (RestInside.out (n := 354) f154 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 355) (ρ' := [(0, 332), (1, 312), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 324), (8, 354), (9, 340), (10, 342), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e06) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 356) (RestInside.out (n := 356) f155 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 357) (ρ' := [(0, 332), (1, 356), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 324), (8, 354), (9, 340), (10, 342), (11, 302), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e10) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 358) (RestInside.out (n := 358) f156 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 359) (ρ' := [(0, 332), (1, 356), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 324), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e13) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 360) (RestInside.out (n := 360) f157 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 361) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 324), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e1d) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 362) (RestInside.out (n := 362) f158 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 363) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 362), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e20) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 364) (RestInside.out (n := 364) f159 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 365) (ρ' := [(0, 360), (1, 356), (2, 338), (3, 251), (4, 65), (5, 346), (6, 348), (7, 364), (8, 354), (9, 340), (10, 342), (11, 358), (12, 158), (13, 71), (14, 330), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102e23) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_8 code

theorem rest_l102bd0_6 [Bindings] (code : CodeMap) :
    Rest (n := 287) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 279), (1, 277), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]
      491 0x102d86 bytes_l102bd0_6 b_l102bd0_6 := by
  have f120 : InstrSpec 0x102d86 [0x48, 0xB9, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88] (fun s => s.RIP = 0x102d86) (movR64Imm64Effect 0x102d86 1 0x8888888888888888)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x102d86 1 0x8888888888888888).toInstrSpec (mov_r64_imm64_effect_step 0x102d86 0x48 0xb9 (by decide) (by decide) 0x8888888888888888) pre_rip
  have f121 : InstrSpec 0x102d90 [0x49, 0x21, 0xCE] (fun s => s.RIP = 0x102d90) (andR64R64Effect 0x102d90 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d90 14 1).toInstrSpec (and_r64_r64_effect_step 0x102d90 0x49 0xce (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x102d93 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102d93) (movR64R64Effect 0x102d93 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102d93 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102d93 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x102d96 [0x49, 0x0F, 0xAF, 0xC8] (fun s => s.RIP = 0x102d96) (imulR64R64Effect 0x102d96 4 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102d96 4 1 8).toInstrSpec (imul_r64_r64_effect_step 0x102d96 0x49 (by decide) 0xc8 (by decide)) pre_rip
  have f124 : InstrSpec 0x102d9a [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x102d9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x102d9a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102d9a 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d9a 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x102d9a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f125 : InstrSpec 0x102d9f [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x102d9f) (movR64R64Effect 0x102d9f 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x102d9f 11 2).toInstrSpec (mov_r64_r64_effect_step 0x102d9f 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x102da2 [0x4D, 0x0F, 0xAF, 0xDE] (fun s => s.RIP = 0x102da2) (imulR64R64Effect 0x102da2 4 11 14)
      [.gpr 11, .gpr 14] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102da2 4 11 14).toInstrSpec (imul_r64_r64_effect_step 0x102da2 0x4d (by decide) 0xde (by decide)) pre_rip
  have f127 : InstrSpec 0x102da6 [0x49, 0x31, 0xCB] (fun s => s.RIP = 0x102da6) (xorR64R64Effect 0x102da6 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102da6 11 1).toInstrSpec (xor_r64_r64_effect_step 0x102da6 0x49 0xcb (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x102da9 [0x49, 0x31, 0xEB] (fun s => s.RIP = 0x102da9) (xorR64R64Effect 0x102da9 11 5)
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102da9 11 5).toInstrSpec (xor_r64_r64_effect_step 0x102da9 0x49 0xeb (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x102dac [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x102dac) (movR64R64Effect 0x102dac 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102dac 5 0).toInstrSpec (mov_r64_r64_effect_step 0x102dac 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x102daf [0x49, 0x0F, 0xAF, 0xE9] (fun s => s.RIP = 0x102daf) (imulR64R64Effect 0x102daf 4 5 9)
      [.gpr 5, .gpr 9] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102daf 4 5 9).toInstrSpec (imul_r64_r64_effect_step 0x102daf 0x49 (by decide) 0xe9 (by decide)) pre_rip
  have f131 : InstrSpec 0x102db3 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x102db3) (movR64R64Effect 0x102db3 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102db3 1 2).toInstrSpec (mov_r64_r64_effect_step 0x102db3 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x102db6 [0x49, 0x0F, 0xAF, 0xC8] (fun s => s.RIP = 0x102db6) (imulR64R64Effect 0x102db6 4 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102db6 4 1 8).toInstrSpec (imul_r64_r64_effect_step 0x102db6 0x49 (by decide) 0xc8 (by decide)) pre_rip
  have f133 : InstrSpec 0x102dba [0x48, 0x31, 0xE9] (fun s => s.RIP = 0x102dba) (xorR64R64Effect 0x102dba 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102dba 1 5).toInstrSpec (xor_r64_r64_effect_step 0x102dba 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x102dbd [0x4C, 0x89, 0xD5] (fun s => s.RIP = 0x102dbd) (movR64R64Effect 0x102dbd 5 10)
      [.gpr 10] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102dbd 5 10).toInstrSpec (mov_r64_r64_effect_step 0x102dbd 0x4c 0xd5 (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x102dc0 [0x49, 0x0F, 0xAF, 0xEE] (fun s => s.RIP = 0x102dc0) (imulR64R64Effect 0x102dc0 4 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102dc0 4 5 14).toInstrSpec (imul_r64_r64_effect_step 0x102dc0 0x49 (by decide) 0xee (by decide)) pre_rip
  have f136 : InstrSpec 0x102dc4 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x102dc4) (movR64R64Effect 0x102dc4 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102dc4 7 3).toInstrSpec (mov_r64_r64_effect_step 0x102dc4 0x48 0xdf (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x102dc7 [0x48, 0x0F, 0xAF, 0xFE] (fun s => s.RIP = 0x102dc7) (imulR64R64Effect 0x102dc7 4 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102dc7 4 7 6).toInstrSpec (imul_r64_r64_effect_step 0x102dc7 0x48 (by decide) 0xfe (by decide)) pre_rip
  have f138 : InstrSpec 0x102dcb [0x48, 0x31, 0xEF] (fun s => s.RIP = 0x102dcb) (xorR64R64Effect 0x102dcb 7 5)
      [.gpr 7, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102dcb 7 5).toInstrSpec (xor_r64_r64_effect_step 0x102dcb 0x48 0xef (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x102dce [0x48, 0x31, 0xCF] (fun s => s.RIP = 0x102dce) (xorR64R64Effect 0x102dce 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102dce 7 1).toInstrSpec (xor_r64_r64_effect_step 0x102dce 0x48 0xcf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f120 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 279), (1, 287), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d90) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f121 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 279), (1, 287), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d93) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f122 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 279), (1, 291), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d96) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f123 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 279), (1, 293), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d9a) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.exec (n := 295) (ρ' := [(0, 279), (1, 293), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d9f) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 296) (RestInside.out (n := 296) f125 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 297) (ρ' := [(0, 279), (1, 293), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 296), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da2) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f126 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 279), (1, 293), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 298), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da6) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f127 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 279), (1, 293), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 300), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da9) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f128 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 279), (1, 293), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dac) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f129 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 279), (1, 293), (2, 281), (3, 251), (4, 65), (5, 304), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102daf) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f130 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 279), (1, 293), (2, 281), (3, 251), (4, 65), (5, 306), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102db3) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f131 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 279), (1, 308), (2, 281), (3, 251), (4, 65), (5, 306), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102db6) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f132 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 279), (1, 310), (2, 281), (3, 251), (4, 65), (5, 306), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dba) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f133 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 306), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dbd) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f134 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 314), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc0) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f135 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 316), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc4) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f136 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 316), (6, 261), (7, 318), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc7) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f137 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 316), (6, 261), (7, 320), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dcb) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f138 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 316), (6, 261), (7, 322), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dce) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f139 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 279), (1, 312), (2, 281), (3, 251), (4, 65), (5, 316), (6, 261), (7, 324), (8, 285), (9, 257), (10, 243), (11, 302), (12, 158), (13, 71), (14, 289), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd1) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_7 code

theorem rest_l102bd0_5 [Bindings] (code : CodeMap) :
    Rest (n := 247) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 245), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 239), (9, 93), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      511 0x102d33 bytes_l102bd0_5 b_l102bd0_5 := by
  have f100 : InstrSpec 0x102d33 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x102d33) (movR64R64Effect 0x102d33 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x102d33 2 3).toInstrSpec (mov_r64_r64_effect_step 0x102d33 0x48 0xda (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x102d36 [0x48, 0xB9, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88] (fun s => s.RIP = 0x102d36) (movR64Imm64Effect 0x102d36 1 0x8888888888888888)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x102d36 1 0x8888888888888888).toInstrSpec (mov_r64_imm64_effect_step 0x102d36 0x48 0xb9 (by decide) (by decide) 0x8888888888888888) pre_rip
  have f102 : InstrSpec 0x102d40 [0x48, 0x21, 0xCB] (fun s => s.RIP = 0x102d40) (andR64R64Effect 0x102d40 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d40 3 1).toInstrSpec (and_r64_r64_effect_step 0x102d40 0x48 0xcb (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x102d43 [0x49, 0xB8, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22] (fun s => s.RIP = 0x102d43) (movR64Imm64Effect 0x102d43 8 0x2222222222222222)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x102d43 8 0x2222222222222222).toInstrSpec (mov_r64_imm64_effect_step 0x102d43 0x49 0xb8 (by decide) (by decide) 0x2222222222222222) pre_rip
  have f104 : InstrSpec 0x102d4d [0x4D, 0x89, 0xF1] (fun s => s.RIP = 0x102d4d) (movR64R64Effect 0x102d4d 9 14)
      [.gpr 14] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x102d4d 9 14).toInstrSpec (mov_r64_r64_effect_step 0x102d4d 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x102d50 [0x4D, 0x21, 0xC1] (fun s => s.RIP = 0x102d50) (andR64R64Effect 0x102d50 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d50 9 8).toInstrSpec (and_r64_r64_effect_step 0x102d50 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x102d53 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x102d53) (movR64R64Effect 0x102d53 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102d53 6 14).toInstrSpec (mov_r64_r64_effect_step 0x102d53 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x102d56 [0x48, 0x21, 0xFE] (fun s => s.RIP = 0x102d56) (andR64R64Effect 0x102d56 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d56 6 7).toInstrSpec (and_r64_r64_effect_step 0x102d56 0x48 0xfe (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x102d59 [0x4D, 0x89, 0xD3] (fun s => s.RIP = 0x102d59) (movR64R64Effect 0x102d59 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x102d59 11 10).toInstrSpec (mov_r64_r64_effect_step 0x102d59 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x102d5c [0x4C, 0x0F, 0xAF, 0xDE] (fun s => s.RIP = 0x102d5c) (imulR64R64Effect 0x102d5c 4 11 6)
      [.gpr 11, .gpr 6] [] [.reg 11, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102d5c 4 11 6).toInstrSpec (imul_r64_r64_effect_step 0x102d5c 0x4c (by decide) 0xde (by decide)) pre_rip
  have f110 : InstrSpec 0x102d60 [0x48, 0x89, 0xDD] (fun s => s.RIP = 0x102d60) (movR64R64Effect 0x102d60 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102d60 5 3).toInstrSpec (mov_r64_r64_effect_step 0x102d60 0x48 0xdd (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x102d63 [0x49, 0x0F, 0xAF, 0xE9] (fun s => s.RIP = 0x102d63) (imulR64R64Effect 0x102d63 4 5 9)
      [.gpr 5, .gpr 9] [] [.reg 5, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102d63 4 5 9).toInstrSpec (imul_r64_r64_effect_step 0x102d63 0x49 (by decide) 0xe9 (by decide)) pre_rip
  have f112 : InstrSpec 0x102d67 [0x4C, 0x31, 0xDD] (fun s => s.RIP = 0x102d67) (xorR64R64Effect 0x102d67 5 11)
      [.gpr 5, .gpr 11] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102d67 5 11).toInstrSpec (xor_r64_r64_effect_step 0x102d67 0x4c 0xdd (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x102d6a [0x4D, 0x89, 0xEF] (fun s => s.RIP = 0x102d6a) (movR64R64Effect 0x102d6a 15 13)
      [.gpr 13] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x102d6a 15 13).toInstrSpec (mov_r64_r64_effect_step 0x102d6a 0x4d 0xef (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x102d6d [0x4D, 0x31, 0xF7] (fun s => s.RIP = 0x102d6d) (xorR64R64Effect 0x102d6d 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102d6d 15 14).toInstrSpec (xor_r64_r64_effect_step 0x102d6d 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x102d70 [0x48, 0xB9, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11] (fun s => s.RIP = 0x102d70) (movR64Imm64Effect 0x102d70 1 0x1111111111111111)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x102d70 1 0x1111111111111111).toInstrSpec (mov_r64_imm64_effect_step 0x102d70 0x48 0xb9 (by decide) (by decide) 0x1111111111111111) pre_rip
  have f116 : InstrSpec 0x102d7a [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x102d7a) (andR64R64Effect 0x102d7a 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d7a 0 1).toInstrSpec (and_r64_r64_effect_step 0x102d7a 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x102d7d [0x4C, 0x21, 0xC2] (fun s => s.RIP = 0x102d7d) (andR64R64Effect 0x102d7d 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d7d 2 8).toInstrSpec (and_r64_r64_effect_step 0x102d7d 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x102d80 [0x4D, 0x89, 0xF0] (fun s => s.RIP = 0x102d80) (movR64R64Effect 0x102d80 8 14)
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x102d80 8 14).toInstrSpec (mov_r64_r64_effect_step 0x102d80 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x102d83 [0x49, 0x21, 0xC8] (fun s => s.RIP = 0x102d83) (andR64R64Effect 0x102d83 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d83 8 1).toInstrSpec (and_r64_r64_effect_step 0x102d83 0x49 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f100 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 245), (1, 225), (2, 247), (3, 156), (4, 65), (5, 5), (6, 83), (7, 239), (9, 93), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d36) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f101 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 156), (4, 65), (5, 5), (6, 83), (7, 239), (9, 93), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d40) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f102 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 5), (6, 83), (7, 239), (9, 93), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d43) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f103 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 5), (6, 83), (7, 239), (8, 253), (9, 93), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d4d) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f104 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 5), (6, 83), (7, 239), (8, 253), (9, 255), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d50) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f105 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 5), (6, 83), (7, 239), (8, 253), (9, 257), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d53) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f106 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 5), (6, 259), (7, 239), (8, 253), (9, 257), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d56) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f107 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 5), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d59) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f108 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 5), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 263), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d5c) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f109 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 5), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d60) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f110 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 267), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d63) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.out (n := 269) f111 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 270) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 269), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d67) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f112 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 272) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d6a) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f113 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 273), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d6d) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f114 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 245), (1, 249), (2, 247), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d70) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f115 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 245), (1, 277), (2, 247), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d7a) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f116 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 279), (1, 277), (2, 247), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d7d) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.out (n := 281) f117 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 282) (ρ' := [(0, 279), (1, 277), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 253), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d80) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f118 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 279), (1, 277), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 283), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d83) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f119 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 279), (1, 277), (2, 281), (3, 251), (4, 65), (5, 271), (6, 261), (7, 239), (8, 285), (9, 257), (10, 243), (11, 265), (12, 158), (13, 71), (14, 73), (15, 275), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d86) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_6 code

theorem rest_l102bd0_4 [Bindings] (code : CodeMap) :
    Rest (n := 209) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 207), (1, 205), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      531 0x102ce8 bytes_l102bd0_4 b_l102bd0_4 := by
  have f80 : InstrSpec 0x102ce8 [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x102ce8) (shlR64Effect 0x102ce8 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x102ce8 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x102ce8 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x102cec [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x102cec) (orR64R64Effect 0x102cec 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102cec 0 1).toInstrSpec (or_r64_r64_effect_step 0x102cec 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x102cef [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102cef) (movR64R64Effect 0x102cef 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102cef 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102cef 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x102cf2 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x102cf2) (andR64R64Effect 0x102cf2 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102cf2 1 9).toInstrSpec (and_r64_r64_effect_step 0x102cf2 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x102cf5 [0x48, 0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x102cf5) (shrR64Effect 0x102cf5 4 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102cf5 4 0 2).toInstrSpec (shr_r64_imm8_effect_step 0x102cf5 0x48 0xe8 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x102cf9 [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x102cf9) (andR64R64Effect 0x102cf9 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102cf9 0 9).toInstrSpec (and_r64_r64_effect_step 0x102cf9 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x102cfc [0x48, 0x8D, 0x04, 0x88] (fun s => s.RIP = 0x102cfc) (leaR64Effect 0x102cfc 0 (.sib 0 (some 1) 2 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102cfc 0 (.sib 0 (some 1) 2 .none)).toInstrSpec (lea_r64_effect_step 0x102cfc 0x48 (by decide) 0 (.sib 0 (some 1) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x102d00 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102d00) (movR64R64Effect 0x102d00 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102d00 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102d00 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x102d03 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x102d03) (andR64R64Effect 0x102d03 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d03 1 2).toInstrSpec (and_r64_r64_effect_step 0x102d03 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x102d06 [0x48, 0xD1, 0xE8] (fun s => s.RIP = 0x102d06) (shrR64Effect 0x102d06 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102d06 3 0 1).toInstrSpec (shr_r64_one_effect_step 0x102d06 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x102d09 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x102d09) (andR64R64Effect 0x102d09 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d09 0 2).toInstrSpec (and_r64_r64_effect_step 0x102d09 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x102d0c [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x102d0c) (leaR64Effect 0x102d0c 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102d0c 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x102d0c 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x102d10 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x102d10 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102d10 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102d10 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d10 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102d10 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f93 : InstrSpec 0x102d15 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x102d15) (movR64R64Effect 0x102d15 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102d15 0 12).toInstrSpec (mov_r64_r64_effect_step 0x102d15 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x102d18 [0x48, 0x31, 0xD8] (fun s => s.RIP = 0x102d18) (xorR64R64Effect 0x102d18 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x102d18 0 3).toInstrSpec (xor_r64_r64_effect_step 0x102d18 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x102d1b [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x102d1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102d1b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102d1b 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102d1b 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102d1b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x102d20 [0x48, 0xBF, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] (fun s => s.RIP = 0x102d20) (movR64Imm64Effect 0x102d20 7 0x4444444444444444)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x102d20 7 0x4444444444444444).toInstrSpec (mov_r64_imm64_effect_step 0x102d20 0x48 0xbf (by decide) (by decide) 0x4444444444444444) pre_rip
  have f97 : InstrSpec 0x102d2a [0x49, 0x89, 0xDA] (fun s => s.RIP = 0x102d2a) (movR64R64Effect 0x102d2a 10 3)
      [.gpr 3] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x102d2a 10 3).toInstrSpec (mov_r64_r64_effect_step 0x102d2a 0x49 0xda (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x102d2d [0x49, 0x21, 0xFA] (fun s => s.RIP = 0x102d2d) (andR64R64Effect 0x102d2d 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102d2d 10 7).toInstrSpec (and_r64_r64_effect_step 0x102d2d 0x49 0xfa (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x102d30 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x102d30) (movR64R64Effect 0x102d30 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102d30 0 3).toInstrSpec (mov_r64_r64_effect_step 0x102d30 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f80 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 209), (1, 205), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cec) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f81 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 211), (1, 205), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cef) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 211), (1, 213), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cf2) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 211), (1, 215), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cf5) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f84 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 217), (1, 215), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cf9) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f85 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 219), (1, 215), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cfc) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f86 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 221), (1, 215), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d00) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f87 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 221), (1, 223), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d03) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f88 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 221), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d06) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f89 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 227), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d09) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 229), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d0c) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f91 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 231), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d10) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.exec (n := 233) (ρ' := [(0, 231), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d15) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f93 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 234), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d18) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f94 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 236), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d1b) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.exec (n := 238) (ρ' := [(0, 236), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d20) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f96 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 236), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 239), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d2a) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f97 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 236), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 239), (9, 93), (10, 241), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d2d) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f98 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 236), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 239), (9, 93), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d30) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 245), (1, 225), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 239), (9, 93), (10, 243), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d33) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_5 code

theorem rest_l102bd0_3 [Bindings] (code : CodeMap) :
    Rest (n := 170) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 162), (1, 168), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      551 0x102ca5 bytes_l102bd0_3 b_l102bd0_3 := by
  have f60 : InstrSpec 0x102ca5 [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x102ca5) (andR64R64Effect 0x102ca5 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102ca5 0 6).toInstrSpec (and_r64_r64_effect_step 0x102ca5 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x102ca8 [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x102ca8) (shlR64Effect 0x102ca8 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x102ca8 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x102ca8 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x102cac [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x102cac) (orR64R64Effect 0x102cac 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102cac 0 1).toInstrSpec (or_r64_r64_effect_step 0x102cac 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x102caf [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102caf) (movR64R64Effect 0x102caf 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102caf 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102caf 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x102cb2 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x102cb2) (andR64R64Effect 0x102cb2 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102cb2 1 9).toInstrSpec (and_r64_r64_effect_step 0x102cb2 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x102cb5 [0x48, 0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x102cb5) (shrR64Effect 0x102cb5 4 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102cb5 4 0 2).toInstrSpec (shr_r64_imm8_effect_step 0x102cb5 0x48 0xe8 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x102cb9 [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x102cb9) (andR64R64Effect 0x102cb9 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102cb9 0 9).toInstrSpec (and_r64_r64_effect_step 0x102cb9 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x102cbc [0x48, 0x8D, 0x04, 0x88] (fun s => s.RIP = 0x102cbc) (leaR64Effect 0x102cbc 0 (.sib 0 (some 1) 2 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102cbc 0 (.sib 0 (some 1) 2 .none)).toInstrSpec (lea_r64_effect_step 0x102cbc 0x48 (by decide) 0 (.sib 0 (some 1) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x102cc0 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102cc0) (movR64R64Effect 0x102cc0 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102cc0 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102cc0 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x102cc3 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x102cc3) (andR64R64Effect 0x102cc3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102cc3 1 2).toInstrSpec (and_r64_r64_effect_step 0x102cc3 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x102cc6 [0x48, 0xD1, 0xE8] (fun s => s.RIP = 0x102cc6) (shrR64Effect 0x102cc6 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102cc6 3 0 1).toInstrSpec (shr_r64_one_effect_step 0x102cc6 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x102cc9 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x102cc9) (andR64R64Effect 0x102cc9 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102cc9 0 2).toInstrSpec (and_r64_r64_effect_step 0x102cc9 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x102ccc [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x102ccc) (leaR64Effect 0x102ccc 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102ccc 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x102ccc 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x102cd0 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x102cd0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102cd0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102cd0 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102cd0 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x102cd0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f74 : InstrSpec 0x102cd5 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x102cd5) (movR64R64Effect 0x102cd5 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102cd5 0 12).toInstrSpec (mov_r64_r64_effect_step 0x102cd5 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x102cd8 [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x102cd8) (bswapR64Effect 0x102cd8 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x102cd8 3 0).toInstrSpec (bswap_r64_effect_step 0x102cd8 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f76 : InstrSpec 0x102cdb [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102cdb) (movR64R64Effect 0x102cdb 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102cdb 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102cdb 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x102cde [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x102cde) (shrR64Effect 0x102cde 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x102cde 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x102cde 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x102ce2 [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x102ce2) (andR64R64Effect 0x102ce2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102ce2 1 6).toInstrSpec (and_r64_r64_effect_step 0x102ce2 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x102ce5 [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x102ce5) (andR64R64Effect 0x102ce5 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102ce5 0 6).toInstrSpec (and_r64_r64_effect_step 0x102ce5 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 170), (1, 168), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ca8) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f61 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 172), (1, 168), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cac) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f62 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 174), (1, 168), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102caf) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 174), (1, 176), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cb2) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f64 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 174), (1, 178), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cb5) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f65 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 180), (1, 178), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cb9) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 182), (1, 178), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cbc) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 184), (1, 178), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cc0) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f68 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 184), (1, 186), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cc3) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 184), (1, 188), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cc6) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 190), (1, 188), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cc9) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f71 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 192), (1, 188), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ccc) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f72 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 194), (1, 188), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cd0) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.exec (n := 196) (ρ' := [(0, 194), (1, 188), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cd5) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 197), (1, 188), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cd8) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f75 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 199), (1, 188), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cdb) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 199), (1, 201), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102cde) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f77 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 199), (1, 203), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ce2) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f78 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 199), (1, 205), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ce5) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f79 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 207), (1, 205), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ce8) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_4 code

theorem rest_l102bd0_2 [Bindings] (code : CodeMap) :
    Rest (n := 132) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 130), (1, 126), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      571 0x102c60 bytes_l102bd0_2 b_l102bd0_2 := by
  have f40 : InstrSpec 0x102c60 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x102c60) (orR64R64Effect 0x102c60 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102c60 0 1).toInstrSpec (or_r64_r64_effect_step 0x102c60 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x102c63 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102c63) (movR64R64Effect 0x102c63 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102c63 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102c63 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x102c66 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x102c66) (andR64R64Effect 0x102c66 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c66 1 9).toInstrSpec (and_r64_r64_effect_step 0x102c66 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x102c69 [0x48, 0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x102c69) (shrR64Effect 0x102c69 4 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102c69 4 0 2).toInstrSpec (shr_r64_imm8_effect_step 0x102c69 0x48 0xe8 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x102c6d [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x102c6d) (andR64R64Effect 0x102c6d 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c6d 0 9).toInstrSpec (and_r64_r64_effect_step 0x102c6d 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x102c70 [0x48, 0x8D, 0x04, 0x88] (fun s => s.RIP = 0x102c70) (leaR64Effect 0x102c70 0 (.sib 0 (some 1) 2 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102c70 0 (.sib 0 (some 1) 2 .none)).toInstrSpec (lea_r64_effect_step 0x102c70 0x48 (by decide) 0 (.sib 0 (some 1) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x102c74 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102c74) (movR64R64Effect 0x102c74 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102c74 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102c74 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x102c77 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x102c77) (andR64R64Effect 0x102c77 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c77 1 2).toInstrSpec (and_r64_r64_effect_step 0x102c77 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x102c7a [0x48, 0xD1, 0xE8] (fun s => s.RIP = 0x102c7a) (shrR64Effect 0x102c7a 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102c7a 3 0 1).toInstrSpec (shr_r64_one_effect_step 0x102c7a 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x102c7d [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x102c7d) (andR64R64Effect 0x102c7d 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c7d 0 2).toInstrSpec (and_r64_r64_effect_step 0x102c7d 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x102c80 [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x102c80) (leaR64Effect 0x102c80 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102c80 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x102c80 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x102c84 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x102c84 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102c84 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102c84 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102c84 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x102c84 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x102c89 [0x48, 0x89, 0x7C, 0x24, 0x48] (StorePre 0x102c89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x102c89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102c89 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102c89 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x102c89 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x102c8e [0x48, 0x8B, 0x1F] (LoadPre 0x102c8e (fun s => AddrMode.addr (.base 7 .none) s (0x102c8e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102c8e 3 (.base 7 .none))
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x102c8e 3 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x102c8e 0x48 (by decide) 3 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x102c91 [0x4C, 0x8B, 0x67, 0x08] (LoadPre 0x102c91 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x102c91 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102c91 12 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x102c91 12 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102c91 0x4c (by decide) 4 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x102c95 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x102c95) (movR64R64Effect 0x102c95 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102c95 0 3).toInstrSpec (mov_r64_r64_effect_step 0x102c95 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x102c98 [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x102c98) (bswapR64Effect 0x102c98 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x102c98 3 0).toInstrSpec (bswap_r64_effect_step 0x102c98 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f57 : InstrSpec 0x102c9b [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102c9b) (movR64R64Effect 0x102c9b 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102c9b 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102c9b 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x102c9e [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x102c9e) (shrR64Effect 0x102c9e 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x102c9e 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x102c9e 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x102ca2 [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x102ca2) (andR64R64Effect 0x102ca2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102ca2 1 6).toInstrSpec (and_r64_r64_effect_step 0x102ca2 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 132), (1, 126), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c63) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 132), (1, 134), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c66) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 132), (1, 136), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c69) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 138), (1, 136), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c6d) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 140), (1, 136), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c70) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 142), (1, 136), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c74) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 142), (1, 144), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c77) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 142), (1, 146), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c7a) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f48 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 148), (1, 146), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c7d) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 150), (1, 146), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c80) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 152), (1, 146), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c84) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.exec (n := 154) (ρ' := [(0, 152), (1, 146), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c89) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 155) (RestInside.exec (n := 155) (ρ' := [(0, 152), (1, 146), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c8e) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f53 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 152), (1, 146), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c91) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f54 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 152), (1, 146), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c95) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f55 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 160), (1, 146), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c98) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f56 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 162), (1, 146), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c9b) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 162), (1, 164), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c9e) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 162), (1, 166), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ca2) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 162), (1, 168), (2, 105), (3, 156), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 158), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ca5) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_3 code

theorem rest_l102bd0_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x102bd0 bytes_l102bd0) [(0, 91), (1, 85), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      591 0x102c10 bytes_l102bd0_1 b_l102bd0_1 := by
  have f20 : InstrSpec 0x102c10 [0x49, 0xB9, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33] (fun s => s.RIP = 0x102c10) (movR64Imm64Effect 0x102c10 9 0x3333333333333333)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x102c10 9 0x3333333333333333).toInstrSpec (mov_r64_imm64_effect_step 0x102c10 0x49 0xb9 (by decide) (by decide) 0x3333333333333333) pre_rip
  have f21 : InstrSpec 0x102c1a [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102c1a) (movR64R64Effect 0x102c1a 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102c1a 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102c1a 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x102c1d [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x102c1d) (andR64R64Effect 0x102c1d 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c1d 1 9).toInstrSpec (and_r64_r64_effect_step 0x102c1d 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x102c20 [0x48, 0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x102c20) (shrR64Effect 0x102c20 4 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102c20 4 0 2).toInstrSpec (shr_r64_imm8_effect_step 0x102c20 0x48 0xe8 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x102c24 [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x102c24) (andR64R64Effect 0x102c24 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c24 0 9).toInstrSpec (and_r64_r64_effect_step 0x102c24 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x102c27 [0x48, 0x8D, 0x04, 0x88] (fun s => s.RIP = 0x102c27) (leaR64Effect 0x102c27 0 (.sib 0 (some 1) 2 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102c27 0 (.sib 0 (some 1) 2 .none)).toInstrSpec (lea_r64_effect_step 0x102c27 0x48 (by decide) 0 (.sib 0 (some 1) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x102c2b [0x48, 0xBA, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55] (fun s => s.RIP = 0x102c2b) (movR64Imm64Effect 0x102c2b 2 0x5555555555555555)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x102c2b 2 0x5555555555555555).toInstrSpec (mov_r64_imm64_effect_step 0x102c2b 0x48 0xba (by decide) (by decide) 0x5555555555555555) pre_rip
  have f27 : InstrSpec 0x102c35 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102c35) (movR64R64Effect 0x102c35 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102c35 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102c35 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x102c38 [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x102c38) (andR64R64Effect 0x102c38 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c38 1 2).toInstrSpec (and_r64_r64_effect_step 0x102c38 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x102c3b [0x48, 0xD1, 0xE8] (fun s => s.RIP = 0x102c3b) (shrR64Effect 0x102c3b 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102c3b 3 0 1).toInstrSpec (shr_r64_one_effect_step 0x102c3b 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x102c3e [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x102c3e) (andR64R64Effect 0x102c3e 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c3e 0 2).toInstrSpec (and_r64_r64_effect_step 0x102c3e 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x102c41 [0x48, 0x8D, 0x04, 0x48] (fun s => s.RIP = 0x102c41) (leaR64Effect 0x102c41 0 (.sib 0 (some 1) 1 .none))
      [.gpr 0, .gpr 1] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102c41 0 (.sib 0 (some 1) 1 .none)).toInstrSpec (lea_r64_effect_step 0x102c41 0x48 (by decide) 0 (.sib 0 (some 1) 1 .none) (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x102c45 [0x48, 0x89, 0x04, 0x24] (StorePre 0x102c45 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102c45 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102c45 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102c45 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102c45 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x102c49 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x102c49) (movR64R64Effect 0x102c49 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102c49 0 13).toInstrSpec (mov_r64_r64_effect_step 0x102c49 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x102c4c [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x102c4c) (bswapR64Effect 0x102c4c 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x102c4c 3 0).toInstrSpec (bswap_r64_effect_step 0x102c4c 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f35 : InstrSpec 0x102c4f [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102c4f) (movR64R64Effect 0x102c4f 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102c4f 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102c4f 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x102c52 [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x102c52) (shrR64Effect 0x102c52 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x102c52 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x102c52 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x102c56 [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x102c56) (andR64R64Effect 0x102c56 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c56 1 6).toInstrSpec (and_r64_r64_effect_step 0x102c56 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x102c59 [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x102c59) (andR64R64Effect 0x102c59 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c59 0 6).toInstrSpec (and_r64_r64_effect_step 0x102c59 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x102c5c [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x102c5c) (shlR64Effect 0x102c5c 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x102c5c 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x102c5c 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 91), (1, 85), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c1a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 91), (1, 95), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c1d) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 91), (1, 97), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c20) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 99), (1, 97), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c24) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 97), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c27) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 97), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c2b) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 103), (1, 97), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c35) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 103), (1, 107), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c38) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 103), (1, 109), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c3b) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 111), (1, 109), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c3e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 109), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c41) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 115), (1, 109), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c45) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.exec (n := 117) (ρ' := [(0, 115), (1, 109), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c49) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 118), (1, 109), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c4c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 120), (1, 109), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c4f) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 120), (1, 122), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c52) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 120), (1, 124), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c56) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 120), (1, 126), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c59) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 128), (1, 126), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c5c) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 130), (1, 126), (2, 105), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (9, 93), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c60) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_2 code

theorem rest_l102bd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102bd0 bytes_l102bd0) (entryMap (live .l102bd0))
      611 0x102bd0 bytes_l102bd0 b_l102bd0 := by
  have f0 : InstrSpec 0x102bd0 [0x55] (PushPre 0x102bd0 1) (pushR64Effect 0x102bd0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102bd0 1 5).toInstrSpec (push_r64_effect_step 0x102bd0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102bd1 [0x41, 0x57] (PushPre 0x102bd1 2) (pushR64Effect 0x102bd1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102bd1 2 15).toInstrSpec (push_r64_rex_effect_step 0x102bd1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102bd3 [0x41, 0x56] (PushPre 0x102bd3 2) (pushR64Effect 0x102bd3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102bd3 2 14).toInstrSpec (push_r64_rex_effect_step 0x102bd3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102bd5 [0x41, 0x55] (PushPre 0x102bd5 2) (pushR64Effect 0x102bd5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102bd5 2 13).toInstrSpec (push_r64_rex_effect_step 0x102bd5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102bd7 [0x41, 0x54] (PushPre 0x102bd7 2) (pushR64Effect 0x102bd7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102bd7 2 12).toInstrSpec (push_r64_rex_effect_step 0x102bd7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x102bd9 [0x53] (PushPre 0x102bd9 1) (pushR64Effect 0x102bd9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102bd9 1 3).toInstrSpec (push_r64_effect_step 0x102bd9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x102bda [0x48, 0x83, 0xEC, 0x50] (fun s => s.RIP = 0x102bda) (subR64Imm8Effect 0x102bda 4 0x50)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x102bda 4 0x50).toInstrSpec (sub_r64_imm8_effect_step 0x102bda 0x48 0xec 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102bde [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x102bde) (movR64R64Effect 0x102bde 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x102bde 13 2).toInstrSpec (mov_r64_r64_effect_step 0x102bde 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102be1 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x102be1) (movR64R64Effect 0x102be1 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102be1 14 6).toInstrSpec (mov_r64_r64_effect_step 0x102be1 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102be4 [0x4C, 0x33, 0x6F, 0x18] (LoadPre 0x102be4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x102be4 + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x102be4 13 (.base 7 (.d8 0x18)))
      [.gpr 13, .gpr 7] [] [.reg 13, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x102be4 13 (.base 7 (.d8 0x18))).toInstrSpec (xor_r64_m64_effect_step 0x102be4 0x4c (by decide) 5 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x102be8 [0x4C, 0x33, 0x77, 0x10] (LoadPre 0x102be8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x102be8 + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x102be8 14 (.base 7 (.d8 0x10)))
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x102be8 14 (.base 7 (.d8 0x10))).toInstrSpec (xor_r64_m64_effect_step 0x102be8 0x4c (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x102bec [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x102bec) (movR64R64Effect 0x102bec 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102bec 0 14).toInstrSpec (mov_r64_r64_effect_step 0x102bec 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x102bef [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x102bef) (bswapR64Effect 0x102bef 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x102bef 3 0).toInstrSpec (bswap_r64_effect_step 0x102bef 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f13 : InstrSpec 0x102bf2 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x102bf2) (movR64R64Effect 0x102bf2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102bf2 1 0).toInstrSpec (mov_r64_r64_effect_step 0x102bf2 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x102bf5 [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x102bf5) (shrR64Effect 0x102bf5 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x102bf5 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x102bf5 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x102bf9 [0x48, 0xBE, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F] (fun s => s.RIP = 0x102bf9) (movR64Imm64Effect 0x102bf9 6 0xf0f0f0f0f0f0f0f)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x102bf9 6 0xf0f0f0f0f0f0f0f).toInstrSpec (mov_r64_imm64_effect_step 0x102bf9 0x48 0xbe (by decide) (by decide) 0xf0f0f0f0f0f0f0f) pre_rip
  have f16 : InstrSpec 0x102c03 [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x102c03) (andR64R64Effect 0x102c03 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c03 1 6).toInstrSpec (and_r64_r64_effect_step 0x102c03 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x102c06 [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x102c06) (andR64R64Effect 0x102c06 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102c06 0 6).toInstrSpec (and_r64_r64_effect_step 0x102c06 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x102c09 [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x102c09) (shlR64Effect 0x102c09 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x102c09 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x102c09 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x102c0d [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x102c0d) (orR64R64Effect 0x102c0d 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x102c0d 0 1).toInstrSpec (or_r64_r64_effect_step 0x102c0d 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bd9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bda) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bde) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 67), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102be1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 67), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102be4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 71), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102be8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bec) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bef) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bf2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 79), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bf5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 81), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102bf9) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 77), (1, 81), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c03) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 77), (1, 85), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c06) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 85), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c09) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 85), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c0d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 91), (1, 85), (2, 2), (3, 3), (4, 65), (5, 5), (6, 83), (7, 7), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102c10) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102bd0_1 code

theorem block_l102bd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102bd0 :=
  Rest.liftedBlock (rest_l102bd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102bd0 x hx)

end AesGcm.Proofs.Machine.LIR
