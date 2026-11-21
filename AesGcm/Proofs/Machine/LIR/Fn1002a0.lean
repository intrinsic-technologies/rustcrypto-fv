import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l1002a0_9 [Bindings] (code : CodeMap) :
    Rest (n := 401) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(0, 399), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x100549 bytes_l1002a0_9 b_l1002a0_9 := by
  have f180 : InstrSpec 0x100549 [0x48, 0xC1, 0xC0, 0x18] (fun s => s.RIP = 0x100549) (rolR64Effect 0x100549 4 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x100549 4 0 24).toInstrSpec (rol_r64_imm8_effect_step 0x100549 0x48 0xc0 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x10054d [0x48, 0x89, 0x6F, 0x30] (StorePre 0x10054d 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10054d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10054d 5 (.base 7 (.d8 0x30)))
      [.gpr 5, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10054d 5 (.base 7 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10054d 0x48 (by decide) 5 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f182 : InstrSpec 0x100551 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x100551) (andR64R64Effect 0x100551 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100551 0 3).toInstrSpec (and_r64_r64_effect_step 0x100551 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x100554 [0x49, 0xC1, 0xC2, 0x28] (fun s => s.RIP = 0x100554) (rolR64Effect 0x100554 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x100554 4 10 40).toInstrSpec (rol_r64_imm8_effect_step 0x100554 0x49 0xc2 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f184 : InstrSpec 0x100558 [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x100558) (andR64R64Effect 0x100558 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100558 10 8).toInstrSpec (and_r64_r64_effect_step 0x100558 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f185 : InstrSpec 0x10055b [0x49, 0x09, 0xC2] (fun s => s.RIP = 0x10055b) (orR64R64Effect 0x10055b 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10055b 10 0).toInstrSpec (or_r64_r64_effect_step 0x10055b 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x10055e [0x49, 0x31, 0xCA] (fun s => s.RIP = 0x10055e) (xorR64R64Effect 0x10055e 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10055e 10 1).toInstrSpec (xor_r64_r64_effect_step 0x10055e 0x49 0xca (by decide) (by decide)) pre_rip
  have f187 : InstrSpec 0x100561 [0x4C, 0x89, 0x57, 0x38] (StorePre 0x100561 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x100561 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100561 10 (.base 7 (.d8 0x38)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x100561 10 (.base 7 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x100561 0x4c (by decide) 2 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f188 : InstrSpec 0x100565 [0x48, 0x83, 0xC4, 0x30] (fun s => s.RIP = 0x100565) (addR64Imm8Effect 0x100565 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100565 4 0x30).toInstrSpec (add_r64_imm8_effect_step 0x100565 0x48 0xc4 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f189 : InstrSpec 0x100569 [0x5B] (PopPre 0x100569) (popR64Effect 0x100569 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100569 1 3).toInstrSpec (pop_r64_effect_step 0x100569 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f190 : InstrSpec 0x10056a [0x41, 0x5C] (PopPre 0x10056a) (popR64Effect 0x10056a 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10056a 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10056a 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f191 : InstrSpec 0x10056c [0x41, 0x5D] (PopPre 0x10056c) (popR64Effect 0x10056c 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10056c 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10056c 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f192 : InstrSpec 0x10056e [0x41, 0x5E] (PopPre 0x10056e) (popR64Effect 0x10056e 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10056e 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10056e 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f193 : InstrSpec 0x100570 [0x41, 0x5F] (PopPre 0x100570) (popR64Effect 0x100570 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100570 2 15).toInstrSpec (pop_r64_rex_effect_step 0x100570 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f194 : InstrSpec 0x100572 [0x5D] (PopPre 0x100572) (popR64Effect 0x100572 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100572 1 5).toInstrSpec (pop_r64_effect_step 0x100572 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f195 : InstrSpec 0x100573 [0xC3] (RetPre 0x100573) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x100573).toInstrSpec (ret_effect_step 0x100573) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 401) (RestInside.out (n := 401) f180 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 402) (ρ' := [(0, 401), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10054d) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.exec (n := 403) (ρ' := [(0, 401), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100551) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f182 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100554) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f183 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 407) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 406), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100558) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 408) (RestInside.out (n := 408) f184 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 409) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 408), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10055b) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f185 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 411) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 410), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10055e) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f186 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 413) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100561) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.exec (n := 414) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100565) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 415) (RestInside.out (n := 415) f188 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 416) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 289), (4, 415), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100569) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 417) (RestInside.out (n := 417) f189 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 418) f189 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 419) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 417), (4, 418), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10056a) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 420) (RestInside.out (n := 420) f190 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 421) f190 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 422) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 417), (4, 421), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 420), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10056c) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 423) (RestInside.out (n := 423) f191 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 424) f191 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 425) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 417), (4, 424), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 420), (13, 423), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10056e) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 426) (RestInside.out (n := 426) f192 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 427) f192 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 428) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 417), (4, 427), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 420), (13, 423), (14, 426), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100570) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 429) (RestInside.out (n := 429) f193 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 430) f193 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 431) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 417), (4, 430), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 420), (13, 423), (14, 426), (15, 429), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100572) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 432) (RestInside.out (n := 432) f194 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 433) f194 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 434) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 417), (4, 433), (5, 432), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 420), (13, 423), (14, 426), (15, 429), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100573) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 435) (RestInside.out (n := 435) f195 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 436) f195 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 437) (ρ' := [(0, 404), (1, 389), (2, 370), (3, 417), (4, 436), (5, 432), (6, 343), (7, 359), (8, 322), (9, 301), (10, 412), (11, 349), (12, 420), (13, 423), (14, 426), (15, 429), (22, 22), (39, 39), (50, 50), (51, 51)]) f195 (by decide) rfl rfl rfl (by decide)

theorem rest_l1002a0_8 [Bindings] (code : CodeMap) :
    Rest (n := 362) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(0, 339), (1, 355), (2, 277), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]
      36 0x100506 bytes_l1002a0_8 b_l1002a0_8 := by
  have f160 : InstrSpec 0x100506 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x100506) (movR64R64Effect 0x100506 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100506 0 14).toInstrSpec (mov_r64_r64_effect_step 0x100506 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x100509 [0x48, 0xC1, 0xC0, 0x18] (fun s => s.RIP = 0x100509) (rolR64Effect 0x100509 4 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x100509 4 0 24).toInstrSpec (rol_r64_imm8_effect_step 0x100509 0x48 0xc0 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f162 : InstrSpec 0x10050d [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x10050d) (andR64R64Effect 0x10050d 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10050d 0 3).toInstrSpec (and_r64_r64_effect_step 0x10050d 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f163 : InstrSpec 0x100510 [0x4C, 0x31, 0xF1] (fun s => s.RIP = 0x100510) (xorR64R64Effect 0x100510 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100510 1 14).toInstrSpec (xor_r64_r64_effect_step 0x100510 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f164 : InstrSpec 0x100513 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x100513) (movR64R64Effect 0x100513 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100513 2 1).toInstrSpec (mov_r64_r64_effect_step 0x100513 0x48 0xca (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x100516 [0x49, 0xC1, 0xC6, 0x28] (fun s => s.RIP = 0x100516) (rolR64Effect 0x100516 4 14 40)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR64Effect_footprint 0x100516 4 14 40).toInstrSpec (rol_r64_imm8_effect_step 0x100516 0x49 0xc6 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f166 : InstrSpec 0x10051a [0x4D, 0x21, 0xC6] (fun s => s.RIP = 0x10051a) (andR64R64Effect 0x10051a 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10051a 14 8).toInstrSpec (and_r64_r64_effect_step 0x10051a 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x10051d [0x49, 0x09, 0xC6] (fun s => s.RIP = 0x10051d) (orR64R64Effect 0x10051d 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10051d 14 0).toInstrSpec (or_r64_r64_effect_step 0x10051d 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x100520 [0x49, 0x31, 0xF6] (fun s => s.RIP = 0x100520) (xorR64R64Effect 0x100520 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100520 14 6).toInstrSpec (xor_r64_r64_effect_step 0x100520 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f169 : InstrSpec 0x100523 [0x4C, 0x89, 0x77, 0x28] (StorePre 0x100523 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x100523 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100523 14 (.base 7 (.d8 0x28)))
      [.gpr 14, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x100523 14 (.base 7 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x100523 0x4c (by decide) 6 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f170 : InstrSpec 0x100527 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x100527) (movR64R64Effect 0x100527 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100527 0 5).toInstrSpec (mov_r64_r64_effect_step 0x100527 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x10052a [0x48, 0xC1, 0xC0, 0x18] (fun s => s.RIP = 0x10052a) (rolR64Effect 0x10052a 4 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x10052a 4 0 24).toInstrSpec (rol_r64_imm8_effect_step 0x10052a 0x48 0xc0 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f172 : InstrSpec 0x10052e [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x10052e) (andR64R64Effect 0x10052e 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10052e 0 3).toInstrSpec (and_r64_r64_effect_step 0x10052e 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f173 : InstrSpec 0x100531 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x100531 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100531 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100531 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100531 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100531 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f174 : InstrSpec 0x100536 [0x48, 0x31, 0xE9] (fun s => s.RIP = 0x100536) (xorR64R64Effect 0x100536 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100536 1 5).toInstrSpec (xor_r64_r64_effect_step 0x100536 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x100539 [0x48, 0xC1, 0xC5, 0x28] (fun s => s.RIP = 0x100539) (rolR64Effect 0x100539 4 5 40)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR64Effect_footprint 0x100539 4 5 40).toInstrSpec (rol_r64_imm8_effect_step 0x100539 0x48 0xc5 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f176 : InstrSpec 0x10053d [0x4C, 0x21, 0xC5] (fun s => s.RIP = 0x10053d) (andR64R64Effect 0x10053d 5 8)
      [.gpr 5, .gpr 8] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10053d 5 8).toInstrSpec (and_r64_r64_effect_step 0x10053d 0x4c 0xc5 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x100540 [0x48, 0x09, 0xC5] (fun s => s.RIP = 0x100540) (orR64R64Effect 0x100540 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100540 5 0).toInstrSpec (or_r64_r64_effect_step 0x100540 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f178 : InstrSpec 0x100543 [0x48, 0x31, 0xD5] (fun s => s.RIP = 0x100543) (xorR64R64Effect 0x100543 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100543 5 2).toInstrSpec (xor_r64_r64_effect_step 0x100543 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f179 : InstrSpec 0x100546 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x100546) (movR64R64Effect 0x100546 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100546 0 10).toInstrSpec (mov_r64_r64_effect_step 0x100546 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 362) (RestInside.out (n := 362) f160 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 363) (ρ' := [(0, 362), (1, 355), (2, 277), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100509) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 364) (RestInside.out (n := 364) f161 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 365) (ρ' := [(0, 364), (1, 355), (2, 277), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10050d) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 366) (RestInside.out (n := 366) f162 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 367) (ρ' := [(0, 366), (1, 355), (2, 277), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100510) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 368) (RestInside.out (n := 368) f163 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 369) (ρ' := [(0, 366), (1, 368), (2, 277), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100513) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 370) (RestInside.out (n := 370) f164 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 371) (ρ' := [(0, 366), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100516) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.out (n := 372) f165 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 373) (ρ' := [(0, 366), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 372), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10051a) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 374) (RestInside.out (n := 374) f166 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 375) (ρ' := [(0, 366), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 374), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10051d) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f167 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 366), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 376), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100520) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f168 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 366), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100523) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.exec (n := 380) (ρ' := [(0, 366), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100527) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 381) (RestInside.out (n := 381) f170 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 382) (ρ' := [(0, 381), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10052a) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 383) (RestInside.out (n := 383) f171 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 384) (ρ' := [(0, 383), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10052e) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 385) (RestInside.out (n := 385) f172 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 386) (ρ' := [(0, 385), (1, 368), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100531) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 387) (RestInside.out (n := 387) f173 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 388) (ρ' := [(0, 385), (1, 387), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100536) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f174 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 385), (1, 389), (2, 370), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100539) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f175 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 385), (1, 389), (2, 370), (3, 289), (4, 65), (5, 391), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10053d) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 393) (RestInside.out (n := 393) f176 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 394) (ρ' := [(0, 385), (1, 389), (2, 370), (3, 289), (4, 65), (5, 393), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100540) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 395) (RestInside.out (n := 395) f177 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 396) (ρ' := [(0, 385), (1, 389), (2, 370), (3, 289), (4, 65), (5, 395), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100543) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 397) (RestInside.out (n := 397) f178 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 398) (ρ' := [(0, 385), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100546) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 399) (RestInside.out (n := 399) f179 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 400) (ρ' := [(0, 399), (1, 389), (2, 370), (3, 289), (4, 65), (5, 397), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 378), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100549) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1002a0_9 code

theorem rest_l1002a0_7 [Bindings] (code : CodeMap) :
    Rest (n := 324) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(0, 318), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 320), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 293), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]
      56 0x1004c2 bytes_l1002a0_7 b_l1002a0_7 := by
  have f140 : InstrSpec 0x1004c2 [0x48, 0x09, 0xC7] (fun s => s.RIP = 0x1004c2) (orR64R64Effect 0x1004c2 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1004c2 7 0).toInstrSpec (or_r64_r64_effect_step 0x1004c2 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x1004c5 [0x4D, 0x31, 0xD5] (fun s => s.RIP = 0x1004c5) (xorR64R64Effect 0x1004c5 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004c5 13 10).toInstrSpec (xor_r64_r64_effect_step 0x1004c5 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x1004c8 [0x49, 0x31, 0xFD] (fun s => s.RIP = 0x1004c8) (xorR64R64Effect 0x1004c8 13 7)
      [.gpr 13, .gpr 7] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004c8 13 7).toInstrSpec (xor_r64_r64_effect_step 0x1004c8 0x49 0xfd (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x1004cb [0x48, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x1004cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1004cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004cb 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1004cb 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1004cb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f144 : InstrSpec 0x1004d0 [0x49, 0x31, 0xCE] (fun s => s.RIP = 0x1004d0) (xorR64R64Effect 0x1004d0 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004d0 14 1).toInstrSpec (xor_r64_r64_effect_step 0x1004d0 0x49 0xce (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x1004d3 [0x4C, 0x89, 0x6A, 0x18] (StorePre 0x1004d3 4 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1004d3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004d3 13 (.base 2 (.d8 0x18)))
      [.gpr 13, .gpr 2] [] [.rip] :=
    (movM64R64Effect_footprint 0x1004d3 13 (.base 2 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1004d3 0x4c (by decide) 5 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f146 : InstrSpec 0x1004d7 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x1004d7) (movR64R64Effect 0x1004d7 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1004d7 0 11).toInstrSpec (mov_r64_r64_effect_step 0x1004d7 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f147 : InstrSpec 0x1004da [0x48, 0xC1, 0xC0, 0x18] (fun s => s.RIP = 0x1004da) (rolR64Effect 0x1004da 4 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x1004da 4 0 24).toInstrSpec (rol_r64_imm8_effect_step 0x1004da 0x48 0xc0 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x1004de [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x1004de) (andR64R64Effect 0x1004de 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1004de 0 3).toInstrSpec (and_r64_r64_effect_step 0x1004de 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x1004e1 [0x4C, 0x31, 0xD9] (fun s => s.RIP = 0x1004e1) (xorR64R64Effect 0x1004e1 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004e1 1 11).toInstrSpec (xor_r64_r64_effect_step 0x1004e1 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x1004e4 [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x1004e4) (movR64R64Effect 0x1004e4 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1004e4 6 1).toInstrSpec (mov_r64_r64_effect_step 0x1004e4 0x48 0xce (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x1004e7 [0x49, 0xC1, 0xC3, 0x28] (fun s => s.RIP = 0x1004e7) (rolR64Effect 0x1004e7 4 11 40)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR64Effect_footprint 0x1004e7 4 11 40).toInstrSpec (rol_r64_imm8_effect_step 0x1004e7 0x49 0xc3 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x1004eb [0x4D, 0x21, 0xC3] (fun s => s.RIP = 0x1004eb) (andR64R64Effect 0x1004eb 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1004eb 11 8).toInstrSpec (and_r64_r64_effect_step 0x1004eb 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f153 : InstrSpec 0x1004ee [0x49, 0x09, 0xC3] (fun s => s.RIP = 0x1004ee) (orR64R64Effect 0x1004ee 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1004ee 11 0).toInstrSpec (or_r64_r64_effect_step 0x1004ee 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x1004f1 [0x4D, 0x31, 0xD7] (fun s => s.RIP = 0x1004f1) (xorR64R64Effect 0x1004f1 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004f1 15 10).toInstrSpec (xor_r64_r64_effect_step 0x1004f1 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x1004f4 [0x4D, 0x31, 0xDF] (fun s => s.RIP = 0x1004f4) (xorR64R64Effect 0x1004f4 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004f4 15 11).toInstrSpec (xor_r64_r64_effect_step 0x1004f4 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x1004f7 [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x1004f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1004f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004f7 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1004f7 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1004f7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f157 : InstrSpec 0x1004fc [0x48, 0x31, 0xCD] (fun s => s.RIP = 0x1004fc) (xorR64R64Effect 0x1004fc 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004fc 5 1).toInstrSpec (xor_r64_r64_effect_step 0x1004fc 0x48 0xcd (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x1004ff [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x1004ff) (movR64R64Effect 0x1004ff 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1004ff 7 2).toInstrSpec (mov_r64_r64_effect_step 0x1004ff 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x100502 [0x4C, 0x89, 0x7A, 0x20] (StorePre 0x100502 4 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x100502 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100502 15 (.base 2 (.d8 0x20)))
      [.gpr 15, .gpr 2] [] [.rip] :=
    (movM64R64Effect_footprint 0x100502 15 (.base 2 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x100502 0x4c (by decide) 7 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f140 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 318), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 293), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004c5) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f141 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 318), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 326), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004c8) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f142 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 329) (ρ' := [(0, 318), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004cb) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f143 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 318), (1, 330), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d0) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f144 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 318), (1, 330), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d3) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.exec (n := 334) (ρ' := [(0, 318), (1, 330), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004d7) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 335) (RestInside.out (n := 335) f146 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 336) (ρ' := [(0, 335), (1, 330), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004da) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f147 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 337), (1, 330), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004de) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f148 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 340) (ρ' := [(0, 339), (1, 330), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004e1) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f149 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 339), (1, 341), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004e4) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f150 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 339), (1, 341), (2, 277), (3, 289), (4, 65), (5, 172), (6, 343), (7, 324), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004e7) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f151 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 346) (ρ' := [(0, 339), (1, 341), (2, 277), (3, 289), (4, 65), (5, 172), (6, 343), (7, 324), (8, 322), (9, 301), (10, 239), (11, 345), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004eb) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f152 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 339), (1, 341), (2, 277), (3, 289), (4, 65), (5, 172), (6, 343), (7, 324), (8, 322), (9, 301), (10, 239), (11, 347), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004ee) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f153 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 339), (1, 341), (2, 277), (3, 289), (4, 65), (5, 172), (6, 343), (7, 324), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004f1) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f154 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 339), (1, 341), (2, 277), (3, 289), (4, 65), (5, 172), (6, 343), (7, 324), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 351), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004f4) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f155 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 339), (1, 341), (2, 277), (3, 289), (4, 65), (5, 172), (6, 343), (7, 324), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004f7) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f156 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 339), (1, 355), (2, 277), (3, 289), (4, 65), (5, 172), (6, 343), (7, 324), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004fc) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f157 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 339), (1, 355), (2, 277), (3, 289), (4, 65), (5, 357), (6, 343), (7, 324), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004ff) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f158 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 339), (1, 355), (2, 277), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100502) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.exec (n := 361) (ρ' := [(0, 339), (1, 355), (2, 277), (3, 289), (4, 65), (5, 357), (6, 343), (7, 359), (8, 322), (9, 301), (10, 239), (11, 349), (12, 264), (13, 328), (14, 332), (15, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100506) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1002a0_8 code

theorem rest_l1002a0_6 [Bindings] (code : CodeMap) :
    Rest (n := 285) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(0, 262), (1, 279), (2, 277), (3, 245), (4, 65), (5, 172), (6, 268), (7, 283), (8, 247), (9, 281), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]
      76 0x100473 bytes_l1002a0_6 b_l1002a0_6 := by
  have f120 : InstrSpec 0x100473 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x100473) (movR64R64Effect 0x100473 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100473 0 9).toInstrSpec (mov_r64_r64_effect_step 0x100473 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x100476 [0x48, 0xC1, 0xC0, 0x18] (fun s => s.RIP = 0x100476) (rolR64Effect 0x100476 4 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x100476 4 0 24).toInstrSpec (rol_r64_imm8_effect_step 0x100476 0x48 0xc0 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x10047a [0x48, 0xBB, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x10047a) (movR64Imm64Effect 0x10047a 3 0xff00ff00ff00ff)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x10047a 3 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x10047a 0x48 0xbb (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f123 : InstrSpec 0x100484 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x100484) (andR64R64Effect 0x100484 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100484 0 3).toInstrSpec (and_r64_r64_effect_step 0x100484 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x100487 [0x4D, 0x31, 0xCD] (fun s => s.RIP = 0x100487) (xorR64R64Effect 0x100487 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100487 13 9).toInstrSpec (xor_r64_r64_effect_step 0x100487 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x10048a [0x49, 0xC1, 0xC1, 0x28] (fun s => s.RIP = 0x10048a) (rolR64Effect 0x10048a 4 9 40)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR64Effect_footprint 0x10048a 4 9 40).toInstrSpec (rol_r64_imm8_effect_step 0x10048a 0x49 0xc1 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x10048e [0x48, 0xBE, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF] (fun s => s.RIP = 0x10048e) (movR64Imm64Effect 0x10048e 6 0xff00ff00ff00ff00)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10048e 6 0xff00ff00ff00ff00).toInstrSpec (mov_r64_imm64_effect_step 0x10048e 0x48 0xbe (by decide) (by decide) 0xff00ff00ff00ff00) pre_rip
  have f127 : InstrSpec 0x100498 [0x49, 0x21, 0xF1] (fun s => s.RIP = 0x100498) (andR64R64Effect 0x100498 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100498 9 6).toInstrSpec (and_r64_r64_effect_step 0x100498 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x10049b [0x49, 0x09, 0xC1] (fun s => s.RIP = 0x10049b) (orR64R64Effect 0x10049b 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10049b 9 0).toInstrSpec (or_r64_r64_effect_step 0x10049b 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x10049e [0x49, 0x31, 0xC8] (fun s => s.RIP = 0x10049e) (xorR64R64Effect 0x10049e 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10049e 8 1).toInstrSpec (xor_r64_r64_effect_step 0x10049e 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x1004a1 [0x4D, 0x31, 0xC8] (fun s => s.RIP = 0x1004a1) (xorR64R64Effect 0x1004a1 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004a1 8 9).toInstrSpec (xor_r64_r64_effect_step 0x1004a1 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x1004a4 [0x4C, 0x89, 0x42, 0x10] (StorePre 0x1004a4 4 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1004a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004a4 8 (.base 2 (.d8 0x10)))
      [.gpr 8, .gpr 2] [] [.rip] :=
    (movM64R64Effect_footprint 0x1004a4 8 (.base 2 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1004a4 0x4c (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f132 : InstrSpec 0x1004a8 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x1004a8) (movR64R64Effect 0x1004a8 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1004a8 0 7).toInstrSpec (mov_r64_r64_effect_step 0x1004a8 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x1004ab [0x48, 0xC1, 0xC0, 0x18] (fun s => s.RIP = 0x1004ab) (rolR64Effect 0x1004ab 4 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x1004ab 4 0 24).toInstrSpec (rol_r64_imm8_effect_step 0x1004ab 0x48 0xc0 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x1004af [0x4D, 0x31, 0xFB] (fun s => s.RIP = 0x1004af) (xorR64R64Effect 0x1004af 11 15)
      [.gpr 11, .gpr 15] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004af 11 15).toInstrSpec (xor_r64_r64_effect_step 0x1004af 0x4d 0xfb (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x1004b2 [0x49, 0x31, 0xFF] (fun s => s.RIP = 0x1004b2) (xorR64R64Effect 0x1004b2 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1004b2 15 7).toInstrSpec (xor_r64_r64_effect_step 0x1004b2 0x49 0xff (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x1004b5 [0x48, 0xC1, 0xC7, 0x28] (fun s => s.RIP = 0x1004b5) (rolR64Effect 0x1004b5 4 7 40)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR64Effect_footprint 0x1004b5 4 7 40).toInstrSpec (rol_r64_imm8_effect_step 0x1004b5 0x48 0xc7 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x1004b9 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x1004b9) (andR64R64Effect 0x1004b9 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1004b9 0 3).toInstrSpec (and_r64_r64_effect_step 0x1004b9 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x1004bc [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x1004bc) (andR64R64Effect 0x1004bc 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1004bc 7 6).toInstrSpec (and_r64_r64_effect_step 0x1004bc 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x1004bf [0x49, 0x89, 0xF0] (fun s => s.RIP = 0x1004bf) (movR64R64Effect 0x1004bf 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1004bf 8 6).toInstrSpec (mov_r64_r64_effect_step 0x1004bf 0x49 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f120 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 285), (1, 279), (2, 277), (3, 245), (4, 65), (5, 172), (6, 268), (7, 283), (8, 247), (9, 281), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100476) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f121 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 287), (1, 279), (2, 277), (3, 245), (4, 65), (5, 172), (6, 268), (7, 283), (8, 247), (9, 281), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10047a) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f122 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 287), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 268), (7, 283), (8, 247), (9, 281), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100484) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 268), (7, 283), (8, 247), (9, 281), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100487) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f124 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 268), (7, 283), (8, 247), (9, 281), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10048a) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f125 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 268), (7, 283), (8, 247), (9, 295), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10048e) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f126 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 247), (9, 295), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100498) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f127 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 300) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 247), (9, 299), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10049b) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 301) (RestInside.out (n := 301) f128 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 302) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 247), (9, 301), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10049e) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 303) (RestInside.out (n := 303) f129 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 304) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 303), (9, 301), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004a1) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 305) (RestInside.out (n := 305) f130 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 306) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 305), (9, 301), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004a4) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 307) (RestInside.exec (n := 307) (ρ' := [(0, 291), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 305), (9, 301), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004a8) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f132 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 308), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 305), (9, 301), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004ab) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f133 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 310), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 305), (9, 301), (10, 239), (11, 77), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004af) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f134 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 310), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 305), (9, 301), (10, 239), (11, 312), (12, 264), (13, 293), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004b2) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f135 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 310), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 283), (8, 305), (9, 301), (10, 239), (11, 312), (12, 264), (13, 293), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004b5) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f136 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 310), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 316), (8, 305), (9, 301), (10, 239), (11, 312), (12, 264), (13, 293), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004b9) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f137 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 318), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 316), (8, 305), (9, 301), (10, 239), (11, 312), (12, 264), (13, 293), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004bc) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f138 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 318), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 320), (8, 305), (9, 301), (10, 239), (11, 312), (12, 264), (13, 293), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004bf) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f139 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 318), (1, 279), (2, 277), (3, 289), (4, 65), (5, 172), (6, 297), (7, 320), (8, 322), (9, 301), (10, 239), (11, 312), (12, 264), (13, 293), (14, 79), (15, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1004c2) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1002a0_7 code

theorem rest_l1002a0_5 [Bindings] (code : CodeMap) :
    Rest (n := 247) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(0, 227), (1, 222), (2, 216), (3, 245), (4, 65), (5, 172), (6, 237), (7, 75), (8, 71), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]
      96 0x100422 bytes_l1002a0_5 b_l1002a0_5 := by
  have f100 : InstrSpec 0x100422 [0x49, 0x31, 0xD8] (fun s => s.RIP = 0x100422) (xorR64R64Effect 0x100422 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100422 8 3).toInstrSpec (xor_r64_r64_effect_step 0x100422 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x100425 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x100425) (movR64R64Effect 0x100425 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100425 0 8).toInstrSpec (mov_r64_r64_effect_step 0x100425 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x100428 [0x48, 0xC1, 0xC0, 0x18] (fun s => s.RIP = 0x100428) (rolR64Effect 0x100428 4 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x100428 4 0 24).toInstrSpec (rol_r64_imm8_effect_step 0x100428 0x48 0xc0 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x10042c [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x10042c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10042c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10042c 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10042c 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10042c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f104 : InstrSpec 0x100431 [0x4C, 0x89, 0x21] (StorePre 0x100431 3 (fun s => AddrMode.addr (.base 1 .none) s (0x100431 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x100431 12 (.base 1 .none))
      [.gpr 12, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x100431 12 (.base 1 .none)).toInstrSpec (mov_m64_r64_effect_step 0x100431 0x4c (by decide) 4 (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f105 : InstrSpec 0x100434 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x100434) (movR64R64Effect 0x100434 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100434 6 8).toInstrSpec (mov_r64_r64_effect_step 0x100434 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x100437 [0x48, 0xC1, 0xC6, 0x28] (fun s => s.RIP = 0x100437) (rolR64Effect 0x100437 4 6 40)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x100437 4 6 40).toInstrSpec (rol_r64_imm8_effect_step 0x100437 0x48 0xc6 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x10043b [0x49, 0xBC, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x10043b) (movR64Imm64Effect 0x10043b 12 0xff00ff00ff00ff)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x10043b 12 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x10043b 0x49 0xbc (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f108 : InstrSpec 0x100445 [0x4C, 0x21, 0xE0] (fun s => s.RIP = 0x100445) (andR64R64Effect 0x100445 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100445 0 12).toInstrSpec (and_r64_r64_effect_step 0x100445 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x100448 [0x49, 0xBC, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF] (fun s => s.RIP = 0x100448) (movR64Imm64Effect 0x100448 12 0xff00ff00ff00ff00)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x100448 12 0xff00ff00ff00ff00).toInstrSpec (mov_r64_imm64_effect_step 0x100448 0x49 0xbc (by decide) (by decide) 0xff00ff00ff00ff00) pre_rip
  have f110 : InstrSpec 0x100452 [0x4C, 0x21, 0xE6] (fun s => s.RIP = 0x100452) (andR64R64Effect 0x100452 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100452 6 12).toInstrSpec (and_r64_r64_effect_step 0x100452 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x100455 [0x48, 0x09, 0xC6] (fun s => s.RIP = 0x100455) (orR64R64Effect 0x100455 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100455 6 0).toInstrSpec (or_r64_r64_effect_step 0x100455 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x100458 [0x48, 0x31, 0xDA] (fun s => s.RIP = 0x100458) (xorR64R64Effect 0x100458 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100458 2 3).toInstrSpec (xor_r64_r64_effect_step 0x100458 0x48 0xda (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x10045b [0x4C, 0x31, 0xD2] (fun s => s.RIP = 0x10045b) (xorR64R64Effect 0x10045b 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10045b 2 10).toInstrSpec (xor_r64_r64_effect_step 0x10045b 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x10045e [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x10045e) (xorR64R64Effect 0x10045e 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10045e 2 6).toInstrSpec (xor_r64_r64_effect_step 0x10045e 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x100461 [0x48, 0x89, 0x51, 0x08] (StorePre 0x100461 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x100461 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100461 2 (.base 1 (.d8 0x8)))
      [.gpr 2, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x100461 2 (.base 1 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100461 0x48 (by decide) 2 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f116 : InstrSpec 0x100465 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x100465) (movR64R64Effect 0x100465 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100465 2 1).toInstrSpec (mov_r64_r64_effect_step 0x100465 0x48 0xca (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x100468 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x100468 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100468 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100468 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100468 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100468 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f118 : InstrSpec 0x10046d [0x49, 0x31, 0xC9] (fun s => s.RIP = 0x10046d) (xorR64R64Effect 0x10046d 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10046d 9 1).toInstrSpec (xor_r64_r64_effect_step 0x10046d 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x100470 [0x4C, 0x31, 0xEF] (fun s => s.RIP = 0x100470) (xorR64R64Effect 0x100470 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100470 7 13).toInstrSpec (xor_r64_r64_effect_step 0x100470 0x4c 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f100 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 245), (4, 65), (5, 172), (6, 237), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100425) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f101 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 249), (1, 222), (2, 216), (3, 245), (4, 65), (5, 172), (6, 237), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100428) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f102 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 251), (1, 222), (2, 216), (3, 245), (4, 65), (5, 172), (6, 237), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10042c) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f103 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 251), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 237), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100431) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.exec (n := 255) (ρ' := [(0, 251), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 237), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100434) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f105 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(0, 251), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 256), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100437) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.out (n := 258) f106 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 259) (ρ' := [(0, 251), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 258), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10043b) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.out (n := 260) f107 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 261) (ρ' := [(0, 251), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 258), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 260), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100445) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f108 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 262), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 258), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 260), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100448) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f109 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 262), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 258), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100452) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f110 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 262), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 266), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100455) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f111 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 262), (1, 253), (2, 216), (3, 245), (4, 65), (5, 172), (6, 268), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100458) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f112 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 262), (1, 253), (2, 270), (3, 245), (4, 65), (5, 172), (6, 268), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10045b) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f113 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 262), (1, 253), (2, 272), (3, 245), (4, 65), (5, 172), (6, 268), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10045e) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f114 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 262), (1, 253), (2, 274), (3, 245), (4, 65), (5, 172), (6, 268), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100461) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.exec (n := 276) (ρ' := [(0, 262), (1, 253), (2, 274), (3, 245), (4, 65), (5, 172), (6, 268), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100465) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f116 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 262), (1, 253), (2, 277), (3, 245), (4, 65), (5, 172), (6, 268), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100468) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f117 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 262), (1, 279), (2, 277), (3, 245), (4, 65), (5, 172), (6, 268), (7, 75), (8, 247), (9, 73), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10046d) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.out (n := 281) f118 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 282) (ρ' := [(0, 262), (1, 279), (2, 277), (3, 245), (4, 65), (5, 172), (6, 268), (7, 75), (8, 247), (9, 281), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100470) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f119 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 262), (1, 279), (2, 277), (3, 245), (4, 65), (5, 172), (6, 268), (7, 283), (8, 247), (9, 281), (10, 239), (11, 77), (12, 264), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100473) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1002a0_6 code

theorem rest_l1002a0_4 [Bindings] (code : CodeMap) :
    Rest (n := 208) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(0, 206), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]
      116 0x1003cb bytes_l1002a0_4 b_l1002a0_4 := by
  have f80 : InstrSpec 0x1003cb [0x48, 0xC1, 0xC0, 0x3C] (fun s => s.RIP = 0x1003cb) (rolR64Effect 0x1003cb 4 0 60)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x1003cb 4 0 60).toInstrSpec (rol_r64_imm8_effect_step 0x1003cb 0x48 0xc0 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x1003cf [0x48, 0xB9, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0] (fun s => s.RIP = 0x1003cf) (movR64Imm64Effect 0x1003cf 1 0xf000f000f000f000)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1003cf 1 0xf000f000f000f000).toInstrSpec (mov_r64_imm64_effect_step 0x1003cf 0x48 0xb9 (by decide) (by decide) 0xf000f000f000f000) pre_rip
  have f82 : InstrSpec 0x1003d9 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x1003d9) (andR64R64Effect 0x1003d9 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1003d9 0 1).toInstrSpec (and_r64_r64_effect_step 0x1003d9 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x1003dc [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1003dc) (movR64R64Effect 0x1003dc 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1003dc 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1003dc 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x1003df [0x4C, 0x31, 0xE2] (fun s => s.RIP = 0x1003df) (xorR64R64Effect 0x1003df 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1003df 2 12).toInstrSpec (xor_r64_r64_effect_step 0x1003df 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x1003e2 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x1003e2) (movR64R64Effect 0x1003e2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1003e2 0 2).toInstrSpec (mov_r64_r64_effect_step 0x1003e2 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x1003e5 [0x48, 0xC1, 0xC0, 0x18] (fun s => s.RIP = 0x1003e5) (rolR64Effect 0x1003e5 4 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x1003e5 4 0 24).toInstrSpec (rol_r64_imm8_effect_step 0x1003e5 0x48 0xc0 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x1003e9 [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x1003e9) (orR64R64Effect 0x1003e9 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1003e9 1 6).toInstrSpec (or_r64_r64_effect_step 0x1003e9 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x1003ec [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x1003ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1003ec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003ec 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1003ec 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1003ec 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f89 : InstrSpec 0x1003f1 [0x48, 0xBE, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x1003f1) (movR64Imm64Effect 0x1003f1 6 0xff00ff00ff00ff)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x1003f1 6 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x1003f1 0x48 0xbe (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f90 : InstrSpec 0x1003fb [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x1003fb) (andR64R64Effect 0x1003fb 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1003fb 0 6).toInstrSpec (and_r64_r64_effect_step 0x1003fb 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x1003fe [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1003fe) (movR64R64Effect 0x1003fe 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1003fe 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1003fe 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x100401 [0x48, 0xC1, 0xC6, 0x28] (fun s => s.RIP = 0x100401) (rolR64Effect 0x100401 4 6 40)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x100401 4 6 40).toInstrSpec (rol_r64_imm8_effect_step 0x100401 0x48 0xc6 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x100405 [0x48, 0xBB, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF] (fun s => s.RIP = 0x100405) (movR64Imm64Effect 0x100405 3 0xff00ff00ff00ff00)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x100405 3 0xff00ff00ff00ff00).toInstrSpec (mov_r64_imm64_effect_step 0x100405 0x48 0xbb (by decide) (by decide) 0xff00ff00ff00ff00) pre_rip
  have f94 : InstrSpec 0x10040f [0x48, 0x21, 0xDE] (fun s => s.RIP = 0x10040f) (andR64R64Effect 0x10040f 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10040f 6 3).toInstrSpec (and_r64_r64_effect_step 0x10040f 0x48 0xde (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x100412 [0x48, 0x09, 0xC6] (fun s => s.RIP = 0x100412) (orR64R64Effect 0x100412 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100412 6 0).toInstrSpec (or_r64_r64_effect_step 0x100412 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x100415 [0x49, 0x31, 0xCA] (fun s => s.RIP = 0x100415) (xorR64R64Effect 0x100415 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100415 10 1).toInstrSpec (xor_r64_r64_effect_step 0x100415 0x49 0xca (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x100418 [0x4D, 0x31, 0xD4] (fun s => s.RIP = 0x100418) (xorR64R64Effect 0x100418 12 10)
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100418 12 10).toInstrSpec (xor_r64_r64_effect_step 0x100418 0x4d 0xd4 (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x10041b [0x49, 0x31, 0xF4] (fun s => s.RIP = 0x10041b) (xorR64R64Effect 0x10041b 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10041b 12 6).toInstrSpec (xor_r64_r64_effect_step 0x10041b 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x10041e [0x48, 0x8B, 0x1C, 0x24] (LoadPre 0x10041e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10041e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10041e 3 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10041e 3 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10041e 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f80 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 208), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003cf) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f81 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 208), (1, 210), (2, 69), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003d9) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f82 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 212), (1, 210), (2, 69), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003dc) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 212), (1, 214), (2, 69), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003df) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f84 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 212), (1, 214), (2, 216), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003e2) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f85 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 218), (1, 214), (2, 216), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003e5) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f86 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 220), (1, 214), (2, 216), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003e9) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f87 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 220), (1, 222), (2, 216), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003ec) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.exec (n := 224) (ρ' := [(0, 220), (1, 222), (2, 216), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003f1) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f89 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 220), (1, 222), (2, 216), (3, 3), (4, 65), (5, 172), (6, 225), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003fb) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 3), (4, 65), (5, 172), (6, 225), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003fe) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f91 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 3), (4, 65), (5, 172), (6, 229), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100401) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f92 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 3), (4, 65), (5, 172), (6, 231), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100405) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f93 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 234) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 233), (4, 65), (5, 172), (6, 231), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10040f) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f94 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 233), (4, 65), (5, 172), (6, 235), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100412) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f95 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 233), (4, 65), (5, 172), (6, 237), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100415) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f96 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 233), (4, 65), (5, 172), (6, 237), (7, 75), (8, 71), (9, 73), (10, 239), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100418) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f97 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 233), (4, 65), (5, 172), (6, 237), (7, 75), (8, 71), (9, 73), (10, 239), (11, 77), (12, 241), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10041b) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f98 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 233), (4, 65), (5, 172), (6, 237), (7, 75), (8, 71), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10041e) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f99 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 227), (1, 222), (2, 216), (3, 245), (4, 65), (5, 172), (6, 237), (7, 75), (8, 71), (9, 73), (10, 239), (11, 77), (12, 243), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100422) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1002a0_5 code

theorem rest_l1002a0_3 [Bindings] (code : CodeMap) :
    Rest (n := 170) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(0, 168), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]
      136 0x100371 bytes_l1002a0_3 b_l1002a0_3 := by
  have f60 : InstrSpec 0x100371 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x100371) (andR64R64Effect 0x100371 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100371 0 5).toInstrSpec (and_r64_r64_effect_step 0x100371 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x100374 [0x48, 0x8B, 0x69, 0x30] (LoadPre 0x100374 (fun s => AddrMode.addr (.base 1 (.d8 0x30)) s (0x100374 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100374 5 (.base 1 (.d8 0x30)))
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x100374 5 (.base 1 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x100374 0x48 (by decide) 5 (.base 1 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x100378 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x100378) (movR64R64Effect 0x100378 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100378 6 5).toInstrSpec (mov_r64_r64_effect_step 0x100378 0x48 0xee (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x10037b [0x48, 0xC1, 0xC6, 0x2C] (fun s => s.RIP = 0x10037b) (rolR64Effect 0x10037b 4 6 44)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x10037b 4 6 44).toInstrSpec (rol_r64_imm8_effect_step 0x10037b 0x48 0xc6 0x2c (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x10037f [0x4C, 0x09, 0xD0] (fun s => s.RIP = 0x10037f) (orR64R64Effect 0x10037f 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10037f 0 10).toInstrSpec (or_r64_r64_effect_step 0x10037f 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x100382 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x100382 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100382 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100382 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100382 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x100382 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x100387 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x100387) (movR64R64Effect 0x100387 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100387 0 5).toInstrSpec (mov_r64_r64_effect_step 0x100387 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x10038a [0x48, 0xC1, 0xC0, 0x3C] (fun s => s.RIP = 0x10038a) (rolR64Effect 0x10038a 4 0 60)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x10038a 4 0 60).toInstrSpec (rol_r64_imm8_effect_step 0x10038a 0x48 0xc0 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x10038e [0x49, 0xBA, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F] (fun s => s.RIP = 0x10038e) (movR64Imm64Effect 0x10038e 10 0xfff0fff0fff0fff)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x10038e 10 0xfff0fff0fff0fff).toInstrSpec (mov_r64_imm64_effect_step 0x10038e 0x49 0xba (by decide) (by decide) 0xfff0fff0fff0fff) pre_rip
  have f69 : InstrSpec 0x100398 [0x4C, 0x21, 0xD6] (fun s => s.RIP = 0x100398) (andR64R64Effect 0x100398 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100398 6 10).toInstrSpec (and_r64_r64_effect_step 0x100398 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10039b [0x49, 0xBA, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0] (fun s => s.RIP = 0x10039b) (movR64Imm64Effect 0x10039b 10 0xf000f000f000f000)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x10039b 10 0xf000f000f000f000).toInstrSpec (mov_r64_imm64_effect_step 0x10039b 0x49 0xba (by decide) (by decide) 0xf000f000f000f000) pre_rip
  have f71 : InstrSpec 0x1003a5 [0x4C, 0x21, 0xD0] (fun s => s.RIP = 0x1003a5) (andR64R64Effect 0x1003a5 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1003a5 0 10).toInstrSpec (and_r64_r64_effect_step 0x1003a5 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x1003a8 [0x48, 0x09, 0xF0] (fun s => s.RIP = 0x1003a8) (orR64R64Effect 0x1003a8 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1003a8 0 6).toInstrSpec (or_r64_r64_effect_step 0x1003a8 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x1003ab [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1003ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1003ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003ab 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1003ab 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1003ab 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f74 : InstrSpec 0x1003b0 [0x4C, 0x8B, 0x51, 0x38] (LoadPre 0x1003b0 (fun s => AddrMode.addr (.base 1 (.d8 0x38)) s (0x1003b0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1003b0 10 (.base 1 (.d8 0x38)))
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1003b0 10 (.base 1 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1003b0 0x4c (by decide) 2 (.base 1 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f75 : InstrSpec 0x1003b4 [0x4C, 0x89, 0xD6] (fun s => s.RIP = 0x1003b4) (movR64R64Effect 0x1003b4 6 10)
      [.gpr 10] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1003b4 6 10).toInstrSpec (mov_r64_r64_effect_step 0x1003b4 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x1003b7 [0x48, 0xC1, 0xC6, 0x2C] (fun s => s.RIP = 0x1003b7) (rolR64Effect 0x1003b7 4 6 44)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x1003b7 4 6 44).toInstrSpec (rol_r64_imm8_effect_step 0x1003b7 0x48 0xc6 0x2c (by decide) (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x1003bb [0x48, 0xB8, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F] (fun s => s.RIP = 0x1003bb) (movR64Imm64Effect 0x1003bb 0 0xfff0fff0fff0fff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1003bb 0 0xfff0fff0fff0fff).toInstrSpec (mov_r64_imm64_effect_step 0x1003bb 0x48 0xb8 (by decide) (by decide) 0xfff0fff0fff0fff) pre_rip
  have f78 : InstrSpec 0x1003c5 [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x1003c5) (andR64R64Effect 0x1003c5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1003c5 6 0).toInstrSpec (and_r64_r64_effect_step 0x1003c5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x1003c8 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x1003c8) (movR64R64Effect 0x1003c8 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1003c8 0 10).toInstrSpec (mov_r64_r64_effect_step 0x1003c8 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 170), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100374) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f61 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 170), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 148), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100378) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f62 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 170), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 174), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10037b) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f63 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 170), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 176), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10037f) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f64 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 178), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 176), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100382) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.exec (n := 180) (ρ' := [(0, 178), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 176), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100387) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 181), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 176), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10038a) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 183), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 176), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10038e) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 183), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 176), (7, 75), (8, 71), (9, 73), (10, 185), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100398) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 183), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 187), (7, 75), (8, 71), (9, 73), (10, 185), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10039b) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 183), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 187), (7, 75), (8, 71), (9, 73), (10, 189), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003a5) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 191), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 187), (7, 75), (8, 71), (9, 73), (10, 189), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003a8) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 193), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 187), (7, 75), (8, 71), (9, 73), (10, 189), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003ab) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.exec (n := 195) (ρ' := [(0, 193), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 187), (7, 75), (8, 71), (9, 73), (10, 189), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003b0) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f74 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 193), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 187), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003b4) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f75 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 193), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 198), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003b7) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f76 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 193), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 200), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003bb) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f77 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 202), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 200), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003c5) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f78 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 202), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003c8) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f79 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 206), (1, 67), (2, 69), (3, 3), (4, 65), (5, 172), (6, 204), (7, 75), (8, 71), (9, 73), (10, 196), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1003cb) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1002a0_4 code

theorem rest_l1002a0_2 [Bindings] (code : CodeMap) :
    Rest (n := 131) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(0, 125), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 129), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]
      156 0x10032e bytes_l1002a0_2 b_l1002a0_2 := by
  have f40 : InstrSpec 0x10032e [0x48, 0x09, 0xF0] (fun s => s.RIP = 0x10032e) (orR64R64Effect 0x10032e 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10032e 0 6).toInstrSpec (or_r64_r64_effect_step 0x10032e 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x100331 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x100331 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100331 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100331 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100331 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x100331 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x100336 [0x49, 0x89, 0xFD] (fun s => s.RIP = 0x100336) (movR64R64Effect 0x100336 13 7)
      [.gpr 7] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x100336 13 7).toInstrSpec (mov_r64_r64_effect_step 0x100336 0x49 0xfd (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x100339 [0x49, 0xC1, 0xC5, 0x3C] (fun s => s.RIP = 0x100339) (rolR64Effect 0x100339 4 13 60)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR64Effect_footprint 0x100339 4 13 60).toInstrSpec (rol_r64_imm8_effect_step 0x100339 0x49 0xc5 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x10033d [0x4D, 0x21, 0xFA] (fun s => s.RIP = 0x10033d) (andR64R64Effect 0x10033d 10 15)
      [.gpr 10, .gpr 15] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10033d 10 15).toInstrSpec (and_r64_r64_effect_step 0x10033d 0x4d 0xfa (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x100340 [0x49, 0x21, 0xED] (fun s => s.RIP = 0x100340) (andR64R64Effect 0x100340 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100340 13 5).toInstrSpec (and_r64_r64_effect_step 0x100340 0x49 0xed (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x100343 [0x4D, 0x09, 0xD5] (fun s => s.RIP = 0x100343) (orR64R64Effect 0x100343 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x100343 13 10).toInstrSpec (or_r64_r64_effect_step 0x100343 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x100346 [0x4C, 0x89, 0xDE] (fun s => s.RIP = 0x100346) (movR64R64Effect 0x100346 6 11)
      [.gpr 11] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100346 6 11).toInstrSpec (mov_r64_r64_effect_step 0x100346 0x4c 0xde (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x100349 [0x48, 0xC1, 0xC6, 0x2C] (fun s => s.RIP = 0x100349) (rolR64Effect 0x100349 4 6 44)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x100349 4 6 44).toInstrSpec (rol_r64_imm8_effect_step 0x100349 0x48 0xc6 0x2c (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10034d [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x10034d) (andR64R64Effect 0x10034d 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10034d 6 15).toInstrSpec (and_r64_r64_effect_step 0x10034d 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x100350 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x100350) (movR64R64Effect 0x100350 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100350 0 15).toInstrSpec (mov_r64_r64_effect_step 0x100350 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x100353 [0x4D, 0x89, 0xDF] (fun s => s.RIP = 0x100353) (movR64R64Effect 0x100353 15 11)
      [.gpr 11] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x100353 15 11).toInstrSpec (mov_r64_r64_effect_step 0x100353 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x100356 [0x49, 0xC1, 0xC7, 0x3C] (fun s => s.RIP = 0x100356) (rolR64Effect 0x100356 4 15 60)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR64Effect_footprint 0x100356 4 15 60).toInstrSpec (rol_r64_imm8_effect_step 0x100356 0x49 0xc7 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10035a [0x49, 0x21, 0xEF] (fun s => s.RIP = 0x10035a) (andR64R64Effect 0x10035a 15 5)
      [.gpr 15, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10035a 15 5).toInstrSpec (and_r64_r64_effect_step 0x10035a 0x49 0xef (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x10035d [0x49, 0x09, 0xF7] (fun s => s.RIP = 0x10035d) (orR64R64Effect 0x10035d 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10035d 15 6).toInstrSpec (or_r64_r64_effect_step 0x10035d 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x100360 [0x4D, 0x89, 0xF2] (fun s => s.RIP = 0x100360) (movR64R64Effect 0x100360 10 14)
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x100360 10 14).toInstrSpec (mov_r64_r64_effect_step 0x100360 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x100363 [0x49, 0xC1, 0xC2, 0x2C] (fun s => s.RIP = 0x100363) (rolR64Effect 0x100363 4 10 44)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x100363 4 10 44).toInstrSpec (rol_r64_imm8_effect_step 0x100363 0x49 0xc2 0x2c (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x100367 [0x49, 0x21, 0xC2] (fun s => s.RIP = 0x100367) (andR64R64Effect 0x100367 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100367 10 0).toInstrSpec (and_r64_r64_effect_step 0x100367 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10036a [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x10036a) (movR64R64Effect 0x10036a 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10036a 0 14).toInstrSpec (mov_r64_r64_effect_step 0x10036a 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10036d [0x48, 0xC1, 0xC0, 0x3C] (fun s => s.RIP = 0x10036d) (rolR64Effect 0x10036d 4 0 60)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x10036d 4 0 60).toInstrSpec (rol_r64_imm8_effect_step 0x10036d 0x48 0xc0 0x3c (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 129), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100331) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 129), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100336) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 129), (11, 77), (12, 98), (13, 134), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100339) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 129), (11, 77), (12, 98), (13, 136), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10033d) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 136), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100340) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 140), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100343) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f46 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100346) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f47 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 144), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100349) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f48 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 146), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10034d) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f49 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 131), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100350) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 150), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100353) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f51 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 150), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100356) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 150), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10035a) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f53 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 150), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10035d) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f54 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 150), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 138), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100360) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f55 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 150), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 160), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100363) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f56 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 150), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 162), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100367) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f57 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 150), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10036a) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 166), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10036d) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f59 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 168), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 148), (7, 75), (8, 71), (9, 73), (10, 164), (11, 77), (12, 98), (13, 142), (14, 79), (15, 158), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100371) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1002a0_3 code

theorem rest_l1002a0_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x1002a0 bytes_l1002a0) [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 84), (7, 75), (8, 71), (9, 73), (11, 77), (12, 90), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]
      176 0x1002e5 bytes_l1002a0_1 b_l1002a0_1 := by
  have f20 : InstrSpec 0x1002e5 [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x1002e5) (andR64R64Effect 0x1002e5 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1002e5 6 15).toInstrSpec (and_r64_r64_effect_step 0x1002e5 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1002e8 [0x48, 0xBD, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0xF0] (fun s => s.RIP = 0x1002e8) (movR64Imm64Effect 0x1002e8 5 0xf000f000f000f000)
      [] [] [.reg 5, .rip] :=
    (movR64Imm64Effect_footprint 0x1002e8 5 0xf000f000f000f000).toInstrSpec (mov_r64_imm64_effect_step 0x1002e8 0x48 0xbd (by decide) (by decide) 0xf000f000f000f000) pre_rip
  have f22 : InstrSpec 0x1002f2 [0x49, 0x21, 0xEC] (fun s => s.RIP = 0x1002f2) (andR64R64Effect 0x1002f2 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1002f2 12 5).toInstrSpec (and_r64_r64_effect_step 0x1002f2 0x49 0xec (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1002f5 [0x49, 0x09, 0xF4] (fun s => s.RIP = 0x1002f5) (orR64R64Effect 0x1002f5 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1002f5 12 6).toInstrSpec (or_r64_r64_effect_step 0x1002f5 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1002f8 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x1002f8) (movR64R64Effect 0x1002f8 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1002f8 6 8).toInstrSpec (mov_r64_r64_effect_step 0x1002f8 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1002fb [0x48, 0xC1, 0xC6, 0x2C] (fun s => s.RIP = 0x1002fb) (rolR64Effect 0x1002fb 4 6 44)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x1002fb 4 6 44).toInstrSpec (rol_r64_imm8_effect_step 0x1002fb 0x48 0xc6 0x2c (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1002ff [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x1002ff) (andR64R64Effect 0x1002ff 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1002ff 6 15).toInstrSpec (and_r64_r64_effect_step 0x1002ff 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x100302 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x100302) (movR64R64Effect 0x100302 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100302 0 8).toInstrSpec (mov_r64_r64_effect_step 0x100302 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x100305 [0x48, 0xC1, 0xC0, 0x3C] (fun s => s.RIP = 0x100305) (rolR64Effect 0x100305 4 0 60)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x100305 4 0 60).toInstrSpec (rol_r64_imm8_effect_step 0x100305 0x48 0xc0 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x100309 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x100309) (andR64R64Effect 0x100309 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100309 0 5).toInstrSpec (and_r64_r64_effect_step 0x100309 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10030c [0x48, 0x09, 0xF0] (fun s => s.RIP = 0x10030c) (orR64R64Effect 0x10030c 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10030c 0 6).toInstrSpec (or_r64_r64_effect_step 0x10030c 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10030f [0x48, 0x89, 0x04, 0x24] (StorePre 0x10030f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10030f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10030f 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10030f 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10030f 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x100313 [0x4C, 0x89, 0xCE] (fun s => s.RIP = 0x100313) (movR64R64Effect 0x100313 6 9)
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100313 6 9).toInstrSpec (mov_r64_r64_effect_step 0x100313 0x4c 0xce (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x100316 [0x48, 0xC1, 0xC6, 0x2C] (fun s => s.RIP = 0x100316) (rolR64Effect 0x100316 4 6 44)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x100316 4 6 44).toInstrSpec (rol_r64_imm8_effect_step 0x100316 0x48 0xc6 0x2c (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10031a [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x10031a) (andR64R64Effect 0x10031a 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10031a 6 15).toInstrSpec (and_r64_r64_effect_step 0x10031a 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10031d [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x10031d) (movR64R64Effect 0x10031d 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10031d 0 9).toInstrSpec (mov_r64_r64_effect_step 0x10031d 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x100320 [0x48, 0xC1, 0xC0, 0x3C] (fun s => s.RIP = 0x100320) (rolR64Effect 0x100320 4 0 60)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR64Effect_footprint 0x100320 4 0 60).toInstrSpec (rol_r64_imm8_effect_step 0x100320 0x48 0xc0 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x100324 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x100324) (andR64R64Effect 0x100324 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100324 0 5).toInstrSpec (and_r64_r64_effect_step 0x100324 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x100327 [0x49, 0x89, 0xFA] (fun s => s.RIP = 0x100327) (movR64R64Effect 0x100327 10 7)
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x100327 10 7).toInstrSpec (mov_r64_r64_effect_step 0x100327 0x49 0xfa (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10032a [0x49, 0xC1, 0xC2, 0x2C] (fun s => s.RIP = 0x10032a) (rolR64Effect 0x10032a 4 10 44)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR64Effect_footprint 0x10032a 4 10 44).toInstrSpec (rol_r64_imm8_effect_step 0x10032a 0x49 0xc2 0x2c (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 92), (7, 75), (8, 71), (9, 73), (11, 77), (12, 90), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002e8) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 92), (7, 75), (8, 71), (9, 73), (11, 77), (12, 90), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f2) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 92), (7, 75), (8, 71), (9, 73), (11, 77), (12, 96), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f5) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 92), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002f8) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 100), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002fb) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 102), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002ff) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 104), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100302) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 106), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 104), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100305) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 108), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 104), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100309) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 110), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 104), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10030c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 112), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 104), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10030f) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 112), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 104), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100313) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 112), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 115), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100316) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 112), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 117), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10031a) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 112), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10031d) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 121), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100320) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 123), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100324) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 125), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100327) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 125), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 127), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10032a) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f39 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 125), (1, 67), (2, 69), (3, 3), (4, 65), (5, 94), (6, 119), (7, 75), (8, 71), (9, 73), (10, 129), (11, 77), (12, 98), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10032e) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1002a0_2 code

theorem rest_l1002a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1002a0 bytes_l1002a0) (entryMap (live .l1002a0))
      196 0x1002a0 bytes_l1002a0 b_l1002a0 := by
  have f0 : InstrSpec 0x1002a0 [0x55] (PushPre 0x1002a0 1) (pushR64Effect 0x1002a0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002a0 1 5).toInstrSpec (push_r64_effect_step 0x1002a0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1002a1 [0x41, 0x57] (PushPre 0x1002a1 2) (pushR64Effect 0x1002a1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002a1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1002a1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1002a3 [0x41, 0x56] (PushPre 0x1002a3 2) (pushR64Effect 0x1002a3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002a3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1002a3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1002a5 [0x41, 0x55] (PushPre 0x1002a5 2) (pushR64Effect 0x1002a5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002a5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1002a5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1002a7 [0x41, 0x54] (PushPre 0x1002a7 2) (pushR64Effect 0x1002a7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002a7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1002a7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1002a9 [0x53] (PushPre 0x1002a9 1) (pushR64Effect 0x1002a9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1002a9 1 3).toInstrSpec (push_r64_effect_step 0x1002a9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1002aa [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x1002aa) (subR64Imm8Effect 0x1002aa 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1002aa 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x1002aa 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1002ae [0x48, 0x89, 0xF9] (fun s => s.RIP = 0x1002ae) (movR64R64Effect 0x1002ae 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1002ae 1 7).toInstrSpec (mov_r64_r64_effect_step 0x1002ae 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1002b1 [0x48, 0x8B, 0x17] (LoadPre 0x1002b1 (fun s => AddrMode.addr (.base 7 .none) s (0x1002b1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1002b1 2 (.base 7 .none))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1002b1 2 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1002b1 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1002b4 [0x4C, 0x8B, 0x47, 0x08] (LoadPre 0x1002b4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1002b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002b4 8 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1002b4 8 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1002b4 0x4c (by decide) 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1002b8 [0x4C, 0x8B, 0x4F, 0x10] (LoadPre 0x1002b8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1002b8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002b8 9 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1002b8 9 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1002b8 0x4c (by decide) 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1002bc [0x48, 0x8B, 0x7F, 0x18] (LoadPre 0x1002bc (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1002bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002bc 7 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1002bc 7 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1002bc 0x48 (by decide) 7 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1002c0 [0x4C, 0x8B, 0x59, 0x20] (LoadPre 0x1002c0 (fun s => AddrMode.addr (.base 1 (.d8 0x20)) s (0x1002c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002c0 11 (.base 1 (.d8 0x20)))
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1002c0 11 (.base 1 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1002c0 0x4c (by decide) 3 (.base 1 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1002c4 [0x4C, 0x8B, 0x71, 0x28] (LoadPre 0x1002c4 (fun s => AddrMode.addr (.base 1 (.d8 0x28)) s (0x1002c4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1002c4 14 (.base 1 (.d8 0x28)))
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1002c4 14 (.base 1 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1002c4 0x4c (by decide) 6 (.base 1 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1002c8 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x1002c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1002c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002c8 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1002c8 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1002c8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1002cd [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1002cd) (movR64R64Effect 0x1002cd 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1002cd 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1002cd 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1002d0 [0x48, 0xC1, 0xC6, 0x2C] (fun s => s.RIP = 0x1002d0) (rolR64Effect 0x1002d0 4 6 44)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR64Effect_footprint 0x1002d0 4 6 44).toInstrSpec (rol_r64_imm8_effect_step 0x1002d0 0x48 0xc6 0x2c (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1002d4 [0x49, 0xBF, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F, 0xFF, 0x0F] (fun s => s.RIP = 0x1002d4) (movR64Imm64Effect 0x1002d4 15 0xfff0fff0fff0fff)
      [] [] [.reg 15, .rip] :=
    (movR64Imm64Effect_footprint 0x1002d4 15 0xfff0fff0fff0fff).toInstrSpec (mov_r64_imm64_effect_step 0x1002d4 0x49 0xbf (by decide) (by decide) 0xfff0fff0fff0fff) pre_rip
  have f18 : InstrSpec 0x1002de [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x1002de) (movR64R64Effect 0x1002de 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1002de 12 2).toInstrSpec (mov_r64_r64_effect_step 0x1002de 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1002e1 [0x49, 0xC1, 0xC4, 0x3C] (fun s => s.RIP = 0x1002e1) (rolR64Effect 0x1002e1 4 12 60)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (rolR64Effect_footprint 0x1002e1 4 12 60).toInstrSpec (rol_r64_imm8_effect_step 0x1002e1 0x49 0xc4 0x3c (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002a5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002a7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002a9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002aa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002ae) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (3, 3), (4, 65), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002b1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002b4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 7), (8, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002b8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 7), (8, 71), (9, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002bc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 75), (8, 71), (9, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002c0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 75), (8, 71), (9, 73), (11, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002c4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 75), (8, 71), (9, 73), (11, 77), (12, 12), (13, 13), (14, 79), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002c8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (7, 75), (8, 71), (9, 73), (11, 77), (12, 12), (13, 13), (14, 79), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002cd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 82), (7, 75), (8, 71), (9, 73), (11, 77), (12, 12), (13, 13), (14, 79), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002d0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 84), (7, 75), (8, 71), (9, 73), (11, 77), (12, 12), (13, 13), (14, 79), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002d4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 84), (7, 75), (8, 71), (9, 73), (11, 77), (12, 12), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002de) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 84), (7, 75), (8, 71), (9, 73), (11, 77), (12, 88), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002e1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 84), (7, 75), (8, 71), (9, 73), (11, 77), (12, 90), (13, 13), (14, 79), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1002e5) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1002a0_1 code

theorem block_l1002a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1002a0 :=
  Rest.liftedBlock (rest_l1002a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1002a0 x hx)

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

theorem_by block_l1002a0_eval :
    program.runBlock (dialect code) ⟨.l1002a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
