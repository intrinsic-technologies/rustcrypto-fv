import K256.Proofs.Verify.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l109490_2 [Bindings] (code : CodeMap) :
    Rest (n := 112) code lifted (codeRange 0x109490 bytes_l109490) [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x10955c bytes_l109490_2 b_l109490_2 := by
  have f40 : InstrSpec 0x10955c [0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10955c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10955c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10955c (.sib 4 none 0 (.d8 0x60)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10955c (.sib 4 none 0 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10955c 0x48 (by decide) (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x109565 [0x49, 0x8B, 0x40, 0x18] (LoadPre 0x109565 (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x109565 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109565 0 (.base 8 (.d8 0x18)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109565 0 (.base 8 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109565 0x49 (by decide) 0 (.base 8 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x109569 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x109569 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x109569 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109569 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109569 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x109569 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x109571 [0x49, 0x8B, 0x40, 0x10] (LoadPre 0x109571 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x109571 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109571 0 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109571 0 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109571 0x49 (by decide) 0 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x109575 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x109575 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x109575 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109575 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109575 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x109575 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x10957d [0x49, 0x8B, 0x00] (LoadPre 0x10957d (fun s => AddrMode.addr (.base 8 .none) s (0x10957d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10957d 0 (.base 8 .none))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10957d 0 (.base 8 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10957d 0x49 (by decide) 0 (.base 8 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x109580 [0x49, 0x8B, 0x48, 0x08] (LoadPre 0x109580 (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x109580 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109580 1 (.base 8 (.d8 0x8)))
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109580 1 (.base 8 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109580 0x49 (by decide) 1 (.base 8 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x109584 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x109584 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x109584 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109584 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109584 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x109584 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x10958c [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10958c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10958c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10958c 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10958c 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x10958c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x109594 [0xC6, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109594 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x109594 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x109594 (.sib 4 none 0 (.d32 0xa8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x109594 (.sib 4 none 0 (.d32 0xa8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x109594 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x10959c [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10959c) (movR32Imm32Effect 0x10959c 6 12 0x1)
      [] [] [.reg 12, .rip] :=
    (movR32Imm32Effect_footprint 0x10959c 6 12 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10959c 0x41 0xbc (by decide) (by decide) 0x1) pre_rip
  have f51 : InstrSpec 0x1095a2 [0xBE, 0x4F, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x1095a2) (movR32Imm32Effect 0x1095a2 5 6 0x24f)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1095a2 5 6 0x24f).toInstrSpec (mov_r32_imm32_effect_step 0x1095a2 0xbe (by decide) 0x24f) pre_rip
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109565) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f41 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109569) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 113), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109571) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 116), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109575) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.exec (n := 118) (ρ' := [(0, 116), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10957d) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109580) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109584) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10958c) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.exec (n := 124) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109594) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10959c) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f50 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 126), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095a2) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f51 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 128), (7, 7), (8, 8), (12, 126), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095a7) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 130) (jmp_rel32_effect_step 0x1095a7 0x252 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l109490_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x109490 bytes_l109490) [(0, 84), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x1094ed bytes_l109490_1 b_l109490_1 := by
  have f20 : InstrSpec 0x1094ed [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x1094ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1094ed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094ed 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094ed 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1094ed 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1094f2 [0x48, 0x8B, 0x02] (LoadPre 0x1094f2 (fun s => AddrMode.addr (.base 2 .none) s (0x1094f2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1094f2 0 (.base 2 .none))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1094f2 0 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1094f2 0x48 (by decide) 0 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1094f5 [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x1094f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1094f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094f5 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094f5 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1094f5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x1094fa [0x48, 0x8B, 0x4A, 0x08] (LoadPre 0x1094fa (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1094fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094fa 1 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1094fa 1 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1094fa 0x48 (by decide) 1 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x1094fe [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x1094fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1094fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094fe 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094fe 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1094fe 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x109503 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x109503 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109503 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109503 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109503 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109503 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x109508 [0xC6, 0x44, 0x24, 0x28, 0x00] (StorePre 0x109508 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109508 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x109508 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x109508 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x109508 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x10950d [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x10950d (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10950d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10950d 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10950d 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10950d 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x109511 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x109511 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109511 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109511 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109511 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x109511 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x109516 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x109516 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109516 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109516 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109516 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109516 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x10951a [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x10951a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10951a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10951a 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10951a 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10951a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x10951f [0x48, 0x8B, 0x06] (LoadPre 0x10951f (fun s => AddrMode.addr (.base 6 .none) s (0x10951f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10951f 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10951f 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10951f 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x109522 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x109522 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109522 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109522 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109522 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109522 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x109526 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x109526 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109526 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109526 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109526 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x109526 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x10952b [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x10952b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10952b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10952b 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10952b 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10952b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x109530 [0xC6, 0x44, 0x24, 0x50, 0x00] (StorePre 0x109530 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109530 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x109530 (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x109530 (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x109530 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x109535 [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109535 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109535 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x109535 (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109535 (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109535 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x109541 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109541 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109541 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109541 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109541 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109541 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x10954a [0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10954a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10954a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10954a (.sib 4 none 0 (.d8 0x70)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10954a (.sib 4 none 0 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10954a 0x48 (by decide) (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x109553 [0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109553 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109553 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109553 (.sib 4 none 0 (.d8 0x68)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109553 (.sib 4 none 0 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109553 0x48 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094f2) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094f5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094fa) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 87), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094fe) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109503) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 87), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109508) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 87), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10950d) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109511) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 95), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109516) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 98), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10951a) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 98), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10951f) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109522) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109526) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10952b) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109530) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109535) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109541) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10954a) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109553) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10955c) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109490_2 code

theorem rest_l109490 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109490 bytes_l109490) (entryMap (live .l109490))
      53 0x109490 bytes_l109490 b_l109490 := by
  have f0 : InstrSpec 0x109490 [0x55] (PushPre 0x109490 1) (pushR64Effect 0x109490 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109490 1 5).toInstrSpec (push_r64_effect_step 0x109490 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109491 [0x41, 0x57] (PushPre 0x109491 2) (pushR64Effect 0x109491 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109491 2 15).toInstrSpec (push_r64_rex_effect_step 0x109491 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109493 [0x41, 0x56] (PushPre 0x109493 2) (pushR64Effect 0x109493 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109493 2 14).toInstrSpec (push_r64_rex_effect_step 0x109493 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109495 [0x41, 0x55] (PushPre 0x109495 2) (pushR64Effect 0x109495 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109495 2 13).toInstrSpec (push_r64_rex_effect_step 0x109495 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109497 [0x41, 0x54] (PushPre 0x109497 2) (pushR64Effect 0x109497 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109497 2 12).toInstrSpec (push_r64_rex_effect_step 0x109497 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109499 [0x53] (PushPre 0x109499 1) (pushR64Effect 0x109499 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109499 1 3).toInstrSpec (push_r64_effect_step 0x109499 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10949a [0x48, 0x81, 0xEC, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10949a) (subR64Imm32Effect 0x10949a 4 0x158)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10949a 4 0x158).toInstrSpec (sub_r64_imm32_effect_step 0x10949a 0x48 0xec 0x158 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1094a1 [0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x1094a1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1094a1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094a1 1 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094a1 1 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x1094a1 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1094a9 [0x48, 0x89, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x1094a9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1094a9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094a9 7 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094a9 7 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x1094a9 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1094b1 [0x48, 0x8B, 0x06] (LoadPre 0x1094b1 (fun s => AddrMode.addr (.base 6 .none) s (0x1094b1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1094b1 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1094b1 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1094b1 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1094b4 [0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x1094b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1094b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094b4 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094b4 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x1094b4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1094bc [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x1094bc (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1094bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094bc 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1094bc 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1094bc 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1094c0 [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x1094c0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1094c0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094c0 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094c0 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x1094c0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1094c8 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x1094c8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1094c8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094c8 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1094c8 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1094c8 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1094cc [0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x1094cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1094cc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094cc 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094cc 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x1094cc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1094d4 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x1094d4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1094d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094d4 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1094d4 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1094d4 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1094d8 [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x1094d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1094d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094d8 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094d8 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x1094d8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1094e0 [0x48, 0x8B, 0x42, 0x18] (LoadPre 0x1094e0 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1094e0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094e0 0 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1094e0 0 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1094e0 0x48 (by decide) 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1094e4 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1094e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1094e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094e4 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1094e4 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1094e4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1094e9 [0x48, 0x8B, 0x42, 0x10] (LoadPre 0x1094e9 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1094e9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094e9 0 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1094e9 0 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1094e9 0x48 (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109491) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109493) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109495) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109497) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109499) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10949a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094a1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094a9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094b1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094b4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094bc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094c0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094c8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094cc) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094d4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094d8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094e0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094e4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094e9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1094ed) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109490_1 code

theorem block_l109490 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109490 :=
  Rest.liftedBlock (rest_l109490 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109490 x hx)

theorem rest_l1095b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1095b0 bytes_l1095b0) (entryMap (live .l1095b0))
      4 0x1095b0 bytes_l1095b0 b_l1095b0 := by
  have f0 : InstrSpec 0x1095b0 [0x41, 0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1095b0) (movR32Imm32Effect 0x1095b0 6 14 0x1)
      [] [] [.reg 14, .rip] :=
    (movR32Imm32Effect_footprint 0x1095b0 6 14 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1095b0 0x41 0xbe (by decide) (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x1095b6 [0x45, 0x31, 0xED] (fun s => s.RIP = 0x1095b6) (xorR32R32Effect 0x1095b6 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1095b6 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1095b6 0x45 0xed (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1095b9 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x1095b9) (xorR32R32Effect 0x1095b9 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1095b9 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x1095b9 0x45 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1095bc [0xBB, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1095bc) (movR32Imm32Effect 0x1095bc 5 3 0x1)
      [] [] [.reg 3, .rip] :=
    (movR32Imm32Effect_footprint 0x1095bc 5 3 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1095bc 0xbb (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (9, 9), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095b6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (9, 9), (12, 12), (13, 55), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095b9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 4), (9, 9), (12, 12), (13, 55), (14, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095bc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 59), (4, 4), (9, 9), (12, 12), (13, 55), (14, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095c1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l1095b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1095b0 :=
  Rest.liftedBlock (rest_l1095b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1095b0 x hx)

theorem rest_l1095c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1095c1 bytes_l1095c1) (entryMap (live .l1095c1))
      16 0x1095c1 bytes_l1095c1 b_l1095c1 := by
  have f0 : InstrSpec 0x1095c1 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1095c1) (movR64R64Effect 0x1095c1 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1095c1 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1095c1 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1095c4 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x1095c4) (shrR64Effect 0x1095c4 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1095c4 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x1095c4 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1095c8 [0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x1095c8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1095c8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1095c8 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1095c8 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x1095c8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1095d0 [0x88, 0x44, 0x24, 0x07] (StorePre 0x1095d0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1095d0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1095d0 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1095d0 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1095d0 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1095d4 [0x48, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x1095d4) (leaR64Effect 0x1095d4 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1095d4 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x1095d4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1095d9 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x1095d9) (movR64R64Effect 0x1095d9 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1095d9 0 15).toInstrSpec (mov_r64_r64_effect_step 0x1095d9 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1095dc [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x1095dc) (shrR64Effect 0x1095dc 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1095dc 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x1095dc 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1095e0 [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x1095e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1095e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1095e0 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1095e0 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x1095e0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1095e8 [0x88, 0x44, 0x24, 0x07] (StorePre 0x1095e8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1095e8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1095e8 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1095e8 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1095e8 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1095ec [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1095ec) (leaR64Effect 0x1095ec 7 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1095ec 7 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x1095ec 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1095f4 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x1095f4) (leaR64Effect 0x1095f4 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1095f4 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1095f4 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1095f9 [0x48, 0x8D, 0x54, 0x24, 0x30] (fun s => s.RIP = 0x1095f9) (leaR64Effect 0x1095f9 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1095f9 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x1095f9 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1095fe [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x1095fe) (movR64R64Effect 0x1095fe 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1095fe 1 3).toInstrSpec (mov_r64_r64_effect_step 0x1095fe 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x109601 [0x4D, 0x89, 0xF8] (fun s => s.RIP = 0x109601) (movR64R64Effect 0x109601 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x109601 8 15).toInstrSpec (mov_r64_r64_effect_step 0x109601 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x109604 [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x109604) (movR32R32Effect 0x109604 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x109604 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x109604 0x44 0xcd (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x109607 [0xE8, 0x84, 0xF2, 0xFF, 0xFF] (PushPre 0x109607 5) (callEffect (fun _ => 0x108890) 0x10960c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109607 0x108890 0x10960c).toInstrSpec (call_rel32_effect_step 0x109607 0xfffff284 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095c8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095d0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095d4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095d9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095dc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095e0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095e8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 62), (3, 3), (4, 4), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095ec) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (3, 3), (4, 4), (7, 66), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095f4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (3, 3), (4, 4), (6, 68), (7, 66), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095f9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 62), (2, 70), (3, 3), (4, 4), (6, 68), (7, 66), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1095fe) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 62), (1, 72), (2, 70), (3, 3), (4, 4), (6, 68), (7, 66), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109601) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 62), (1, 72), (2, 70), (3, 3), (4, 4), (6, 68), (7, 66), (8, 74), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109604) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 72), (2, 70), (3, 3), (4, 4), (5, 76), (6, 68), (7, 66), (8, 74), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109607) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 72), (2, 70), (3, 3), (4, 78), (5, 76), (6, 68), (7, 66), (8, 74), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108890) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l1095c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1095c1 :=
  Rest.liftedBlock (rest_l1095c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1095c1 x hx)

theorem rest_l10960c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10960c bytes_l10960c) (entryMap (live .l10960c))
      16 0x10960c bytes_l10960c b_l10960c := by
  have f0 : InstrSpec 0x10960c [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10960c) (movR64R64Effect 0x10960c 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10960c 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10960c 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10960f [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x10960f) (shrR64Effect 0x10960f 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10960f 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x10960f 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109613 [0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x109613 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x109613 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109613 0 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109613 0 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x109613 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10961b [0x88, 0x44, 0x24, 0x07] (StorePre 0x10961b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10961b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10961b 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10961b 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x10961b 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10961f [0x48, 0x8D, 0x44, 0x24, 0x07] (fun s => s.RIP = 0x10961f) (leaR64Effect 0x10961f 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10961f 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x10961f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x109624 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x109624) (movR64R64Effect 0x109624 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109624 1 14).toInstrSpec (mov_r64_r64_effect_step 0x109624 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109627 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x109627) (shrR64Effect 0x109627 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x109627 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x109627 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10962b [0x48, 0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x10962b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10962b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10962b 1 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10962b 1 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x10962b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x109633 [0x88, 0x4C, 0x24, 0x07] (StorePre 0x109633 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109633 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109633 4 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109633 4 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109633 1 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x109637 [0x48, 0x8D, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109637) (leaR64Effect 0x109637 7 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x109637 7 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (lea_r64_effect_step 0x109637 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10963f [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x10963f) (leaR64Effect 0x10963f 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10963f 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10963f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109644 [0x48, 0x8D, 0x54, 0x24, 0x30] (fun s => s.RIP = 0x109644) (leaR64Effect 0x109644 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x109644 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x109644 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x109649 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x109649) (movR64R64Effect 0x109649 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109649 1 13).toInstrSpec (mov_r64_r64_effect_step 0x109649 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10964c [0x4D, 0x89, 0xF0] (fun s => s.RIP = 0x10964c) (movR64R64Effect 0x10964c 8 14)
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10964c 8 14).toInstrSpec (mov_r64_r64_effect_step 0x10964c 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10964f [0x41, 0x89, 0xE9] (fun s => s.RIP = 0x10964f) (movR32R32Effect 0x10964f 3 9 5)
      [.gpr 5] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10964f 3 9 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x10964f 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x109652 [0xE8, 0x39, 0xF2, 0xFF, 0xFF] (PushPre 0x109652 5) (callEffect (fun _ => 0x108890) 0x109657)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109652 0x108890 0x109657).toInstrSpec (call_rel32_effect_step 0x109652 0xfffff239 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10960f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109613) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10961b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10961f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109624) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109627) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10962b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109633) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109637) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (7, 66), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10963f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 62), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109644) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 62), (2, 70), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109649) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10964c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (8, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10964f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (8, 74), (9, 76), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109652) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(1, 72), (2, 70), (3, 3), (4, 78), (5, 5), (6, 68), (7, 66), (8, 74), (9, 76), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108890) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l10960c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10960c :=
  Rest.liftedBlock (rest_l10960c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10960c x hx)

theorem rest_l109657_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x109657 bytes_l109657) [(0, 82), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x1096c7 bytes_l109657_1 b_l109657_1 := by
  have f20 : InstrSpec 0x1096c7 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x1096c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1096c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096c7 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1096c7 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1096c7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1096cc [0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (LoadPre 0x1096cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1096cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1096cc 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1096cc 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_r64_m64_effect_step 0x1096cc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1096d4 [0x88, 0x44, 0x24, 0x07] (StorePre 0x1096d4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1096d4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096d4 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1096d4 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1096d4 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x1096d8 [0x48, 0x8D, 0x44, 0x24, 0x07] (fun s => s.RIP = 0x1096d8) (leaR64Effect 0x1096d8 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1096d8 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x1096d8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1096dd [0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x1096dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1096dd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1096dd 1 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1096dd 1 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x1096dd 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x1096e5 [0x88, 0x4C, 0x24, 0x07] (StorePre 0x1096e5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1096e5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096e5 4 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1096e5 4 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1096e5 1 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x1096e9 [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1096e9) (leaR64Effect 0x1096e9 7 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1096e9 7 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x1096e9 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1096f1 [0x48, 0x8D, 0x74, 0x24, 0x60] (fun s => s.RIP = 0x1096f1) (leaR64Effect 0x1096f1 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1096f1 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x1096f1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1096f6 [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1096f6) (leaR64Effect 0x1096f6 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1096f6 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x1096f6 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1096fe [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x1096fe) (movR64R64Effect 0x1096fe 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1096fe 1 3).toInstrSpec (mov_r64_r64_effect_step 0x1096fe 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x109701 [0x4D, 0x89, 0xF8] (fun s => s.RIP = 0x109701) (movR64R64Effect 0x109701 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x109701 8 15).toInstrSpec (mov_r64_r64_effect_step 0x109701 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x109704 [0x41, 0x89, 0xE9] (fun s => s.RIP = 0x109704) (movR32R32Effect 0x109704 3 9 5)
      [.gpr 5] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x109704 3 9 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x109704 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x109707 [0x4C, 0x8B, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x109707 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x109707 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109707 15 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x109707 15 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_r64_m64_effect_step 0x109707 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x10970f [0x41, 0x57] (PushPre 0x10970f 2) (pushR64Effect 0x10970f 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10970f 2 15).toInstrSpec (push_r64_rex_effect_step 0x10970f 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f34 : InstrSpec 0x109711 [0x48, 0x8B, 0x5C, 0x24, 0x60] (LoadPre 0x109711 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109711 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109711 3 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x109711 3 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x109711 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x109716 [0x53] (PushPre 0x109716 1) (pushR64Effect 0x109716 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109716 1 3).toInstrSpec (push_r64_effect_step 0x109716 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f36 : InstrSpec 0x109717 [0xE8, 0x64, 0xF2, 0xFF, 0xFF] (PushPre 0x109717 5) (callEffect (fun _ => 0x108980) 0x10971c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109717 0x108980 0x10971c).toInstrSpec (call_rel32_effect_step 0x109717 0xfffff264 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096cc) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096d4) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 85), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096d8) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096dd) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 89), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096e5) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(1, 89), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096e9) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f26 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(1, 89), (2, 68), (3, 3), (4, 4), (5, 5), (7, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096f1) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(1, 89), (2, 68), (3, 3), (4, 4), (5, 5), (6, 94), (7, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096f6) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(1, 89), (2, 96), (3, 3), (4, 4), (5, 5), (6, 94), (7, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096fe) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(1, 98), (2, 96), (3, 3), (4, 4), (5, 5), (6, 94), (7, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109701) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f30 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(1, 98), (2, 96), (3, 3), (4, 4), (5, 5), (6, 94), (7, 92), (8, 100), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109704) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f31 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(1, 98), (2, 96), (3, 3), (4, 4), (5, 5), (6, 94), (7, 92), (8, 100), (9, 102), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109707) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f32 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(1, 98), (2, 96), (3, 3), (4, 4), (5, 5), (6, 94), (7, 92), (8, 100), (9, 102), (12, 12), (13, 13), (14, 14), (15, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10970f) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f33 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(1, 98), (2, 96), (3, 3), (4, 106), (5, 5), (6, 94), (7, 92), (8, 100), (9, 102), (12, 12), (13, 13), (14, 14), (15, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109711) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(1, 98), (2, 96), (3, 108), (4, 106), (5, 5), (6, 94), (7, 92), (8, 100), (9, 102), (12, 12), (13, 13), (14, 14), (15, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109716) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f35 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(1, 98), (2, 96), (3, 108), (4, 110), (5, 5), (6, 94), (7, 92), (8, 100), (9, 102), (12, 12), (13, 13), (14, 14), (15, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109717) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f36 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(1, 98), (2, 96), (3, 108), (4, 112), (5, 5), (6, 94), (7, 92), (8, 100), (9, 102), (12, 12), (13, 13), (14, 14), (15, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108980) f36 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 114) (by decide) (by decide) rfl rfl

theorem rest_l109657 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109657 bytes_l109657) (entryMap (live .l109657))
      37 0x109657 bytes_l109657 b_l109657 := by
  have f0 : InstrSpec 0x109657 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x109657 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x109657 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109657 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109657 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x109657 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10965f [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x10965f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10965f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10965f 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10965f 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10965f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x109664 [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x109664 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x109664 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109664 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109664 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x109664 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10966c [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10966c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10966c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10966c 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10966c 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10966c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x109671 [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x109671 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x109671 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109671 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109671 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x109671 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109679 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x109679 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109679 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109679 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109679 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109679 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10967e [0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x10967e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10967e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10967e 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10967e 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x10967e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x109686 [0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x109686 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x109686 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109686 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109686 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x109686 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10968e [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x10968e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10968e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10968e 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10968e 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10968e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x109693 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x109693 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109693 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109693 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109693 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109693 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x109698 [0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109698) (leaR64Effect 0x109698 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x109698 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (lea_r64_effect_step 0x109698 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1096a0 [0x48, 0x8B, 0x02] (LoadPre 0x1096a0 (fun s => AddrMode.addr (.base 2 .none) s (0x1096a0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1096a0 0 (.base 2 .none))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1096a0 0 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1096a0 0x48 (by decide) 0 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1096a3 [0x48, 0x8B, 0x4A, 0x08] (LoadPre 0x1096a3 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1096a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1096a3 1 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1096a3 1 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1096a3 0x48 (by decide) 1 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1096a7 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x1096a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1096a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096a7 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1096a7 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1096a7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1096ac [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x1096ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1096ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096ac 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1096ac 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1096ac 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1096b1 [0x48, 0x8B, 0x42, 0x10] (LoadPre 0x1096b1 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1096b1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1096b1 0 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1096b1 0 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1096b1 0x48 (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1096b5 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x1096b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1096b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096b5 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1096b5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1096b5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1096ba [0x48, 0x8B, 0x42, 0x18] (LoadPre 0x1096ba (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1096ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1096ba 0 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1096ba 0 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1096ba 0x48 (by decide) 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1096be [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x1096be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1096be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096be 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1096be 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1096be 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1096c3 [0x48, 0x8B, 0x42, 0x20] (LoadPre 0x1096c3 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1096c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1096c3 0 (.base 2 (.d8 0x20)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1096c3 0 (.base 2 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1096c3 0x48 (by decide) 0 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10965f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109664) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10966c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109671) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109679) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10967e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109686) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10968e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109693) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109698) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 64), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096a0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 64), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096a3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096a7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096ac) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 70), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096b1) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096b5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096ba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096be) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096c3) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1096c7) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109657_1 code

theorem block_l109657 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109657 :=
  Rest.liftedBlock (rest_l109657 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109657 x hx)

theorem rest_l10971c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10971c bytes_l10971c) (entryMap (live .l10971c))
      15 0x10971c bytes_l10971c b_l10971c := by
  have f0 : InstrSpec 0x10971c [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x10971c) (addR64Imm8Effect 0x10971c 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10971c 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10971c 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109720 [0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00] (LoadPre 0x109720 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x109720 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109720 0 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109720 0 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_r64_m64_effect_step 0x109720 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109728 [0x88, 0x44, 0x24, 0x07] (StorePre 0x109728 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109728 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109728 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109728 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109728 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10972c [0x48, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x10972c) (leaR64Effect 0x10972c 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x10972c 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x10972c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x109731 [0x48, 0x8B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x109731 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x109731 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109731 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109731 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_r64_m64_effect_step 0x109731 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109739 [0x88, 0x44, 0x24, 0x07] (StorePre 0x109739 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109739 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109739 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109739 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109739 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10973d [0x48, 0x8D, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10973d) (leaR64Effect 0x10973d 7 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10973d 7 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (lea_r64_effect_step 0x10973d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109745 [0x48, 0x8D, 0x74, 0x24, 0x60] (fun s => s.RIP = 0x109745) (leaR64Effect 0x109745 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x109745 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x109745 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10974a [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10974a) (leaR64Effect 0x10974a 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x10974a 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x10974a 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x109752 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x109752) (movR64R64Effect 0x109752 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109752 1 13).toInstrSpec (mov_r64_r64_effect_step 0x109752 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x109755 [0x4D, 0x89, 0xF0] (fun s => s.RIP = 0x109755) (movR64R64Effect 0x109755 8 14)
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x109755 8 14).toInstrSpec (mov_r64_r64_effect_step 0x109755 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109758 [0x41, 0x89, 0xE9] (fun s => s.RIP = 0x109758) (movR32R32Effect 0x109758 3 9 5)
      [.gpr 5] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x109758 3 9 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x109758 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10975b [0x41, 0x57] (PushPre 0x10975b 2) (pushR64Effect 0x10975b 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10975b 2 15).toInstrSpec (push_r64_rex_effect_step 0x10975b 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x10975d [0x53] (PushPre 0x10975d 1) (pushR64Effect 0x10975d 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10975d 1 3).toInstrSpec (push_r64_effect_step 0x10975d 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x10975e [0xE8, 0x1D, 0xF2, 0xFF, 0xFF] (PushPre 0x10975e 5) (callEffect (fun _ => 0x108980) 0x109763)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10975e 0x108980 0x109763).toInstrSpec (call_rel32_effect_step 0x10975e 0xfffff21d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109720) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109728) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10972c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109731) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109739) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10973d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109745) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10974a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 59), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109752) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109755) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (8, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109758) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10975b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 74), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10975d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 76), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10975e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 78), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108980) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l10971c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10971c :=
  Rest.liftedBlock (rest_l10971c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10971c x hx)

theorem rest_l109763_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x109763 bytes_l109763) [(0, 81), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      5 0x1097e2 bytes_l109763_1 b_l109763_1 := by
  have f20 : InstrSpec 0x1097e2 [0x48, 0x8B, 0x42, 0x20] (LoadPre 0x1097e2 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1097e2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1097e2 0 (.base 2 (.d8 0x20)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1097e2 0 (.base 2 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1097e2 0x48 (by decide) 0 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1097e6 [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x1097e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1097e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097e6 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1097e6 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x1097e6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1097ee [0x48, 0x8B, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00] (LoadPre 0x1097ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1097ee + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1097ee 6 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1097ee 6 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_r64_m64_effect_step 0x1097ee 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x1097f6 [0x29, 0xEE] (fun s => s.RIP = 0x1097f6) (subR32R32Effect 0x1097f6 2 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1097f6 2 6 5).toInstrSpec (sub_r32_r32_effect_step 0x1097f6 0xee (by decide)) pre_rip
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097e6) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097ee) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (6, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097f6) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 90) f23 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 91) (ρ' := [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (6, 89), (12, 12), (13, 13), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097f8) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 92) (jcc_rel32_effect_step 0x1097f8 4 0x14a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l109763 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109763 bytes_l109763) (entryMap (live .l109763))
      25 0x109763 bytes_l109763 b_l109763 := by
  have f0 : InstrSpec 0x109763 [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x109763) (addR64Imm8Effect 0x109763 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109763 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x109763 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109767 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x109767 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x109767 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109767 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109767 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x109767 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10976f [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10976f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10976f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10976f 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10976f 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10976f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x109777 [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x109777 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x109777 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109777 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109777 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x109777 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10977f [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x10977f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10977f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10977f 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10977f 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x10977f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x109784 [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x109784 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x109784 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109784 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109784 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x109784 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10978c [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x10978c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10978c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10978c 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10978c 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10978c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x109791 [0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x109791 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109791 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109791 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109791 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x109791 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109799 [0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x109799 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x109799 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109799 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109799 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x109799 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1097a1 [0x48, 0x89, 0x4C, 0x24, 0x68] (StorePre 0x1097a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1097a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1097a1 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1097a1 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1097a1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1097a6 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x1097a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1097a6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1097a6 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1097a6 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x1097a6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1097ab [0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1097ab) (leaR64Effect 0x1097ab 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1097ab 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (lea_r64_effect_step 0x1097ab 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1097b3 [0x48, 0x8B, 0x02] (LoadPre 0x1097b3 (fun s => AddrMode.addr (.base 2 .none) s (0x1097b3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1097b3 0 (.base 2 .none))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1097b3 0 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1097b3 0x48 (by decide) 0 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1097b6 [0x48, 0x8B, 0x4A, 0x08] (LoadPre 0x1097b6 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1097b6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1097b6 1 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1097b6 1 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1097b6 0x48 (by decide) 1 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1097ba [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1097ba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1097ba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097ba 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1097ba 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1097ba 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1097c2 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1097c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1097c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097c2 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1097c2 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1097c2 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1097ca [0x48, 0x8B, 0x42, 0x10] (LoadPre 0x1097ca (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1097ca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1097ca 0 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1097ca 0 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1097ca 0x48 (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1097ce [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1097ce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1097ce + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097ce 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1097ce 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1097ce 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1097d6 [0x48, 0x8B, 0x42, 0x18] (LoadPre 0x1097d6 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1097d6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1097d6 0 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1097d6 0 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1097d6 0x48 (by decide) 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1097da [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1097da 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1097da + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097da 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1097da 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1097da 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109767) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10976f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109777) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10977f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109784) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10978c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109791) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109799) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097a1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097a6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097ab) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 64), (1, 66), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097b3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 66), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097b6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097ba) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097c2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097ca) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097ce) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097d6) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097da) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1097e2) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109763_1 code

theorem block_l109763 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109763 :=
  Rest.liftedBlock (rest_l109763 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109763 x hx)

theorem rest_l1097fe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1097fe bytes_l1097fe) (entryMap (live .l1097fe))
      3 0x1097fe bytes_l1097fe b_l1097fe := by
  have f0 : InstrSpec 0x1097fe [0x48, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x1097fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1097fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1097fe 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1097fe 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1097fe 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109803 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x109803) (testR64R64Effect 0x109803 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x109803 2 2).toInstrSpec (test_r64_r64_effect_step 0x109803 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109803) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109806) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x109806 5 0x1c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1097fe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1097fe :=
  Rest.liftedBlock (rest_l1097fe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1097fe x hx)

theorem rest_l109808 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109808 bytes_l109808) (entryMap (live .l109808))
      2 0x109808 bytes_l109808 b_l109808 := by
  have f0 : InstrSpec 0x109808 [0x48, 0x83, 0x7C, 0x24, 0x38, 0x00] (LoadPre 0x109808 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109808 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x109808 6 64 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x109808 6 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (cmp_m64_imm8_effect_step 0x109808 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10980e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x10980e 5 0x14) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109808 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109808 :=
  Rest.liftedBlock (rest_l109808 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109808 x hx)

theorem rest_l109810 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109810 bytes_l109810) (entryMap (live .l109810))
      2 0x109810 bytes_l109810 b_l109810 := by
  have f0 : InstrSpec 0x109810 [0x48, 0x83, 0x7C, 0x24, 0x40, 0x00] (LoadPre 0x109810 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109810 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x109810 6 64 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x109810 6 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (cmp_m64_imm8_effect_step 0x109810 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109816) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x109816 5 0xc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109810 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109810 :=
  Rest.liftedBlock (rest_l109810 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109810 x hx)

theorem rest_l109818 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109818 bytes_l109818) (entryMap (live .l109818))
      2 0x109818 bytes_l109818 b_l109818 := by
  have f0 : InstrSpec 0x109818 [0x48, 0x83, 0x7C, 0x24, 0x48, 0x00] (LoadPre 0x109818 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109818 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x109818 6 64 (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x109818 6 (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (cmp_m64_imm8_effect_step 0x109818 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10981e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10981e 4 0x124) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109818 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109818 :=
  Rest.liftedBlock (rest_l109818 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109818 x hx)

theorem rest_l109824_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x109824 bytes_l109824) [(0, 84), (1, 86), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x109884 bytes_l109824_1 b_l109824_1 := by
  exact Rest.jcc (n := 89) (jcc_rel32_effect_step 0x109884 4 0xfffffd26) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l109824 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109824 bytes_l109824) (entryMap (live .l109824))
      21 0x109824 bytes_l109824 b_l109824 := by
  have f0 : InstrSpec 0x109824 [0x89, 0xF0] (fun s => s.RIP = 0x109824) (movR32R32Effect 0x109824 2 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x109824 2 0 6).toInstrSpec (mov_r32_r32_effect_step 0x109824 0xf0 (by decide)) pre_rip
  have f1 : InstrSpec 0x109826 [0xF7, 0xD0] (fun s => s.RIP = 0x109826) (notR32Effect 0x109826 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x109826 2 0).toInstrSpec (not_r32_effect_step 0x109826 0xd0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109828 [0x8D, 0x4E, 0xC2] (fun s => s.RIP = 0x109828) (leaR32Effect 0x109828 3 1 (.base 6 (.d8 0xc2)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x109828 3 1 (.base 6 (.d8 0xc2))).toInstrSpec (lea_r32_effect_step 0x109828 1 (.base 6 (.d8 0xc2)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10982b [0x21, 0xC1] (fun s => s.RIP = 0x10982b) (andR32R32Effect 0x10982b 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x10982b 2 1 0).toInstrSpec (and_r32_r32_effect_step 0x10982b 0xc1 (by decide)) pre_rip
  have f4 : InstrSpec 0x10982d [0xC1, 0xE9, 0x1F] (fun s => s.RIP = 0x10982d) (shrR32Effect 0x10982d 3 1 31)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10982d 3 1 31).toInstrSpec (shr_r32_imm8_effect_step 0x10982d 0xe9 0x1f (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x109830 [0x88, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x109830 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109830 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x109830 7 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109830 7 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m8_r8_effect_step 0x109830 1 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x109837 [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109837) (leaR64Effect 0x109837 7 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x109837 7 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x109837 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10983f [0x0F, 0xB6, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x10983f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10983f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10983f 8 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10983f 8 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m8_effect_step 0x10983f 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109847 [0xF7, 0xD8] (fun s => s.RIP = 0x109847) (negR32Effect 0x109847 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR32Effect_footprint 0x109847 2 0).toInstrSpec (neg_r32_effect_step 0x109847 0xd8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x109849 [0x48, 0x89, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x109849 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x109849 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109849 6 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109849 6 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x109849 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x109851 [0x41, 0x89, 0xF1] (fun s => s.RIP = 0x109851) (movR32R32Effect 0x109851 3 9 6)
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x109851 3 9 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x109851 0x41 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109854 [0x41, 0x83, 0xF1, 0x3E] (fun s => s.RIP = 0x109854) (xorR32Imm8Effect 0x109854 4 9 0x3e)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x109854 4 9 0x3e).toInstrSpec (xor_r32_imm8_rex_effect_step 0x109854 0x41 0xf1 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x109858 [0x41, 0x21, 0xC1] (fun s => s.RIP = 0x109858) (andR32R32Effect 0x109858 3 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (andR32R32Effect_footprint 0x109858 3 9 0).toInstrSpec (and_r32_r32_rex_effect_step 0x109858 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10985b [0x41, 0x83, 0xF1, 0x3E] (fun s => s.RIP = 0x10985b) (xorR32Imm8Effect 0x10985b 4 9 0x3e)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x10985b 4 9 0x3e).toInstrSpec (xor_r32_imm8_rex_effect_step 0x10985b 0x41 0xf1 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10985f [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x10985f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10985f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10985f 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10985f 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10985f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x109864 [0x0F, 0xB6, 0x44, 0x24, 0x28] (LoadPre 0x109864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109864 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109864 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109864 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x109864 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x109869 [0x88, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x109869 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109869 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x109869 7 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109869 7 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m8_r8_effect_step 0x109869 0 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x109870 [0x0F, 0xB6, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x109870 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109870 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109870 8 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109870 8 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m8_effect_step 0x109870 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x109878 [0x0F, 0xB6, 0x4C, 0x24, 0x50] (LoadPre 0x109878 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109878 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109878 5 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109878 5 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x109878 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10987d [0x88, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x10987d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10987d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10987d 7 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10987d 7 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m8_r8_effect_step 0x10987d 1 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109826) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109828) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10982b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10982d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109830) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 61), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109837) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 61), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10983f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 61), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109847) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109849) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109851) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 70), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109854) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 72), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109858) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 74), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10985b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10985f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109864) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 61), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109869) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 61), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109870) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 61), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109878) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 84), (1, 86), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10987d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 84), (1, 86), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109884) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109824_1 code

theorem block_l109824 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109824 :=
  Rest.liftedBlock (rest_l109824 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109824 x hx)

theorem rest_l10988a_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10988a bytes_l10988a) [(0, 83), (1, 69), (2, 87), (3, 85), (4, 4), (6, 91), (7, 63), (8, 55), (9, 9), (12, 12), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x1098d3 bytes_l10988a_1 b_l10988a_1 := by
  have f20 : InstrSpec 0x1098d3 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1098d3) (movR32Imm32Effect 0x1098d3 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x1098d3 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1098d3 0xbf (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 83), (1, 69), (2, 87), (3, 85), (4, 4), (6, 91), (7, 93), (8, 55), (9, 9), (12, 12), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098d8) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 95) (jmp_rel8_effect_step 0x1098d8 0x4b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l10988a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10988a bytes_l10988a) (entryMap (live .l10988a))
      22 0x10988a bytes_l10988a b_l10988a := by
  have f0 : InstrSpec 0x10988a [0x0F, 0xB6, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x10988a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10988a + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10988a 8 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10988a 8 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m8_effect_step 0x10988a 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109892 [0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x109892) (movR64Imm64Effect 0x109892 8 0x7fffffffffffffff)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x109892 8 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x109892 0x49 0xb8 (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f2 : InstrSpec 0x10989c [0x4C, 0x21, 0xC2] (fun s => s.RIP = 0x10989c) (andR64R64Effect 0x10989c 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10989c 2 8).toInstrSpec (and_r64_r64_effect_step 0x10989c 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10989f [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x10989f) (movR64R64Effect 0x10989f 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10989f 7 2).toInstrSpec (mov_r64_r64_effect_step 0x10989f 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1098a2 [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x1098a2) (negR64Effect 0x1098a2 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x1098a2 7).toInstrSpec (neg_r64_effect_step 0x1098a2 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1098a5 [0x48, 0x31, 0xD7] (fun s => s.RIP = 0x1098a5) (xorR64R64Effect 0x1098a5 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1098a5 7 2).toInstrSpec (xor_r64_r64_effect_step 0x1098a5 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1098a8 [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x1098a8) (negR64Effect 0x1098a8 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x1098a8 1).toInstrSpec (neg_r64_effect_step 0x1098a8 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1098ab [0x48, 0x21, 0xF9] (fun s => s.RIP = 0x1098ab) (andR64R64Effect 0x1098ab 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1098ab 1 7).toInstrSpec (and_r64_r64_effect_step 0x1098ab 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1098ae [0x48, 0x31, 0xD1] (fun s => s.RIP = 0x1098ae) (xorR64R64Effect 0x1098ae 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1098ae 1 2).toInstrSpec (xor_r64_r64_effect_step 0x1098ae 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1098b1 [0x4C, 0x21, 0xC6] (fun s => s.RIP = 0x1098b1) (andR64R64Effect 0x1098b1 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1098b1 6 8).toInstrSpec (and_r64_r64_effect_step 0x1098b1 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1098b4 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x1098b4) (movR64R64Effect 0x1098b4 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1098b4 2 6).toInstrSpec (mov_r64_r64_effect_step 0x1098b4 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1098b7 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x1098b7) (negR64Effect 0x1098b7 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x1098b7 2).toInstrSpec (neg_r64_effect_step 0x1098b7 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1098ba [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x1098ba) (xorR64R64Effect 0x1098ba 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1098ba 2 6).toInstrSpec (xor_r64_r64_effect_step 0x1098ba 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1098bd [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x1098bd) (negR64Effect 0x1098bd 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x1098bd 0).toInstrSpec (neg_r64_effect_step 0x1098bd 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1098c0 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x1098c0) (andR64R64Effect 0x1098c0 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1098c0 0 2).toInstrSpec (and_r64_r64_effect_step 0x1098c0 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1098c3 [0x48, 0x31, 0xF0] (fun s => s.RIP = 0x1098c3) (xorR64R64Effect 0x1098c3 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1098c3 0 6).toInstrSpec (xor_r64_r64_effect_step 0x1098c3 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1098c6 [0xBB, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1098c6) (movR32Imm32Effect 0x1098c6 5 3 0x1)
      [] [] [.reg 3, .rip] :=
    (movR32Imm32Effect_footprint 0x1098c6 5 3 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1098c6 0xbb (by decide) 0x1) pre_rip
  have f17 : InstrSpec 0x1098cb [0x44, 0x89, 0xCA] (fun s => s.RIP = 0x1098cb) (movR32R32Effect 0x1098cb 3 2 9)
      [.gpr 9] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1098cb 3 2 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1098cb 0x44 0xca (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1098ce [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x1098ce) (xorR32R32Effect 0x1098ce 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1098ce 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x1098ce 0x45 0xff (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1098d1 [0x31, 0xF6] (fun s => s.RIP = 0x1098d1) (xorR32R32Effect 0x1098d1 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1098d1 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1098d1 0xf6 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109892) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10989c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 57), (4, 4), (6, 6), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10989f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 57), (4, 4), (6, 6), (7, 59), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098a2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 57), (4, 4), (6, 6), (7, 61), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098a5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 57), (4, 4), (6, 6), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098a8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 57), (4, 4), (6, 6), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098ab) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 57), (4, 4), (6, 6), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098ae) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 57), (4, 4), (6, 6), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098b1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 57), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098b4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 69), (2, 73), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098b7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 69), (2, 75), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098ba) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 69), (2, 77), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098bd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 69), (2, 77), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098c0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 69), (2, 77), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098c3) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 69), (2, 77), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098c6) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 69), (2, 77), (3, 85), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098cb) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 69), (2, 87), (3, 85), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098ce) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 83), (1, 69), (2, 87), (3, 85), (4, 4), (6, 71), (7, 63), (8, 55), (9, 9), (12, 12), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098d1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 83), (1, 69), (2, 87), (3, 85), (4, 4), (6, 91), (7, 63), (8, 55), (9, 9), (12, 12), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098d3) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10988a_1 code

theorem block_l10988a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10988a :=
  Rest.liftedBlock (rest_l10988a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10988a x hx)

theorem rest_l1098e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1098e0 bytes_l1098e0) (entryMap (live .l1098e0))
      2 0x1098e0 bytes_l1098e0 b_l1098e0 := by
  have f0 : InstrSpec 0x1098e0 [0x4D, 0x85, 0xE4] (fun s => s.RIP = 0x1098e0) (testR64R64Effect 0x1098e0 12 12)
      [.gpr 12, .gpr 12] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1098e0 12 12).toInstrSpec (test_r64_r64_effect_step 0x1098e0 0x4d 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 55) f0 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1098e3 14 0x4b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1098e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1098e0 :=
  Rest.liftedBlock (rest_l1098e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1098e0 x hx)

theorem rest_l1098e5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1098e5 bytes_l1098e5) (entryMap (live .l1098e5))
      12 0x1098e5 bytes_l1098e5 b_l1098e5 := by
  have f0 : InstrSpec 0x1098e5 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x1098e5) (movR64R64Effect 0x1098e5 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1098e5 8 1).toInstrSpec (mov_r64_r64_effect_step 0x1098e5 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1098e8 [0x49, 0x29, 0xC0] (fun s => s.RIP = 0x1098e8) (subR64R64Effect 0x1098e8 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1098e8 8 0).toInstrSpec (sub_r64_r64_effect_step 0x1098e8 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1098eb [0xB8, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1098eb) (movR32Imm32Effect 0x1098eb 5 0 0x2)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1098eb 5 0 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x1098eb 0xb8 (by decide) 0x2) pre_rip
  have f3 : InstrSpec 0x1098f0 [0x4C, 0x29, 0xE0] (fun s => s.RIP = 0x1098f0) (subR64R64Effect 0x1098f0 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1098f0 0 12).toInstrSpec (sub_r64_r64_effect_step 0x1098f0 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1098f3 [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x1098f3) (movR64R64Effect 0x1098f3 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1098f3 13 6).toInstrSpec (mov_r64_r64_effect_step 0x1098f3 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1098f6 [0x49, 0x29, 0xDD] (fun s => s.RIP = 0x1098f6) (subR64R64Effect 0x1098f6 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1098f6 13 3).toInstrSpec (sub_r64_r64_effect_step 0x1098f6 0x49 0xdd (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1098f9 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x1098f9) (movR64R64Effect 0x1098f9 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1098f9 14 7).toInstrSpec (mov_r64_r64_effect_step 0x1098f9 0x49 0xfe (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1098fc [0x4D, 0x29, 0xFE] (fun s => s.RIP = 0x1098fc) (subR64R64Effect 0x1098fc 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1098fc 14 15).toInstrSpec (sub_r64_r64_effect_step 0x1098fc 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1098ff [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x1098ff) (movR64R64Effect 0x1098ff 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1098ff 15 7).toInstrSpec (mov_r64_r64_effect_step 0x1098ff 0x49 0xff (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x109902 [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x109902) (movR64R64Effect 0x109902 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x109902 3 6).toInstrSpec (mov_r64_r64_effect_step 0x109902 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x109905 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x109905) (movR64R64Effect 0x109905 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x109905 12 0).toInstrSpec (mov_r64_r64_effect_step 0x109905 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109908 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x109908) (movR64R64Effect 0x109908 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109908 0 1).toInstrSpec (mov_r64_r64_effect_step 0x109908 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098e8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098eb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098f0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098f3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098f6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098f9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 63), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098fc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 63), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1098ff) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109902) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 71), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109905) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 71), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 73), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109908) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 71), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 73), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10990b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l1098e5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1098e5 :=
  Rest.liftedBlock (rest_l1098e5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1098e5 x hx)

theorem rest_l10990b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10990b bytes_l10990b) (entryMap (live .l10990b))
      8 0x10990b bytes_l10990b b_l10990b := by
  have f0 : InstrSpec 0x10990b [0x49, 0xD1, 0xF8] (fun s => s.RIP = 0x10990b) (sarR64Effect 0x10990b 3 8 1)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (sarR64Effect_footprint 0x10990b 3 8 1).toInstrSpec (sar_r64_one_effect_step 0x10990b 0x49 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10990e [0x48, 0x01, 0xDB] (fun s => s.RIP = 0x10990e) (addR64R64Effect 0x10990e 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10990e 3 3).toInstrSpec (add_r64_r64_effect_step 0x10990e 0x48 0xdb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109911 [0x4D, 0x01, 0xFF] (fun s => s.RIP = 0x109911) (addR64R64Effect 0x109911 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109911 15 15).toInstrSpec (add_r64_r64_effect_step 0x109911 0x4d 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x109914 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x109914) (movR64R64Effect 0x109914 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109914 1 8).toInstrSpec (mov_r64_r64_effect_step 0x109914 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x109917 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x109917) (movR64R64Effect 0x109917 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x109917 6 13).toInstrSpec (mov_r64_r64_effect_step 0x109917 0x4c 0xee (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10991a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10991a) (movR64R64Effect 0x10991a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10991a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10991a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10991d [0xFF, 0xCA] (fun s => s.RIP = 0x10991d) (decR32Effect 0x10991d 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (decR32Effect_footprint 0x10991d 2 2).toInstrSpec (dec_r32_effect_step 0x10991d 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10990e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 55), (4, 4), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109911) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 55), (4, 4), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109914) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 55), (4, 4), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109917) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 55), (4, 4), (6, 61), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10991a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 55), (4, 4), (6, 61), (7, 63), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10991d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 66) f6 .ZF (fun _ => rfl) (decR32Effect_fresh 0x10991d 2 2 _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 59), (2, 65), (3, 55), (4, 4), (6, 61), (7, 63), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 57), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10991f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel32_effect_step 0x10991f 4 0xfffffc9c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10990b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10990b :=
  Rest.liftedBlock (rest_l10990b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10990b x hx)

theorem rest_l109925 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109925 bytes_l109925) (entryMap (live .l109925))
      2 0x109925 bytes_l109925 b_l109925 := by
  have f0 : InstrSpec 0x109925 [0xF6, 0xC1, 0x01] (fun s => s.RIP = 0x109925) (testR8Imm8LowEffect 0x109925 1 0x1)
      [.gpr 1] [] [.flags, .rip] :=
    (testR8Imm8LowEffect_footprint 0x109925 1 0x1).toInstrSpec (test_r8_imm8_low_effect_step 0x109925 0xc1 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109928) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x109928 5 0xb6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109925 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109925 :=
  Rest.liftedBlock (rest_l109925 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109925 x hx)

theorem rest_l10992a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10992a bytes_l10992a) (entryMap (live .l10992a))
      2 0x10992a bytes_l10992a b_l10992a := by
  have f0 : InstrSpec 0x10992a [0x49, 0x83, 0xC4, 0x02] (fun s => s.RIP = 0x10992a) (addR64Imm8Effect 0x10992a 12 0x2)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10992a 12 0x2).toInstrSpec (add_r64_imm8_effect_step 0x10992a 0x49 0xc4 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10992e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x10992e 0xd (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10992a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10992a :=
  Rest.liftedBlock (rest_l10992a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10992a x hx)

theorem rest_l109930 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109930 bytes_l109930) (entryMap (live .l109930))
      4 0x109930 bytes_l109930 b_l109930 := by
  have f0 : InstrSpec 0x109930 [0x48, 0x01, 0xC1] (fun s => s.RIP = 0x109930) (addR64R64Effect 0x109930 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109930 1 0).toInstrSpec (add_r64_r64_effect_step 0x109930 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109933 [0x49, 0x83, 0xC4, 0x02] (fun s => s.RIP = 0x109933) (addR64Imm8Effect 0x109933 12 0x2)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109933 12 0x2).toInstrSpec (add_r64_imm8_effect_step 0x109933 0x49 0xc4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109937 [0x48, 0x01, 0xDE] (fun s => s.RIP = 0x109937) (addR64R64Effect 0x109937 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109937 6 3).toInstrSpec (add_r64_r64_effect_step 0x109937 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10993a [0x4C, 0x01, 0xFF] (fun s => s.RIP = 0x10993a) (addR64R64Effect 0x10993a 7 15)
      [.gpr 7, .gpr 15] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10993a 7 15).toInstrSpec (add_r64_r64_effect_step 0x10993a 0x4c 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109933) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109937) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (12, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10993a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (12, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10993d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l109930 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109930 :=
  Rest.liftedBlock (rest_l109930 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109930 x hx)

theorem rest_l10993d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10993d bytes_l10993d) (entryMap (live .l10993d))
      4 0x10993d bytes_l10993d b_l10993d := by
  have f0 : InstrSpec 0x10993d [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x10993d) (movR64R64Effect 0x10993d 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10993d 14 7).toInstrSpec (mov_r64_r64_effect_step 0x10993d 0x49 0xfe (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109940 [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x109940) (movR64R64Effect 0x109940 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109940 13 6).toInstrSpec (mov_r64_r64_effect_step 0x109940 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109943 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x109943) (movR64R64Effect 0x109943 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x109943 8 1).toInstrSpec (mov_r64_r64_effect_step 0x109943 0x49 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109940) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (13, 55), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109943) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (12, 12), (13, 55), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109946) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x109946 0xc3 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10993d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10993d :=
  Rest.liftedBlock (rest_l10993d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10993d x hx)

theorem rest_l109948 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109948 bytes_l109948) (entryMap (live .l109948))
      11 0x109948 bytes_l109948 b_l109948 := by
  have f0 : InstrSpec 0x109948 [0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (LoadPre 0x109948 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x109948 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109948 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109948 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_r64_m64_effect_step 0x109948 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109950 [0x48, 0x0B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (LoadPre 0x109950 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x109950 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109950 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109950 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (or_r64_m64_effect_step 0x109950 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109958 [0x48, 0x0B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x109958 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x109958 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109958 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109958 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (or_r64_m64_effect_step 0x109958 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109960 [0x48, 0x0B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x109960 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x109960 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109960 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109960 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (or_r64_m64_effect_step 0x109960 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x109968 [0x0F, 0x95, 0xC3] (fun s => s.RIP = 0x109968) (atFlags (condHolds 5) (setccR8Effect 0x109968 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x109968 3 3 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x109968 5 0xc3 (by decide) (by decide) c)) pre_rip
  have f5 : InstrSpec 0x10996b [0x8B, 0x54, 0x24, 0x28] (LoadPre 0x10996b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10996b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10996b 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x10996b 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x10996b 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10996f [0x48, 0x8D, 0x74, 0x24, 0x60] (fun s => s.RIP = 0x10996f) (leaR64Effect 0x10996f 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10996f 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x10996f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109974 [0x4C, 0x8B, 0xB4, 0x24, 0x20, 0x01, 0x00, 0x00] (LoadPre 0x109974 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x109974 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109974 14 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x109974 14 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_r64_m64_effect_step 0x109974 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10997c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10997c) (movR64R64Effect 0x10997c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10997c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10997c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10997f [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x10997f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10997f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10997f 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10997f 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10997f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x109984 [0xE8, 0x77, 0x02, 0x00, 0x00] (PushPre 0x109984 5) (callEffect (fun _ => 0x109c00) 0x109989)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109984 0x109c00 0x109989).toInstrSpec (call_rel32_effect_step 0x109984 0x277 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109950) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109958) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109960) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109968) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 61), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10996b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 63), (3, 61), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10996f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 63), (3, 61), (4, 4), (5, 5), (6, 65), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109974) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 63), (3, 61), (4, 4), (5, 5), (6, 65), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10997c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 63), (3, 61), (4, 4), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10997f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 71), (2, 63), (3, 61), (4, 4), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109984) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 71), (2, 63), (3, 61), (4, 73), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c00) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l109948 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109948 :=
  Rest.liftedBlock (rest_l109948 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109948 x hx)

theorem rest_l109989 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109989 bytes_l109989) (entryMap (live .l109989))
      17 0x109989 bytes_l109989 b_l109989 := by
  have f0 : InstrSpec 0x109989 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x109989 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109989 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109989 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109989 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109989 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10998e [0x48, 0x83, 0xF0, 0x01] (fun s => s.RIP = 0x10998e) (xorR64Imm8Effect 0x10998e 0 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x10998e 0 0x1).toInstrSpec (xor_r64_imm8_effect_step 0x10998e 0x48 0xf0 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109992 [0x48, 0x0B, 0x44, 0x24, 0x10] (LoadPre 0x109992 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109992 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x109992 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109992 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (or_r64_m64_effect_step 0x109992 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109997 [0x48, 0x0B, 0x44, 0x24, 0x18] (LoadPre 0x109997 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109997 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x109997 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109997 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (or_r64_m64_effect_step 0x109997 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10999c [0x48, 0x0B, 0x44, 0x24, 0x20] (LoadPre 0x10999c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10999c + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x10999c 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x10999c 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (or_r64_m64_effect_step 0x10999c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1099a1 [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x1099a1) (atFlags (condHolds 4) (setccR8Effect 0x1099a1 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1099a1 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1099a1 4 0xc0 (by decide) (by decide) c)) pre_rip
  have f6 : InstrSpec 0x1099a4 [0x20, 0xD8] (fun s => s.RIP = 0x1099a4) (andR8R8Effect 0x1099a4 2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR8R8Effect_footprint 0x1099a4 2 0 3).toInstrSpec (and_r8_r8_effect_step 0x1099a4 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1099a6 [0x41, 0x88, 0x46, 0x20] (StorePre 0x1099a6 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1099a6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1099a6 4 0 (.base 14 (.d8 0x20)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM8R8Effect_footprint 0x1099a6 4 0 (.base 14 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1099a6 0x41 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1099aa [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x1099aa) (movR64R64Effect 0x1099aa 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1099aa 0 14).toInstrSpec (mov_r64_r64_effect_step 0x1099aa 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1099ad [0x48, 0x81, 0xC4, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1099ad) (addR64Imm32Effect 0x1099ad 4 0x158)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1099ad 4 0x158).toInstrSpec (add_r64_imm32_effect_step 0x1099ad 0x48 0xc4 0x158 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1099b4 [0x5B] (PopPre 0x1099b4) (popR64Effect 0x1099b4 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1099b4 1 3).toInstrSpec (pop_r64_effect_step 0x1099b4 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x1099b5 [0x41, 0x5C] (PopPre 0x1099b5) (popR64Effect 0x1099b5 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1099b5 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1099b5 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x1099b7 [0x41, 0x5D] (PopPre 0x1099b7) (popR64Effect 0x1099b7 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1099b7 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1099b7 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x1099b9 [0x41, 0x5E] (PopPre 0x1099b9) (popR64Effect 0x1099b9 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1099b9 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1099b9 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x1099bb [0x41, 0x5F] (PopPre 0x1099bb) (popR64Effect 0x1099bb 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1099bb 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1099bb 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x1099bd [0x5D] (PopPre 0x1099bd) (popR64Effect 0x1099bd 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1099bd 1 5).toInstrSpec (pop_r64_effect_step 0x1099bd 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f16 : InstrSpec 0x1099be [0xC3] (RetPre 0x1099be) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1099be).toInstrSpec (ret_effect_step 0x1099be) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10998e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109992) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109997) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10999c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099a1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099a4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099a6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099aa) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099ad) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099b4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 74), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099b5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 77), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099b7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 80), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099b9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 83), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099bb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099bd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 89) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 89), (5, 88), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099be) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f16 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 93) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 92), (5, 88), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) f16 (by decide) rfl rfl rfl (by decide)

theorem block_l109989 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109989 :=
  Rest.liftedBlock (rest_l109989 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109989 x hx)

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

theorem_by block_l109490_eval :
    program.runBlock (dialect code) ⟨.l109490, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1095b0_eval :
    program.runBlock (dialect code) ⟨.l1095b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1095c1_eval :
    program.runBlock (dialect code) ⟨.l1095c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10960c_eval :
    program.runBlock (dialect code) ⟨.l10960c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109657_eval :
    program.runBlock (dialect code) ⟨.l109657, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10971c_eval :
    program.runBlock (dialect code) ⟨.l10971c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109763_eval :
    program.runBlock (dialect code) ⟨.l109763, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1097fe_eval :
    program.runBlock (dialect code) ⟨.l1097fe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109808_eval :
    program.runBlock (dialect code) ⟨.l109808, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109810_eval :
    program.runBlock (dialect code) ⟨.l109810, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109818_eval :
    program.runBlock (dialect code) ⟨.l109818, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109824_eval :
    program.runBlock (dialect code) ⟨.l109824, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10988a_eval :
    program.runBlock (dialect code) ⟨.l10988a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1098e0_eval :
    program.runBlock (dialect code) ⟨.l1098e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1098e5_eval :
    program.runBlock (dialect code) ⟨.l1098e5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10990b_eval :
    program.runBlock (dialect code) ⟨.l10990b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109925_eval :
    program.runBlock (dialect code) ⟨.l109925, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10992a_eval :
    program.runBlock (dialect code) ⟨.l10992a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109930_eval :
    program.runBlock (dialect code) ⟨.l109930, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10993d_eval :
    program.runBlock (dialect code) ⟨.l10993d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109948_eval :
    program.runBlock (dialect code) ⟨.l109948, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109989_eval :
    program.runBlock (dialect code) ⟨.l109989, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
