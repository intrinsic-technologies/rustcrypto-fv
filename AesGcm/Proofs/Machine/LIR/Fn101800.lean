import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l101800_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x101800 bytes_l101800) [(0, 83), (1, 85), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x10184d bytes_l101800_1 b_l101800_1 := by
  have f20 : InstrSpec 0x10184d [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x10184d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10184d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10184d 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10184d 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10184d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x101852 [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x101852) (movR64R64Effect 0x101852 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101852 2 8).toInstrSpec (mov_r64_r64_effect_step 0x101852 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x101855 [0x48, 0xC1, 0xEA, 0x04] (fun s => s.RIP = 0x101855) (shrR64Effect 0x101855 4 2 4)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x101855 4 2 4).toInstrSpec (shr_r64_imm8_effect_step 0x101855 0x48 0xea 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x101859 [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101859) (leaR64Effect 0x101859 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101859 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101859 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x10185e [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10185e) (movR64R64Effect 0x10185e 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10185e 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10185e 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x101861 [0xE8, 0x1A, 0x81, 0x00, 0x00] (PushPre 0x101861 5) (callEffect (fun _ => 0x109980) 0x101866)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101861 0x109980 0x101866).toInstrSpec (call_rel32_effect_step 0x101861 0x811a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 85), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101852) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 83), (1, 85), (2, 89), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101855) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 83), (1, 85), (2, 91), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101859) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 83), (1, 85), (2, 91), (3, 72), (4, 65), (5, 5), (6, 6), (7, 93), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10185e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 83), (1, 85), (2, 91), (3, 72), (4, 65), (5, 5), (6, 95), (7, 93), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101861) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 83), (1, 85), (2, 91), (3, 72), (4, 97), (5, 5), (6, 95), (7, 93), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109980) f25 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 99) (by decide) (by decide) rfl rfl

theorem rest_l101800 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101800 bytes_l101800) (entryMap (live .l101800))
      26 0x101800 bytes_l101800 b_l101800 := by
  have f0 : InstrSpec 0x101800 [0x55] (PushPre 0x101800 1) (pushR64Effect 0x101800 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101800 1 5).toInstrSpec (push_r64_effect_step 0x101800 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101801 [0x41, 0x57] (PushPre 0x101801 2) (pushR64Effect 0x101801 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101801 2 15).toInstrSpec (push_r64_rex_effect_step 0x101801 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101803 [0x41, 0x56] (PushPre 0x101803 2) (pushR64Effect 0x101803 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101803 2 14).toInstrSpec (push_r64_rex_effect_step 0x101803 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101805 [0x41, 0x55] (PushPre 0x101805 2) (pushR64Effect 0x101805 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101805 2 13).toInstrSpec (push_r64_rex_effect_step 0x101805 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101807 [0x41, 0x54] (PushPre 0x101807 2) (pushR64Effect 0x101807 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101807 2 12).toInstrSpec (push_r64_rex_effect_step 0x101807 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101809 [0x53] (PushPre 0x101809 1) (pushR64Effect 0x101809 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101809 1 3).toInstrSpec (push_r64_effect_step 0x101809 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10180a [0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10180a) (subR64Imm32Effect 0x10180a 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10180a 4 0x88).toInstrSpec (sub_r64_imm32_effect_step 0x10180a 0x48 0xec 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101811 [0x49, 0x89, 0xCC] (fun s => s.RIP = 0x101811) (movR64R64Effect 0x101811 12 1)
      [.gpr 1] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x101811 12 1).toInstrSpec (mov_r64_r64_effect_step 0x101811 0x49 0xcc (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101814 [0x48, 0x89, 0x54, 0x24, 0x78] (StorePre 0x101814 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101814 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101814 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101814 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x101814 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101819 [0x4D, 0x89, 0xCE] (fun s => s.RIP = 0x101819) (movR64R64Effect 0x101819 14 9)
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101819 14 9).toInstrSpec (mov_r64_r64_effect_step 0x101819 0x4d 0xce (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10181c [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x10181c) (movR64R64Effect 0x10181c 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10181c 3 8).toInstrSpec (mov_r64_r64_effect_step 0x10181c 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10181f [0x48, 0x89, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10181f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10181f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10181f 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10181f 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10181f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101827 [0x4C, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x101827 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x101827 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101827 15 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x101827 15 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x101827 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10182f [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x10182f (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10182f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10182f 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10182f 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10182f 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101833 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x101833 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101833 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101833 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101833 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x101833 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101838 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x101838 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101838 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101838 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101838 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101838 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10183c [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x10183c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10183c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10183c 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10183c 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10183c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101841 [0x48, 0x8B, 0x06] (LoadPre 0x101841 (fun s => AddrMode.addr (.base 6 .none) s (0x101841 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101841 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101841 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101841 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x101844 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x101844 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101844 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101844 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101844 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101844 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x101848 [0x48, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x101848 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101848 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101848 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101848 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x101848 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101801) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101803) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101805) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101807) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101809) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10180a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101811) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101814) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101819) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10181c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10181f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101827) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10182f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101833) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101838) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10183c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101841) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101844) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 85), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101848) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 85), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10184d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l101800_1 code

theorem block_l101800 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101800 :=
  Rest.liftedBlock (rest_l101800 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101800 x hx)

theorem rest_l101866 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101866 bytes_l101866) (entryMap (live .l101866))
      3 0x101866 bytes_l101866 b_l101866 := by
  have f0 : InstrSpec 0x101866 [0x49, 0x89, 0xDD] (fun s => s.RIP = 0x101866) (movR64R64Effect 0x101866 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101866 13 3).toInstrSpec (mov_r64_r64_effect_step 0x101866 0x49 0xdd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101869 [0x49, 0x83, 0xE5, 0x0F] (fun s => s.RIP = 0x101869) (andR64Imm8Effect 0x101869 13 0xf)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x101869 13 0xf).toInstrSpec (and_r64_imm8_effect_step 0x101869 0x49 0xe5 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101869) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10186d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x10186d 4 0xcb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101866 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101866 :=
  Rest.liftedBlock (rest_l101866 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101866 x hx)

theorem rest_l101873 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101873 bytes_l101873) (entryMap (live .l101873))
      9 0x101873 bytes_l101873 b_l101873 := by
  have f0 : InstrSpec 0x101873 [0x48, 0xB8, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F] (fun s => s.RIP = 0x101873) (movR64Imm64Effect 0x101873 0 0x1ffffffffffffff0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x101873 0 0x1ffffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x101873 0x48 0xb8 (by decide) (by decide) 0x1ffffffffffffff0) pre_rip
  have f1 : InstrSpec 0x10187d [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x10187d) (andR64R64Effect 0x10187d 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10187d 0 3).toInstrSpec (and_r64_r64_effect_step 0x10187d 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101880 [0x49, 0x01, 0xC4] (fun s => s.RIP = 0x101880) (addR64R64Effect 0x101880 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101880 12 0).toInstrSpec (add_r64_r64_effect_step 0x101880 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101883 [0xBA, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101883) (movR32Imm32Effect 0x101883 5 2 0x10)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101883 5 2 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x101883 0xba (by decide) 0x10) pre_rip
  have f4 : InstrSpec 0x101888 [0x4C, 0x29, 0xEA] (fun s => s.RIP = 0x101888) (subR64R64Effect 0x101888 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101888 2 13).toInstrSpec (sub_r64_r64_effect_step 0x101888 0x4c 0xea (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10188b [0x4A, 0x8D, 0x3C, 0x2C] (fun s => s.RIP = 0x10188b) (leaR64Effect 0x10188b 7 (.sib 4 (some 13) 0 .none))
      [.gpr 4, .gpr 13] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10188b 7 (.sib 4 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10188b 0x4a (by decide) 7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10188f [0x48, 0x83, 0xC7, 0x40] (fun s => s.RIP = 0x10188f) (addR64Imm8Effect 0x10188f 7 0x40)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10188f 7 0x40).toInstrSpec (add_r64_imm8_effect_step 0x10188f 0x48 0xc7 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101893 [0x31, 0xF6] (fun s => s.RIP = 0x101893) (xorR32R32Effect 0x101893 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101893 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x101893 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x101895 [0xFF, 0x15, 0x8D, 0xF9, 0x0F, 0x00] (GoesTo (CallMemPre 0x101895 (.rip 0xff98d)) (callEffect (callMemPtr 0x101895 (.rip 0xff98d)) (0x101895 + BitVec.ofNat 64 (callMemLen (.rip 0xff98d)))) 0x103eb0) (callEffect (callMemPtr 0x101895 (.rip 0xff98d)) (0x101895 + BitVec.ofNat 64 (callMemLen (.rip 0xff98d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101895 (.rip 0xff98d)).toInstrSpec (call_m64_effect_step 0x101895 (.rip 0xff98d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10187d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101880) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101883) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101888) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10188b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10188f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101893) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101895) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l101873 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101873 :=
  Rest.liftedBlock (rest_l101873 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101873 x hx)

theorem rest_l10189b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10189b bytes_l10189b) (entryMap (live .l10189b))
      4 0x10189b bytes_l10189b b_l10189b := by
  have f0 : InstrSpec 0x10189b [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x10189b) (leaR64Effect 0x10189b 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10189b 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x10189b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1018a0 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x1018a0) (movR64R64Effect 0x1018a0 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1018a0 6 12).toInstrSpec (mov_r64_r64_effect_step 0x1018a0 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1018a3 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1018a3) (movR64R64Effect 0x1018a3 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1018a3 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1018a3 0x4c 0xea (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1018a6 [0xFF, 0x15, 0x5C, 0xF9, 0x0F, 0x00] (GoesTo (CallMemPre 0x1018a6 (.rip 0xff95c)) (callEffect (callMemPtr 0x1018a6 (.rip 0xff95c)) (0x1018a6 + BitVec.ofNat 64 (callMemLen (.rip 0xff95c)))) 0x103f00) (callEffect (callMemPtr 0x1018a6 (.rip 0xff95c)) (0x1018a6 + BitVec.ofNat 64 (callMemLen (.rip 0xff95c))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1018a6 (.rip 0xff95c)).toInstrSpec (call_m64_effect_step 0x1018a6 (.rip 0xff95c) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10189b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10189b :=
  Rest.liftedBlock (rest_l10189b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10189b x hx)

theorem rest_l1018ac_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x1018ac bytes_l1018ac) [(0, 83), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x10190a bytes_l1018ac_1 b_l1018ac_1 := by
  have f20 : InstrSpec 0x10190a [0x0F, 0xB6, 0x4C, 0x24, 0x1A] (LoadPre 0x10190a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x10190a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10190a 5 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10190a 5 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (movzx_r32_m8_effect_step 0x10190a 1 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10190f [0x88, 0x4C, 0x24, 0x15] (StorePre 0x10190f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x10190f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10190f 4 1 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10190f 4 1 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_effect_step 0x10190f 1 (by decide) (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x101913 [0x88, 0x44, 0x24, 0x1A] (StorePre 0x101913 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101913 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101913 4 0 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101913 4 0 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_effect_step 0x101913 0 (by decide) (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101917 [0x0F, 0xB6, 0x44, 0x24, 0x16] (LoadPre 0x101917 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101917 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101917 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101917 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m8_effect_step 0x101917 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10191c [0x0F, 0xB6, 0x4C, 0x24, 0x19] (LoadPre 0x10191c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x10191c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10191c 5 1 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10191c 5 1 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m8_effect_step 0x10191c 1 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x101921 [0x88, 0x4C, 0x24, 0x16] (StorePre 0x101921 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101921 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101921 4 1 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101921 4 1 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_effect_step 0x101921 1 (by decide) (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x101925 [0x88, 0x44, 0x24, 0x19] (StorePre 0x101925 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101925 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101925 4 0 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101925 4 0 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x101925 0 (by decide) (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x101929 [0x66, 0xC1, 0x44, 0x24, 0x17, 0x08] (StorePre 0x101929 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x101929 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x101929 6 16 (.sib 4 none 0 (.d8 0x17)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x101929 6 (.sib 4 none 0 (.d8 0x17)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x101929 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x10192f [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x10192f) (leaR64Effect 0x10192f 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10192f 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x10192f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x101934 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x101934) (leaR64Effect 0x101934 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101934 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101934 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x101939 [0xE8, 0x82, 0x1B, 0x00, 0x00] (PushPre 0x101939 5) (callEffect (fun _ => 0x1034c0) 0x10193e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101939 0x1034c0 0x10193e).toInstrSpec (call_rel32_effect_step 0x101939 0x1b82 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10190f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101913) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101917) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10191c) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101921) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101925) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101929) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10192f) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101934) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101939) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f30 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 100), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c0) f30 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 102) (by decide) (by decide) rfl rfl

theorem rest_l1018ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1018ac bytes_l1018ac) (entryMap (live .l1018ac))
      31 0x1018ac bytes_l1018ac b_l1018ac := by
  have f0 : InstrSpec 0x1018ac [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x1018ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1018ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1018ac 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1018ac 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1018ac 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1018b1 [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x1018b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1018b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1018b1 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1018b1 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1018b1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1018b6 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x1018b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1018b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1018b6 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1018b6 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1018b6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1018bb [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x1018bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1018bb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1018bb 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1018bb 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1018bb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1018c0 [0x0F, 0xB6, 0x4C, 0x24, 0x1F] (LoadPre 0x1018c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1018c0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1018c0 5 1 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1018c0 5 1 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_effect_step 0x1018c0 1 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1018c5 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x1018c5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1018c5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1018c5 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1018c5 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x1018c5 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1018c9 [0x88, 0x44, 0x24, 0x1F] (StorePre 0x1018c9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1018c9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1018c9 4 0 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1018c9 4 0 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x1018c9 0 (by decide) (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1018cd [0x0F, 0xB7, 0x44, 0x24, 0x11] (LoadPre 0x1018cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1018cd + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1018cd 5 0 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1018cd 5 0 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m16_effect_step 0x1018cd 0 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1018d2 [0x66, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x1018d2) (rolR16Effect 0x1018d2 4 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1018d2 4 0 8).toInstrSpec (rol_r16_imm8_effect_step 0x1018d2 0xc0 0x8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1018d6 [0x0F, 0xB7, 0x4C, 0x24, 0x1D] (LoadPre 0x1018d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1018d6 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1018d6 5 1 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x1018d6 5 1 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m16_effect_step 0x1018d6 1 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1018db [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x1018db) (rolR16Effect 0x1018db 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x1018db 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x1018db 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1018df [0x0F, 0xB7, 0x54, 0x24, 0x13] (LoadPre 0x1018df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1018df + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1018df 5 2 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1018df 5 2 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m16_effect_step 0x1018df 2 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1018e4 [0x66, 0x89, 0x4C, 0x24, 0x11] (StorePre 0x1018e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1018e4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1018e4 5 1 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1018e4 5 1 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m16_r16_effect_step 0x1018e4 1 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1018e9 [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x1018e9) (rolR16Effect 0x1018e9 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x1018e9 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x1018e9 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1018ed [0x66, 0x89, 0x44, 0x24, 0x1D] (StorePre 0x1018ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1018ed + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1018ed 5 0 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1018ed 5 0 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_m16_r16_effect_step 0x1018ed 0 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1018f2 [0x0F, 0xB7, 0x44, 0x24, 0x1B] (LoadPre 0x1018f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x1018f2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1018f2 5 0 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1018f2 5 0 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m16_effect_step 0x1018f2 0 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1018f7 [0x66, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x1018f7) (rolR16Effect 0x1018f7 4 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1018f7 4 0 8).toInstrSpec (rol_r16_imm8_effect_step 0x1018f7 0xc0 0x8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1018fb [0x66, 0x89, 0x44, 0x24, 0x13] (StorePre 0x1018fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1018fb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1018fb 5 0 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1018fb 5 0 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m16_r16_effect_step 0x1018fb 0 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101900 [0x66, 0x89, 0x54, 0x24, 0x1B] (StorePre 0x101900 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101900 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101900 5 2 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101900 5 2 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_m16_r16_effect_step 0x101900 2 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x101905 [0x0F, 0xB6, 0x44, 0x24, 0x15] (LoadPre 0x101905 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101905 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101905 5 0 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101905 5 0 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (movzx_r32_m8_effect_step 0x101905 0 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018b6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018bb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018c0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018c5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018c9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018cd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018d2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018d6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018db) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018df) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018e4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 65), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018e9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018ed) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018f2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018f7) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018fb) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101900) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101905) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10190a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1018ac_1 code

theorem block_l1018ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1018ac :=
  Rest.liftedBlock (rest_l1018ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1018ac x hx)

theorem rest_l10193e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10193e bytes_l10193e) (entryMap (live .l10193e))
      5 0x10193e bytes_l10193e b_l10193e := by
  have f0 : InstrSpec 0x10193e [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x10193e) (movR64R64Effect 0x10193e 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10193e 2 15).toInstrSpec (mov_r64_r64_effect_step 0x10193e 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101941 [0x48, 0xC1, 0xEA, 0x04] (fun s => s.RIP = 0x101941) (shrR64Effect 0x101941 4 2 4)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x101941 4 2 4).toInstrSpec (shr_r64_imm8_effect_step 0x101941 0x48 0xea 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101945 [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101945) (leaR64Effect 0x101945 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101945 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101945 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10194a [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10194a) (movR64R64Effect 0x10194a 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10194a 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10194a 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10194d [0xE8, 0x2E, 0x80, 0x00, 0x00] (PushPre 0x10194d 5) (callEffect (fun _ => 0x109980) 0x101952)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10194d 0x109980 0x101952).toInstrSpec (call_rel32_effect_step 0x10194d 0x802e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101941) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101945) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10194a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10194d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109980) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10193e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10193e :=
  Rest.liftedBlock (rest_l10193e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10193e x hx)

theorem rest_l101952 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101952 bytes_l101952) (entryMap (live .l101952))
      3 0x101952 bytes_l101952 b_l101952 := by
  have f0 : InstrSpec 0x101952 [0x4D, 0x89, 0xFC] (fun s => s.RIP = 0x101952) (movR64R64Effect 0x101952 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x101952 12 15).toInstrSpec (mov_r64_r64_effect_step 0x101952 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101955 [0x49, 0x83, 0xE4, 0x0F] (fun s => s.RIP = 0x101955) (andR64Imm8Effect 0x101955 12 0xf)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x101955 12 0xf).toInstrSpec (and_r64_imm8_effect_step 0x101955 0x49 0xe4 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101955) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101959) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x101959 4 0xcb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101952 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101952 :=
  Rest.liftedBlock (rest_l101952 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101952 x hx)

theorem rest_l10195f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10195f bytes_l10195f) (entryMap (live .l10195f))
      9 0x10195f bytes_l10195f b_l10195f := by
  have f0 : InstrSpec 0x10195f [0x48, 0xB8, 0xF0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10195f) (movR64Imm64Effect 0x10195f 0 0xffffffff0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10195f 0 0xffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x10195f 0x48 0xb8 (by decide) (by decide) 0xffffffff0) pre_rip
  have f1 : InstrSpec 0x101969 [0x4C, 0x21, 0xF8] (fun s => s.RIP = 0x101969) (andR64R64Effect 0x101969 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101969 0 15).toInstrSpec (and_r64_r64_effect_step 0x101969 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10196c [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x10196c) (addR64R64Effect 0x10196c 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10196c 14 0).toInstrSpec (add_r64_r64_effect_step 0x10196c 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10196f [0xBA, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10196f) (movR32Imm32Effect 0x10196f 5 2 0x10)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10196f 5 2 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x10196f 0xba (by decide) 0x10) pre_rip
  have f4 : InstrSpec 0x101974 [0x4C, 0x29, 0xE2] (fun s => s.RIP = 0x101974) (subR64R64Effect 0x101974 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101974 2 12).toInstrSpec (sub_r64_r64_effect_step 0x101974 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101977 [0x4A, 0x8D, 0x3C, 0x24] (fun s => s.RIP = 0x101977) (leaR64Effect 0x101977 7 (.sib 4 (some 12) 0 .none))
      [.gpr 4, .gpr 12] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101977 7 (.sib 4 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x101977 0x4a (by decide) 7 (.sib 4 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10197b [0x48, 0x83, 0xC7, 0x40] (fun s => s.RIP = 0x10197b) (addR64Imm8Effect 0x10197b 7 0x40)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10197b 7 0x40).toInstrSpec (add_r64_imm8_effect_step 0x10197b 0x48 0xc7 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10197f [0x31, 0xF6] (fun s => s.RIP = 0x10197f) (xorR32R32Effect 0x10197f 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10197f 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10197f 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x101981 [0xFF, 0x15, 0xA1, 0xF8, 0x0F, 0x00] (GoesTo (CallMemPre 0x101981 (.rip 0xff8a1)) (callEffect (callMemPtr 0x101981 (.rip 0xff8a1)) (0x101981 + BitVec.ofNat 64 (callMemLen (.rip 0xff8a1)))) 0x103eb0) (callEffect (callMemPtr 0x101981 (.rip 0xff8a1)) (0x101981 + BitVec.ofNat 64 (callMemLen (.rip 0xff8a1))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101981 (.rip 0xff8a1)).toInstrSpec (call_m64_effect_step 0x101981 (.rip 0xff8a1) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101969) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10196c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10196f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101974) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101977) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10197b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10197f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101981) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l10195f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10195f :=
  Rest.liftedBlock (rest_l10195f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10195f x hx)

theorem rest_l101987 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101987 bytes_l101987) (entryMap (live .l101987))
      4 0x101987 bytes_l101987 b_l101987 := by
  have f0 : InstrSpec 0x101987 [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x101987) (leaR64Effect 0x101987 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101987 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x101987 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10198c [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10198c) (movR64R64Effect 0x10198c 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10198c 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10198c 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10198f [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x10198f) (movR64R64Effect 0x10198f 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10198f 2 12).toInstrSpec (mov_r64_r64_effect_step 0x10198f 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101992 [0xFF, 0x15, 0x70, 0xF8, 0x0F, 0x00] (GoesTo (CallMemPre 0x101992 (.rip 0xff870)) (callEffect (callMemPtr 0x101992 (.rip 0xff870)) (0x101992 + BitVec.ofNat 64 (callMemLen (.rip 0xff870)))) 0x103f00) (callEffect (callMemPtr 0x101992 (.rip 0xff870)) (0x101992 + BitVec.ofNat 64 (callMemLen (.rip 0xff870))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101992 (.rip 0xff870)).toInstrSpec (call_m64_effect_step 0x101992 (.rip 0xff870) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10198c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10198f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101992) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101987 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101987 :=
  Rest.liftedBlock (rest_l101987 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101987 x hx)

theorem rest_l101998_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x101998 bytes_l101998) [(0, 83), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x1019f6 bytes_l101998_1 b_l101998_1 := by
  have f20 : InstrSpec 0x1019f6 [0x0F, 0xB6, 0x4C, 0x24, 0x1A] (LoadPre 0x1019f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1019f6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1019f6 5 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1019f6 5 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (movzx_r32_m8_effect_step 0x1019f6 1 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1019fb [0x88, 0x4C, 0x24, 0x15] (StorePre 0x1019fb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x1019fb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1019fb 4 1 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1019fb 4 1 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_effect_step 0x1019fb 1 (by decide) (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1019ff [0x88, 0x44, 0x24, 0x1A] (StorePre 0x1019ff 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1019ff + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1019ff 4 0 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1019ff 4 0 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_effect_step 0x1019ff 0 (by decide) (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101a03 [0x0F, 0xB6, 0x44, 0x24, 0x16] (LoadPre 0x101a03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101a03 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101a03 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101a03 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m8_effect_step 0x101a03 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x101a08 [0x0F, 0xB6, 0x4C, 0x24, 0x19] (LoadPre 0x101a08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101a08 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101a08 5 1 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101a08 5 1 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m8_effect_step 0x101a08 1 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x101a0d [0x88, 0x4C, 0x24, 0x16] (StorePre 0x101a0d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101a0d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a0d 4 1 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a0d 4 1 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_effect_step 0x101a0d 1 (by decide) (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x101a11 [0x88, 0x44, 0x24, 0x19] (StorePre 0x101a11 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101a11 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a11 4 0 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a11 4 0 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x101a11 0 (by decide) (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x101a15 [0x66, 0xC1, 0x44, 0x24, 0x17, 0x08] (StorePre 0x101a15 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x101a15 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x101a15 6 16 (.sib 4 none 0 (.d8 0x17)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x101a15 6 (.sib 4 none 0 (.d8 0x17)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x101a15 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x101a1b [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101a1b) (leaR64Effect 0x101a1b 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101a1b 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101a1b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x101a20 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x101a20) (leaR64Effect 0x101a20 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101a20 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101a20 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x101a25 [0xE8, 0x96, 0x1A, 0x00, 0x00] (PushPre 0x101a25 5) (callEffect (fun _ => 0x1034c0) 0x101a2a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101a25 0x1034c0 0x101a2a).toInstrSpec (call_rel32_effect_step 0x101a25 0x1a96 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019fb) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019ff) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a03) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a08) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a0d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a11) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a15) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a1b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a20) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a25) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f30 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 100), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c0) f30 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 102) (by decide) (by decide) rfl rfl

theorem rest_l101998 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101998 bytes_l101998) (entryMap (live .l101998))
      31 0x101998 bytes_l101998 b_l101998 := by
  have f0 : InstrSpec 0x101998 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x101998 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101998 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101998 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101998 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x101998 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10199d [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x10199d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10199d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10199d 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10199d 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10199d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1019a2 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x1019a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1019a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1019a2 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1019a2 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1019a2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1019a7 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x1019a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1019a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1019a7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1019a7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1019a7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1019ac [0x0F, 0xB6, 0x4C, 0x24, 0x1F] (LoadPre 0x1019ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1019ac + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1019ac 5 1 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1019ac 5 1 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_effect_step 0x1019ac 1 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1019b1 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x1019b1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1019b1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1019b1 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1019b1 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x1019b1 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1019b5 [0x88, 0x44, 0x24, 0x1F] (StorePre 0x1019b5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1019b5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1019b5 4 0 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1019b5 4 0 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x1019b5 0 (by decide) (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1019b9 [0x0F, 0xB7, 0x44, 0x24, 0x11] (LoadPre 0x1019b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1019b9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1019b9 5 0 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1019b9 5 0 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m16_effect_step 0x1019b9 0 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1019be [0x66, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x1019be) (rolR16Effect 0x1019be 4 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1019be 4 0 8).toInstrSpec (rol_r16_imm8_effect_step 0x1019be 0xc0 0x8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1019c2 [0x0F, 0xB7, 0x4C, 0x24, 0x1D] (LoadPre 0x1019c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1019c2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1019c2 5 1 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x1019c2 5 1 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m16_effect_step 0x1019c2 1 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1019c7 [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x1019c7) (rolR16Effect 0x1019c7 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x1019c7 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x1019c7 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1019cb [0x0F, 0xB7, 0x54, 0x24, 0x13] (LoadPre 0x1019cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1019cb + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1019cb 5 2 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1019cb 5 2 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m16_effect_step 0x1019cb 2 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1019d0 [0x66, 0x89, 0x4C, 0x24, 0x11] (StorePre 0x1019d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1019d0 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1019d0 5 1 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1019d0 5 1 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m16_r16_effect_step 0x1019d0 1 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1019d5 [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x1019d5) (rolR16Effect 0x1019d5 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x1019d5 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x1019d5 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1019d9 [0x66, 0x89, 0x44, 0x24, 0x1D] (StorePre 0x1019d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1019d9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1019d9 5 0 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1019d9 5 0 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_m16_r16_effect_step 0x1019d9 0 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1019de [0x0F, 0xB7, 0x44, 0x24, 0x1B] (LoadPre 0x1019de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x1019de + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1019de 5 0 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1019de 5 0 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m16_effect_step 0x1019de 0 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1019e3 [0x66, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x1019e3) (rolR16Effect 0x1019e3 4 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1019e3 4 0 8).toInstrSpec (rol_r16_imm8_effect_step 0x1019e3 0xc0 0x8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1019e7 [0x66, 0x89, 0x44, 0x24, 0x13] (StorePre 0x1019e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1019e7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1019e7 5 0 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1019e7 5 0 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m16_r16_effect_step 0x1019e7 0 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1019ec [0x66, 0x89, 0x54, 0x24, 0x1B] (StorePre 0x1019ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x1019ec + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1019ec 5 2 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1019ec 5 2 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_m16_r16_effect_step 0x1019ec 2 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1019f1 [0x0F, 0xB6, 0x44, 0x24, 0x15] (LoadPre 0x1019f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x1019f1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1019f1 5 0 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1019f1 5 0 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (movzx_r32_m8_effect_step 0x1019f1 0 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10199d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019a2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019a7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019ac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019b1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019b5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019b9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019be) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019c2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019c7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019cb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019d0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 65), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019d5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019d9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019de) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019e3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019e7) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019ec) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019f1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019f6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101998_1 code

theorem block_l101998 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101998 :=
  Rest.liftedBlock (rest_l101998 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101998 x hx)

theorem rest_l101a2a_2 [Bindings] (code : CodeMap) :
    Rest (n := 118) code lifted (codeRange 0x101a2a bytes_l101a2a) [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x101ac1 bytes_l101a2a_2 b_l101a2a_2 := by
  have f40 : InstrSpec 0x101ac1 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x101ac1) (leaR64Effect 0x101ac1 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101ac1 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101ac1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x101ac6 [0xE8, 0xF5, 0x19, 0x00, 0x00] (PushPre 0x101ac6 5) (callEffect (fun _ => 0x1034c0) 0x101acb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101ac6 0x1034c0 0x101acb).toInstrSpec (call_rel32_effect_step 0x101ac6 0x19f5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (6, 118), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ac6) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 120), (5, 5), (6, 118), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c0) f41 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 122) (by decide) (by decide) rfl rfl

theorem rest_l101a2a_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x101a2a bytes_l101a2a) [(0, 85), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x101a6f bytes_l101a2a_1 b_l101a2a_1 := by
  have f20 : InstrSpec 0x101a6f [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x101a6f) (movR64R64Effect 0x101a6f 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x101a6f 1 15).toInstrSpec (mov_r64_r64_effect_step 0x101a6f 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x101a72 [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x101a72) (shrR64Effect 0x101a72 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101a72 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x101a72 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x101a76 [0x88, 0x4C, 0x24, 0x13] (StorePre 0x101a76 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101a76 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a76 4 1 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a76 4 1 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m8_r8_effect_step 0x101a76 1 (by decide) (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101a7a [0x88, 0x44, 0x24, 0x1C] (StorePre 0x101a7a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x101a7a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a7a 4 0 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a7a 4 0 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m8_r8_effect_step 0x101a7a 0 (by decide) (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x101a7e [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x101a7e) (movR64R64Effect 0x101a7e 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101a7e 0 3).toInstrSpec (mov_r64_r64_effect_step 0x101a7e 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x101a81 [0x48, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x101a81) (shrR64Effect 0x101a81 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101a81 4 0 32).toInstrSpec (shr_r64_imm8_effect_step 0x101a81 0x48 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x101a85 [0x41, 0xC1, 0xEF, 0x18] (fun s => s.RIP = 0x101a85) (shrR32Effect 0x101a85 4 15 24)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR32Effect_footprint 0x101a85 4 15 24).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101a85 0x41 0xef 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x101a89 [0x44, 0x88, 0x7C, 0x24, 0x14] (StorePre 0x101a89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x101a89 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x101a89 5 15 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a89 5 15 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101a89 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x101a8e [0x88, 0x44, 0x24, 0x1B] (StorePre 0x101a8e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101a8e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a8e 4 0 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a8e 4 0 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_m8_r8_effect_step 0x101a8e 0 (by decide) (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x101a92 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x101a92) (movR64R64Effect 0x101a92 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101a92 0 3).toInstrSpec (mov_r64_r64_effect_step 0x101a92 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x101a95 [0x48, 0xC1, 0xE8, 0x28] (fun s => s.RIP = 0x101a95) (shrR64Effect 0x101a95 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101a95 4 0 40).toInstrSpec (shr_r64_imm8_effect_step 0x101a95 0x48 0xe8 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x101a99 [0xC6, 0x44, 0x24, 0x15, 0x00] (StorePre 0x101a99 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101a99 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x101a99 (.sib 4 none 0 (.d8 0x15)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101a99 (.sib 4 none 0 (.d8 0x15)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101a99 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x101a9e [0x88, 0x44, 0x24, 0x1A] (StorePre 0x101a9e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101a9e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a9e 4 0 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a9e 4 0 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_effect_step 0x101a9e 0 (by decide) (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x101aa2 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x101aa2) (movR64R64Effect 0x101aa2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101aa2 0 3).toInstrSpec (mov_r64_r64_effect_step 0x101aa2 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x101aa5 [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x101aa5) (shrR64Effect 0x101aa5 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101aa5 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x101aa5 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x101aa9 [0x66, 0xC7, 0x44, 0x24, 0x16, 0x00, 0x00] (StorePre 0x101aa9 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101aa9 + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x101aa9 (.sib 4 none 0 (.d8 0x16)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x101aa9 (.sib 4 none 0 (.d8 0x16)) 0x0).toInstrSpec (mov_m16_imm16_effect_step 0x101aa9 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x101ab0 [0x88, 0x44, 0x24, 0x19] (StorePre 0x101ab0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101ab0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ab0 4 0 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ab0 4 0 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x101ab0 0 (by decide) (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x101ab4 [0x48, 0xC1, 0xEB, 0x38] (fun s => s.RIP = 0x101ab4) (shrR64Effect 0x101ab4 4 3 56)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x101ab4 4 3 56).toInstrSpec (shr_r64_imm8_effect_step 0x101ab4 0x48 0xeb 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x101ab8 [0x88, 0x5C, 0x24, 0x18] (StorePre 0x101ab8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101ab8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ab8 4 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ab8 4 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_effect_step 0x101ab8 3 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x101abc [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101abc) (leaR64Effect 0x101abc 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101abc 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101abc 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (1, 87), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a72) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 85), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a76) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 85), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a7a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 85), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a7e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a81) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a85) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a89) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a8e) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a92) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a95) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a99) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 103), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a9e) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 103), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aa2) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 107), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aa5) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aa9) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 109), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab0) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 109), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab4) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f37 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab8) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101abc) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ac1) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101a2a_2 code

theorem rest_l101a2a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101a2a bytes_l101a2a) (entryMap (live .l101a2a))
      42 0x101a2a bytes_l101a2a b_l101a2a := by
  have f0 : InstrSpec 0x101a2a [0x48, 0xC1, 0xE3, 0x03] (fun s => s.RIP = 0x101a2a) (shlR64Effect 0x101a2a 4 3 3)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x101a2a 4 3 3).toInstrSpec (shl_r64_imm8_effect_step 0x101a2a 0x48 0xe3 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101a2e [0x49, 0xC1, 0xE7, 0x03] (fun s => s.RIP = 0x101a2e) (shlR64Effect 0x101a2e 4 15 3)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64Effect_footprint 0x101a2e 4 15 3).toInstrSpec (shl_r64_imm8_effect_step 0x101a2e 0x49 0xe7 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101a32 [0x48, 0x0F, 0xCB] (fun s => s.RIP = 0x101a32) (bswapR64Effect 0x101a32 3 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (bswapR64Effect_footprint 0x101a32 3 3).toInstrSpec (bswap_r64_effect_step 0x101a32 0x48 (by decide) 0xcb (by decide)) pre_rip
  have f3 : InstrSpec 0x101a35 [0x49, 0x0F, 0xCF] (fun s => s.RIP = 0x101a35) (bswapR64Effect 0x101a35 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (bswapR64Effect_footprint 0x101a35 3 15).toInstrSpec (bswap_r64_effect_step 0x101a35 0x49 (by decide) 0xcf (by decide)) pre_rip
  have f4 : InstrSpec 0x101a38 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x101a38) (movR64R64Effect 0x101a38 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101a38 0 15).toInstrSpec (mov_r64_r64_effect_step 0x101a38 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101a3b [0x48, 0xC1, 0xE8, 0x38] (fun s => s.RIP = 0x101a3b) (shrR64Effect 0x101a3b 4 0 56)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101a3b 4 0 56).toInstrSpec (shr_r64_imm8_effect_step 0x101a3b 0x48 0xe8 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101a3f [0x88, 0x44, 0x24, 0x10] (StorePre 0x101a3f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101a3f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a3f 4 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a3f 4 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x101a3f 0 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101a43 [0x88, 0x5C, 0x24, 0x1F] (StorePre 0x101a43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101a43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a43 4 3 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a43 4 3 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x101a43 3 (by decide) (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101a47 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x101a47) (movR64R64Effect 0x101a47 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101a47 0 15).toInstrSpec (mov_r64_r64_effect_step 0x101a47 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101a4a [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x101a4a) (shrR64Effect 0x101a4a 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101a4a 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x101a4a 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101a4e [0x88, 0x44, 0x24, 0x11] (StorePre 0x101a4e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101a4e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a4e 4 0 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a4e 4 0 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m8_r8_effect_step 0x101a4e 0 (by decide) (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x101a52 [0x88, 0x7C, 0x24, 0x1E] (StorePre 0x101a52 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x101a52 + BitVec.ofNat 64 4)) 1) (movM8R8NoRexEffect 0x101a52 4 7 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x101a52 4 7 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (mov_m8_r8_norex_effect_step 0x101a52 7 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101a56 [0x89, 0xD8] (fun s => s.RIP = 0x101a56) (movR32R32Effect 0x101a56 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101a56 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x101a56 0xd8 (by decide)) pre_rip
  have f13 : InstrSpec 0x101a58 [0xC1, 0xE8, 0x10] (fun s => s.RIP = 0x101a58) (shrR32Effect 0x101a58 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x101a58 3 0 16).toInstrSpec (shr_r32_imm8_effect_step 0x101a58 0xe8 0x10 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101a5b [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x101a5b) (movR64R64Effect 0x101a5b 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x101a5b 1 15).toInstrSpec (mov_r64_r64_effect_step 0x101a5b 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101a5e [0x48, 0xC1, 0xE9, 0x28] (fun s => s.RIP = 0x101a5e) (shrR64Effect 0x101a5e 4 1 40)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101a5e 4 1 40).toInstrSpec (shr_r64_imm8_effect_step 0x101a5e 0x48 0xe9 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101a62 [0x88, 0x4C, 0x24, 0x12] (StorePre 0x101a62 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x101a62 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a62 4 1 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a62 4 1 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m8_r8_effect_step 0x101a62 1 (by decide) (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101a66 [0x88, 0x44, 0x24, 0x1D] (StorePre 0x101a66 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101a66 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101a66 4 0 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101a66 4 0 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_m8_r8_effect_step 0x101a66 0 (by decide) (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101a6a [0x89, 0xD8] (fun s => s.RIP = 0x101a6a) (movR32R32Effect 0x101a6a 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101a6a 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x101a6a 0xd8 (by decide)) pre_rip
  have f19 : InstrSpec 0x101a6c [0xC1, 0xE8, 0x18] (fun s => s.RIP = 0x101a6c) (shrR32Effect 0x101a6c 3 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x101a6c 3 0 24).toInstrSpec (shr_r32_imm8_effect_step 0x101a6c 0xe8 0x18 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a2e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a32) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a38) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a3b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a3f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a43) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 63), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a47) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a4a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a4e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a52) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 69), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a56) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a58) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a5b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 77), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a5e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 75), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a62) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 75), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a66) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 75), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a6a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a6c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a6f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101a2a_1 code

theorem block_l101a2a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101a2a :=
  Rest.liftedBlock (rest_l101a2a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101a2a x hx)

theorem rest_l101acb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101acb bytes_l101acb) (entryMap (live .l101acb))
      11 0x101acb bytes_l101acb b_l101acb := by
  have f0 : InstrSpec 0x101acb [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x101acb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101acb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101acb 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101acb 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x101acb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101ad0 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x101ad0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101ad0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ad0 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101ad0 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x101ad0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101ad5 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x101ad5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101ad5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ad5 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101ad5 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x101ad5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101ada [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x101ada 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101ada + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ada 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101ada 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101ada 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101adf [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x101adf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101adf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101adf 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101adf 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x101adf 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101ae4 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x101ae4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101ae4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ae4 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101ae4 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x101ae4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101ae9 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x101ae9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101ae9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ae9 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101ae9 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101ae9 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101aee [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x101aee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101aee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101aee 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101aee 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101aee 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101af3 [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x101af3) (leaR64Effect 0x101af3 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101af3 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x101af3 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101af8 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x101af8) (leaR64Effect 0x101af8 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101af8 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101af8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101afd [0xE8, 0x9E, 0x19, 0x00, 0x00] (PushPre 0x101afd 5) (callEffect (fun _ => 0x1034a0) 0x101b02)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101afd 0x1034a0 0x101b02).toInstrSpec (call_rel32_effect_step 0x101afd 0x199e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ad0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ad5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ada) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101adf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aee) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101afd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034a0) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l101acb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101acb :=
  Rest.liftedBlock (rest_l101acb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101acb x hx)

theorem rest_l101b02_3 [Bindings] (code : CodeMap) :
    Rest (n := 154) code lifted (codeRange 0x101b02 bytes_l101b02) [(0, 127), (1, 125), (2, 145), (3, 151), (4, 152), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x101c08 bytes_l101b02_3 b_l101b02_3 := by
  have f60 : InstrSpec 0x101c08 [0x41, 0x5C] (PopPre 0x101c08) (popR64Effect 0x101c08 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c08 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101c08 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f61 : InstrSpec 0x101c0a [0x41, 0x5D] (PopPre 0x101c0a) (popR64Effect 0x101c0a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c0a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101c0a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f62 : InstrSpec 0x101c0c [0x41, 0x5E] (PopPre 0x101c0c) (popR64Effect 0x101c0c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c0c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101c0c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f63 : InstrSpec 0x101c0e [0x41, 0x5F] (PopPre 0x101c0e) (popR64Effect 0x101c0e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c0e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101c0e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f64 : InstrSpec 0x101c10 [0x5D] (PopPre 0x101c10) (popR64Effect 0x101c10 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c10 1 5).toInstrSpec (pop_r64_effect_step 0x101c10 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f65 : InstrSpec 0x101c11 [0xC3] (RetPre 0x101c11) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101c11).toInstrSpec (ret_effect_step 0x101c11) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f60 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 155) f60 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 156) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 155), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c0a) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f61 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 158) f61 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 159) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 158), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c0c) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f62 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 161) f62 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 162) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 161), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c0e) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f63 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 164) f63 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 165) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 164), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c10) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f64 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 167) f64 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 168) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 167), (5, 166), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c11) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f65 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 170) f65 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 171) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 170), (5, 166), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) f65 (by decide) rfl rfl rfl (by decide)

theorem rest_l101b02_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x101b02 bytes_l101b02) [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]
      26 0x101bbb bytes_l101b02_2 b_l101b02_2 := by
  have f40 : InstrSpec 0x101bbb [0x44, 0x88, 0x00] (StorePre 0x101bbb 3 (fun s => AddrMode.addr (.base 0 .none) s (0x101bbb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bbb 3 8 (.base 0 .none))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bbb 3 8 (.base 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bbb 0x44 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x101bbe [0x44, 0x88, 0x50, 0x01] (StorePre 0x101bbe 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x101bbe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bbe 4 10 (.base 0 (.d8 0x1)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bbe 4 10 (.base 0 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bbe 0x44 (by decide) 2 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x101bc2 [0x44, 0x88, 0x58, 0x02] (StorePre 0x101bc2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x101bc2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bc2 4 11 (.base 0 (.d8 0x2)))
      [.gpr 11, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bc2 4 11 (.base 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bc2 0x44 (by decide) 3 (.base 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x101bc6 [0x44, 0x88, 0x78, 0x03] (StorePre 0x101bc6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x101bc6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bc6 4 15 (.base 0 (.d8 0x3)))
      [.gpr 15, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bc6 4 15 (.base 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bc6 0x44 (by decide) 7 (.base 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x101bca [0x44, 0x88, 0x60, 0x04] (StorePre 0x101bca 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101bca + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bca 4 12 (.base 0 (.d8 0x4)))
      [.gpr 12, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bca 4 12 (.base 0 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bca 0x44 (by decide) 4 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x101bce [0x44, 0x88, 0x68, 0x05] (StorePre 0x101bce 4 (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x101bce + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bce 4 13 (.base 0 (.d8 0x5)))
      [.gpr 13, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bce 4 13 (.base 0 (.d8 0x5))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bce 0x44 (by decide) 5 (.base 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x101bd2 [0x40, 0x88, 0x68, 0x06] (StorePre 0x101bd2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x101bd2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bd2 4 5 (.base 0 (.d8 0x6)))
      [.gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bd2 4 5 (.base 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bd2 0x40 (by decide) 5 (.base 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x101bd6 [0x44, 0x88, 0x70, 0x07] (StorePre 0x101bd6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x101bd6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bd6 4 14 (.base 0 (.d8 0x7)))
      [.gpr 14, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bd6 4 14 (.base 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bd6 0x44 (by decide) 6 (.base 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x101bda [0x40, 0x88, 0x70, 0x08] (StorePre 0x101bda 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101bda + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bda 4 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bda 4 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bda 0x40 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x101bde [0x88, 0x58, 0x09] (StorePre 0x101bde 3 (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x101bde + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bde 3 3 (.base 0 (.d8 0x9)))
      [.gpr 3, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bde 3 3 (.base 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x101bde 3 (by decide) (.base 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x101be1 [0x44, 0x88, 0x48, 0x0A] (StorePre 0x101be1 4 (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x101be1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101be1 4 9 (.base 0 (.d8 0xa)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101be1 4 9 (.base 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101be1 0x44 (by decide) 1 (.base 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x101be5 [0x40, 0x88, 0x78, 0x0B] (StorePre 0x101be5 4 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x101be5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101be5 4 7 (.base 0 (.d8 0xb)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101be5 4 7 (.base 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101be5 0x40 (by decide) 7 (.base 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x101be9 [0x0F, 0xB6, 0x74, 0x24, 0x3E] (LoadPre 0x101be9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x101be9 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101be9 5 6 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x101be9 5 6 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (movzx_r32_m8_effect_step 0x101be9 6 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x101bee [0x40, 0x88, 0x70, 0x0C] (StorePre 0x101bee 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x101bee + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101bee 4 6 (.base 0 (.d8 0xc)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bee 4 6 (.base 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101bee 0x40 (by decide) 6 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x101bf2 [0x88, 0x50, 0x0D] (StorePre 0x101bf2 3 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x101bf2 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bf2 3 2 (.base 0 (.d8 0xd)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bf2 3 2 (.base 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_effect_step 0x101bf2 2 (by decide) (.base 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x101bf5 [0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x101bf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101bf5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101bf5 5 2 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x101bf5 5 2 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x101bf5 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f56 : InstrSpec 0x101bfa [0x88, 0x50, 0x0E] (StorePre 0x101bfa 3 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x101bfa + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bfa 3 2 (.base 0 (.d8 0xe)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bfa 3 2 (.base 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_effect_step 0x101bfa 2 (by decide) (.base 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x101bfd [0x88, 0x48, 0x0F] (StorePre 0x101bfd 3 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x101bfd + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101bfd 3 1 (.base 0 (.d8 0xf)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101bfd 3 1 (.base 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x101bfd 1 (by decide) (.base 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x101c00 [0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101c00) (addR64Imm32Effect 0x101c00 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101c00 4 0x88).toInstrSpec (add_r64_imm32_effect_step 0x101c00 0x48 0xc4 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x101c07 [0x5B] (PopPre 0x101c07) (popR64Effect 0x101c07 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c07 1 3).toInstrSpec (pop_r64_effect_step 0x101c07 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 129) (RestInside.exec (n := 129) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bbe) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bc2) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bc6) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.exec (n := 132) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bca) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bce) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.exec (n := 134) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bd2) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bd6) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bda) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bde) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101be1) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101be5) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101be9) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bee) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bf2) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bf5) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f55 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bfa) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bfd) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c00) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f58 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 107), (4, 149), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c07) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f59 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 152) f59 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 153) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 152), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c08) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101b02_3 code

theorem rest_l101b02_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x101b02 bytes_l101b02) [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      46 0x101b6a bytes_l101b02_1 b_l101b02_1 := by
  have f20 : InstrSpec 0x101b6a [0x44, 0x32, 0x50, 0x01] (LoadPre 0x101b6a (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x101b6a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b6a 4 10 (.base 0 (.d8 0x1)))
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b6a 4 10 (.base 0 (.d8 0x1))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b6a 0x44 (by decide) 2 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x101b6e [0x44, 0x32, 0x58, 0x02] (LoadPre 0x101b6e (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x101b6e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b6e 4 11 (.base 0 (.d8 0x2)))
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b6e 4 11 (.base 0 (.d8 0x2))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b6e 0x44 (by decide) 3 (.base 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x101b72 [0x44, 0x32, 0x78, 0x03] (LoadPre 0x101b72 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x101b72 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b72 4 15 (.base 0 (.d8 0x3)))
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b72 4 15 (.base 0 (.d8 0x3))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b72 0x44 (by decide) 7 (.base 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x101b76 [0x44, 0x32, 0x60, 0x04] (LoadPre 0x101b76 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101b76 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b76 4 12 (.base 0 (.d8 0x4)))
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b76 4 12 (.base 0 (.d8 0x4))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b76 0x44 (by decide) 4 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x101b7a [0x44, 0x32, 0x68, 0x05] (LoadPre 0x101b7a (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x101b7a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b7a 4 13 (.base 0 (.d8 0x5)))
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b7a 4 13 (.base 0 (.d8 0x5))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b7a 0x44 (by decide) 5 (.base 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x101b7e [0x40, 0x32, 0x68, 0x06] (LoadPre 0x101b7e (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x101b7e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b7e 4 5 (.base 0 (.d8 0x6)))
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b7e 4 5 (.base 0 (.d8 0x6))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b7e 0x40 (by decide) 5 (.base 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x101b82 [0x44, 0x32, 0x70, 0x07] (LoadPre 0x101b82 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x101b82 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b82 4 14 (.base 0 (.d8 0x7)))
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b82 4 14 (.base 0 (.d8 0x7))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b82 0x44 (by decide) 6 (.base 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x101b86 [0x40, 0x32, 0x70, 0x08] (LoadPre 0x101b86 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101b86 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b86 4 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b86 4 6 (.base 0 (.d8 0x8))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b86 0x40 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x101b8a [0x32, 0x58, 0x09] (LoadPre 0x101b8a (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x101b8a + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101b8a 3 3 (.base 0 (.d8 0x9)))
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b8a 3 3 (.base 0 (.d8 0x9))).toInstrSpec (xor_r8_m8_effect_step 0x101b8a 3 (by decide) (.base 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x101b8d [0x44, 0x32, 0x48, 0x0A] (LoadPre 0x101b8d (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x101b8d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b8d 4 9 (.base 0 (.d8 0xa)))
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b8d 4 9 (.base 0 (.d8 0xa))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b8d 0x44 (by decide) 1 (.base 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x101b91 [0x40, 0x32, 0x78, 0x0B] (LoadPre 0x101b91 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x101b91 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101b91 4 7 (.base 0 (.d8 0xb)))
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b91 4 7 (.base 0 (.d8 0xb))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b91 0x40 (by decide) 7 (.base 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x101b95 [0x32, 0x50, 0x0C] (LoadPre 0x101b95 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x101b95 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101b95 3 2 (.base 0 (.d8 0xc)))
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b95 3 2 (.base 0 (.d8 0xc))).toInstrSpec (xor_r8_m8_effect_step 0x101b95 2 (by decide) (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x101b98 [0x88, 0x54, 0x24, 0x3E] (StorePre 0x101b98 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x101b98 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101b98 4 2 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101b98 4 2 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (mov_m8_r8_effect_step 0x101b98 2 (by decide) (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x101b9c [0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x101b9c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101b9c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b9c 5 2 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x101b9c 5 2 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x101b9c 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x101ba1 [0x32, 0x50, 0x0D] (LoadPre 0x101ba1 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x101ba1 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101ba1 3 2 (.base 0 (.d8 0xd)))
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101ba1 3 2 (.base 0 (.d8 0xd))).toInstrSpec (xor_r8_m8_effect_step 0x101ba1 2 (by decide) (.base 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x101ba4 [0x32, 0x48, 0x0E] (LoadPre 0x101ba4 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x101ba4 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101ba4 3 1 (.base 0 (.d8 0xe)))
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101ba4 3 1 (.base 0 (.d8 0xe))).toInstrSpec (xor_r8_m8_effect_step 0x101ba4 1 (by decide) (.base 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x101ba7 [0x88, 0x4C, 0x24, 0x0F] (StorePre 0x101ba7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101ba7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ba7 4 1 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ba7 4 1 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x101ba7 1 (by decide) (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x101bab [0x0F, 0xB6, 0x4C, 0x24, 0x3F] (LoadPre 0x101bab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x101bab + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101bab 5 1 (.sib 4 none 0 (.d8 0x3f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101bab 5 1 (.sib 4 none 0 (.d8 0x3f))).toInstrSpec (movzx_r32_m8_effect_step 0x101bab 1 (.sib 4 none 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x101bb0 [0x32, 0x48, 0x0F] (LoadPre 0x101bb0 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x101bb0 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101bb0 3 1 (.base 0 (.d8 0xf)))
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101bb0 3 1 (.base 0 (.d8 0xf))).toInstrSpec (xor_r8_m8_effect_step 0x101bb0 1 (by decide) (.base 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x101bb3 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x101bb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101bb3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101bb3 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101bb3 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x101bb3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b6e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b72) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 73), (13, 77), (14, 85), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b76) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 77), (14, 85), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b7a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 85), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b7e) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 101), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 85), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b82) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 101), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b86) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 101), (6, 105), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b8a) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 107), (4, 4), (5, 101), (6, 105), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b8d) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 107), (4, 4), (5, 101), (6, 105), (7, 71), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b91) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b95) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 87), (1, 58), (2, 113), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b98) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 87), (1, 58), (2, 113), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b9c) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 87), (1, 58), (2, 116), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ba1) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 87), (1, 58), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ba4) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 87), (1, 120), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ba7) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.exec (n := 122) (ρ' := [(0, 87), (1, 120), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bab) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 87), (1, 123), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bb0) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 87), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bb3) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bbb) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101b02_2 code

theorem rest_l101b02 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101b02 bytes_l101b02) (entryMap (live .l101b02))
      66 0x101b02 bytes_l101b02 b_l101b02 := by
  have f0 : InstrSpec 0x101b02 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x4F] (LoadPre 0x101b02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x101b02 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b02 6 8 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x101b02 6 8 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101b02 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101b08 [0x0F, 0xB6, 0x44, 0x24, 0x40] (LoadPre 0x101b08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101b08 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b08 5 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101b08 5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (movzx_r32_m8_effect_step 0x101b08 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101b0d [0x88, 0x44, 0x24, 0x3F] (StorePre 0x101b0d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x101b0d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101b0d 4 0 (.sib 4 none 0 (.d8 0x3f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101b0d 4 0 (.sib 4 none 0 (.d8 0x3f))).toInstrSpec (mov_m8_r8_effect_step 0x101b0d 0 (by decide) (.sib 4 none 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101b11 [0x0F, 0xB6, 0x4C, 0x24, 0x41] (LoadPre 0x101b11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x101b11 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b11 5 1 (.sib 4 none 0 (.d8 0x41)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101b11 5 1 (.sib 4 none 0 (.d8 0x41))).toInstrSpec (movzx_r32_m8_effect_step 0x101b11 1 (.sib 4 none 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x101b16 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x4E] (LoadPre 0x101b16 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x101b16 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b16 6 10 (.sib 4 none 0 (.d8 0x4e)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x101b16 6 10 (.sib 4 none 0 (.d8 0x4e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101b16 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x4e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101b1c [0x0F, 0xB6, 0x44, 0x24, 0x42] (LoadPre 0x101b1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x101b1c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b1c 5 0 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101b1c 5 0 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (movzx_r32_m8_effect_step 0x101b1c 0 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101b21 [0x88, 0x44, 0x24, 0x0F] (StorePre 0x101b21 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101b21 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101b21 4 0 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101b21 4 0 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x101b21 0 (by decide) (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101b25 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x4D] (LoadPre 0x101b25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x101b25 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b25 6 11 (.sib 4 none 0 (.d8 0x4d)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x101b25 6 11 (.sib 4 none 0 (.d8 0x4d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101b25 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101b2b [0x0F, 0xB6, 0x54, 0x24, 0x43] (LoadPre 0x101b2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x101b2b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b2b 5 2 (.sib 4 none 0 (.d8 0x43)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x101b2b 5 2 (.sib 4 none 0 (.d8 0x43))).toInstrSpec (movzx_r32_m8_effect_step 0x101b2b 2 (.sib 4 none 0 (.d8 0x43)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x101b30 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x4C] (LoadPre 0x101b30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x101b30 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b30 6 15 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x101b30 6 15 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101b30 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101b36 [0x0F, 0xB6, 0x7C, 0x24, 0x44] (LoadPre 0x101b36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x101b36 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b36 5 7 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x101b36 5 7 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (movzx_r32_m8_effect_step 0x101b36 7 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101b3b [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x4B] (LoadPre 0x101b3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x101b3b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b3b 6 12 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x101b3b 6 12 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101b3b 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101b41 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x45] (LoadPre 0x101b41 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x101b41 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b41 6 9 (.sib 4 none 0 (.d8 0x45)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x101b41 6 9 (.sib 4 none 0 (.d8 0x45))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101b41 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x45)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x101b47 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4A] (LoadPre 0x101b47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x101b47 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b47 6 13 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x101b47 6 13 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101b47 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101b4d [0x0F, 0xB6, 0x5C, 0x24, 0x46] (LoadPre 0x101b4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x101b4d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b4d 5 3 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x101b4d 5 3 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (movzx_r32_m8_effect_step 0x101b4d 3 (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101b52 [0x0F, 0xB6, 0x6C, 0x24, 0x49] (LoadPre 0x101b52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x101b52 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b52 5 5 (.sib 4 none 0 (.d8 0x49)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x101b52 5 5 (.sib 4 none 0 (.d8 0x49))).toInstrSpec (movzx_r32_m8_effect_step 0x101b52 5 (.sib 4 none 0 (.d8 0x49)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101b57 [0x0F, 0xB6, 0x74, 0x24, 0x47] (LoadPre 0x101b57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x101b57 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101b57 5 6 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x101b57 5 6 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (movzx_r32_m8_effect_step 0x101b57 6 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x101b5c [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x48] (LoadPre 0x101b5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101b5c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101b5c 6 14 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x101b5c 6 14 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101b5c 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x101b62 [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x101b62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101b62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101b62 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101b62 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x101b62 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x101b67 [0x44, 0x32, 0x00] (LoadPre 0x101b67 (fun s => AddrMode.addr (.base 0 .none) s (0x101b67 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101b67 3 8 (.base 0 .none))
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101b67 3 8 (.base 0 .none)).toInstrSpec (xor_r8_m8_rex_effect_step 0x101b67 0x44 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b08) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b0d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (4, 4), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b11) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 58), (4, 4), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b16) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 58), (4, 4), (8, 53), (10, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b1c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 58), (4, 4), (8, 53), (10, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b21) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 58), (4, 4), (8, 53), (10, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b25) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 58), (4, 4), (8, 53), (10, 60), (11, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b2b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (8, 53), (10, 60), (11, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b30) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (8, 53), (10, 60), (11, 65), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b36) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (7, 71), (8, 53), (10, 60), (11, 65), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b3b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (7, 71), (8, 53), (10, 60), (11, 65), (12, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b41) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b47) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b4d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 62), (1, 58), (2, 67), (3, 79), (4, 4), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b52) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 62), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b57) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b5c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b62) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b67) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b6a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101b02_1 code

theorem block_l101b02 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101b02 :=
  Rest.liftedBlock (rest_l101b02 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101b02 x hx)

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

theorem_by block_l101800_eval :
    program.runBlock (dialect code) ⟨.l101800, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101866_eval :
    program.runBlock (dialect code) ⟨.l101866, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101873_eval :
    program.runBlock (dialect code) ⟨.l101873, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10189b_eval :
    program.runBlock (dialect code) ⟨.l10189b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1018ac_eval :
    program.runBlock (dialect code) ⟨.l1018ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10193e_eval :
    program.runBlock (dialect code) ⟨.l10193e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101952_eval :
    program.runBlock (dialect code) ⟨.l101952, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10195f_eval :
    program.runBlock (dialect code) ⟨.l10195f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101987_eval :
    program.runBlock (dialect code) ⟨.l101987, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101998_eval :
    program.runBlock (dialect code) ⟨.l101998, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101a2a_eval :
    program.runBlock (dialect code) ⟨.l101a2a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101acb_eval :
    program.runBlock (dialect code) ⟨.l101acb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101b02_eval :
    program.runBlock (dialect code) ⟨.l101b02, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
