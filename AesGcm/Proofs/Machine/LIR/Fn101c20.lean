import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l101c20_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x101c20 bytes_l101c20) [(0, 83), (1, 85), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x101c6d bytes_l101c20_1 b_l101c20_1 := by
  have f20 : InstrSpec 0x101c6d [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x101c6d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101c6d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c6d 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c6d 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x101c6d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x101c72 [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x101c72) (movR64R64Effect 0x101c72 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101c72 2 8).toInstrSpec (mov_r64_r64_effect_step 0x101c72 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x101c75 [0x48, 0xC1, 0xEA, 0x04] (fun s => s.RIP = 0x101c75) (shrR64Effect 0x101c75 4 2 4)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x101c75 4 2 4).toInstrSpec (shr_r64_imm8_effect_step 0x101c75 0x48 0xea 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x101c79 [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101c79) (leaR64Effect 0x101c79 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101c79 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101c79 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x101c7e [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x101c7e) (movR64R64Effect 0x101c7e 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101c7e 6 12).toInstrSpec (mov_r64_r64_effect_step 0x101c7e 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x101c81 [0xE8, 0xFA, 0x7C, 0x00, 0x00] (PushPre 0x101c81 5) (callEffect (fun _ => 0x109980) 0x101c86)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101c81 0x109980 0x101c86).toInstrSpec (call_rel32_effect_step 0x101c81 0x7cfa (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 85), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c72) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 83), (1, 85), (2, 89), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c75) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 83), (1, 85), (2, 91), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c79) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 83), (1, 85), (2, 91), (3, 72), (4, 65), (5, 5), (6, 6), (7, 93), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c7e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 83), (1, 85), (2, 91), (3, 72), (4, 65), (5, 5), (6, 95), (7, 93), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c81) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 83), (1, 85), (2, 91), (3, 72), (4, 97), (5, 5), (6, 95), (7, 93), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109980) f25 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 99) (by decide) (by decide) rfl rfl

theorem rest_l101c20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c20 bytes_l101c20) (entryMap (live .l101c20))
      26 0x101c20 bytes_l101c20 b_l101c20 := by
  have f0 : InstrSpec 0x101c20 [0x55] (PushPre 0x101c20 1) (pushR64Effect 0x101c20 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c20 1 5).toInstrSpec (push_r64_effect_step 0x101c20 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101c21 [0x41, 0x57] (PushPre 0x101c21 2) (pushR64Effect 0x101c21 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c21 2 15).toInstrSpec (push_r64_rex_effect_step 0x101c21 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101c23 [0x41, 0x56] (PushPre 0x101c23 2) (pushR64Effect 0x101c23 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c23 2 14).toInstrSpec (push_r64_rex_effect_step 0x101c23 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101c25 [0x41, 0x55] (PushPre 0x101c25 2) (pushR64Effect 0x101c25 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c25 2 13).toInstrSpec (push_r64_rex_effect_step 0x101c25 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101c27 [0x41, 0x54] (PushPre 0x101c27 2) (pushR64Effect 0x101c27 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c27 2 12).toInstrSpec (push_r64_rex_effect_step 0x101c27 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101c29 [0x53] (PushPre 0x101c29 1) (pushR64Effect 0x101c29 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c29 1 3).toInstrSpec (push_r64_effect_step 0x101c29 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101c2a [0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101c2a) (subR64Imm32Effect 0x101c2a 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x101c2a 4 0x88).toInstrSpec (sub_r64_imm32_effect_step 0x101c2a 0x48 0xec 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101c31 [0x49, 0x89, 0xCC] (fun s => s.RIP = 0x101c31) (movR64R64Effect 0x101c31 12 1)
      [.gpr 1] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x101c31 12 1).toInstrSpec (mov_r64_r64_effect_step 0x101c31 0x49 0xcc (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101c34 [0x48, 0x89, 0x54, 0x24, 0x78] (StorePre 0x101c34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101c34 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c34 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c34 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x101c34 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101c39 [0x4D, 0x89, 0xCE] (fun s => s.RIP = 0x101c39) (movR64R64Effect 0x101c39 14 9)
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101c39 14 9).toInstrSpec (mov_r64_r64_effect_step 0x101c39 0x4d 0xce (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101c3c [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x101c3c) (movR64R64Effect 0x101c3c 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101c3c 3 8).toInstrSpec (mov_r64_r64_effect_step 0x101c3c 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101c3f [0x48, 0x89, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x101c3f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101c3f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101c3f 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c3f 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x101c3f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101c47 [0x4C, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x101c47 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x101c47 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101c47 15 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x101c47 15 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x101c47 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x101c4f [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x101c4f (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101c4f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c4f 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101c4f 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101c4f 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101c53 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x101c53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101c53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c53 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c53 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x101c53 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101c58 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x101c58 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101c58 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c58 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101c58 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101c58 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101c5c [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x101c5c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101c5c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c5c 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c5c 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x101c5c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101c61 [0x48, 0x8B, 0x06] (LoadPre 0x101c61 (fun s => AddrMode.addr (.base 6 .none) s (0x101c61 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101c61 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101c61 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101c61 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x101c64 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x101c64 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101c64 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c64 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101c64 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101c64 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x101c68 [0x48, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x101c68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101c68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c68 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c68 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x101c68 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c21) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c23) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c25) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c27) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c29) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c2a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c31) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c34) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c39) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c3c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c3f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c47) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c4f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c53) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c58) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c5c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c61) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c64) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 85), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c68) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 85), (2, 2), (3, 72), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c6d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l101c20_1 code

theorem block_l101c20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c20 :=
  Rest.liftedBlock (rest_l101c20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c20 x hx)

theorem rest_l101c86 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c86 bytes_l101c86) (entryMap (live .l101c86))
      3 0x101c86 bytes_l101c86 b_l101c86 := by
  have f0 : InstrSpec 0x101c86 [0x49, 0x89, 0xDD] (fun s => s.RIP = 0x101c86) (movR64R64Effect 0x101c86 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101c86 13 3).toInstrSpec (mov_r64_r64_effect_step 0x101c86 0x49 0xdd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101c89 [0x49, 0x83, 0xE5, 0x0F] (fun s => s.RIP = 0x101c89) (andR64Imm8Effect 0x101c89 13 0xf)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x101c89 13 0xf).toInstrSpec (and_r64_imm8_effect_step 0x101c89 0x49 0xe5 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c89) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c8d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x101c8d 4 0xcb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101c86 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c86 :=
  Rest.liftedBlock (rest_l101c86 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c86 x hx)

theorem rest_l101c93 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c93 bytes_l101c93) (entryMap (live .l101c93))
      9 0x101c93 bytes_l101c93 b_l101c93 := by
  have f0 : InstrSpec 0x101c93 [0x48, 0xB8, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F] (fun s => s.RIP = 0x101c93) (movR64Imm64Effect 0x101c93 0 0x1ffffffffffffff0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x101c93 0 0x1ffffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x101c93 0x48 0xb8 (by decide) (by decide) 0x1ffffffffffffff0) pre_rip
  have f1 : InstrSpec 0x101c9d [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x101c9d) (andR64R64Effect 0x101c9d 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101c9d 0 3).toInstrSpec (and_r64_r64_effect_step 0x101c9d 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101ca0 [0x49, 0x01, 0xC4] (fun s => s.RIP = 0x101ca0) (addR64R64Effect 0x101ca0 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101ca0 12 0).toInstrSpec (add_r64_r64_effect_step 0x101ca0 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101ca3 [0xBA, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ca3) (movR32Imm32Effect 0x101ca3 5 2 0x10)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101ca3 5 2 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x101ca3 0xba (by decide) 0x10) pre_rip
  have f4 : InstrSpec 0x101ca8 [0x4C, 0x29, 0xEA] (fun s => s.RIP = 0x101ca8) (subR64R64Effect 0x101ca8 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101ca8 2 13).toInstrSpec (sub_r64_r64_effect_step 0x101ca8 0x4c 0xea (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101cab [0x4A, 0x8D, 0x3C, 0x2C] (fun s => s.RIP = 0x101cab) (leaR64Effect 0x101cab 7 (.sib 4 (some 13) 0 .none))
      [.gpr 4, .gpr 13] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101cab 7 (.sib 4 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x101cab 0x4a (by decide) 7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101caf [0x48, 0x83, 0xC7, 0x40] (fun s => s.RIP = 0x101caf) (addR64Imm8Effect 0x101caf 7 0x40)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x101caf 7 0x40).toInstrSpec (add_r64_imm8_effect_step 0x101caf 0x48 0xc7 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101cb3 [0x31, 0xF6] (fun s => s.RIP = 0x101cb3) (xorR32R32Effect 0x101cb3 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101cb3 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x101cb3 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x101cb5 [0xFF, 0x15, 0x6D, 0xF5, 0x0F, 0x00] (GoesTo (CallMemPre 0x101cb5 (.rip 0xff56d)) (callEffect (callMemPtr 0x101cb5 (.rip 0xff56d)) (0x101cb5 + BitVec.ofNat 64 (callMemLen (.rip 0xff56d)))) 0x103eb0) (callEffect (callMemPtr 0x101cb5 (.rip 0xff56d)) (0x101cb5 + BitVec.ofNat 64 (callMemLen (.rip 0xff56d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101cb5 (.rip 0xff56d)).toInstrSpec (call_m64_effect_step 0x101cb5 (.rip 0xff56d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c9d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cab) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101caf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cb3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cb5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l101c93 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c93 :=
  Rest.liftedBlock (rest_l101c93 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c93 x hx)

theorem rest_l101cbb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101cbb bytes_l101cbb) (entryMap (live .l101cbb))
      4 0x101cbb bytes_l101cbb b_l101cbb := by
  have f0 : InstrSpec 0x101cbb [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x101cbb) (leaR64Effect 0x101cbb 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101cbb 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x101cbb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101cc0 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x101cc0) (movR64R64Effect 0x101cc0 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101cc0 6 12).toInstrSpec (mov_r64_r64_effect_step 0x101cc0 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101cc3 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x101cc3) (movR64R64Effect 0x101cc3 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101cc3 2 13).toInstrSpec (mov_r64_r64_effect_step 0x101cc3 0x4c 0xea (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101cc6 [0xFF, 0x15, 0x3C, 0xF5, 0x0F, 0x00] (GoesTo (CallMemPre 0x101cc6 (.rip 0xff53c)) (callEffect (callMemPtr 0x101cc6 (.rip 0xff53c)) (0x101cc6 + BitVec.ofNat 64 (callMemLen (.rip 0xff53c)))) 0x103f00) (callEffect (callMemPtr 0x101cc6 (.rip 0xff53c)) (0x101cc6 + BitVec.ofNat 64 (callMemLen (.rip 0xff53c))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101cc6 (.rip 0xff53c)).toInstrSpec (call_m64_effect_step 0x101cc6 (.rip 0xff53c) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cc0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cc3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cc6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101cbb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101cbb :=
  Rest.liftedBlock (rest_l101cbb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101cbb x hx)

theorem rest_l101ccc_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x101ccc bytes_l101ccc) [(0, 83), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x101d2a bytes_l101ccc_1 b_l101ccc_1 := by
  have f20 : InstrSpec 0x101d2a [0x0F, 0xB6, 0x4C, 0x24, 0x1A] (LoadPre 0x101d2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101d2a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d2a 5 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101d2a 5 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (movzx_r32_m8_effect_step 0x101d2a 1 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x101d2f [0x88, 0x4C, 0x24, 0x15] (StorePre 0x101d2f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101d2f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101d2f 4 1 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101d2f 4 1 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_effect_step 0x101d2f 1 (by decide) (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x101d33 [0x88, 0x44, 0x24, 0x1A] (StorePre 0x101d33 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101d33 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101d33 4 0 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101d33 4 0 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_effect_step 0x101d33 0 (by decide) (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101d37 [0x0F, 0xB6, 0x44, 0x24, 0x16] (LoadPre 0x101d37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101d37 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d37 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101d37 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m8_effect_step 0x101d37 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x101d3c [0x0F, 0xB6, 0x4C, 0x24, 0x19] (LoadPre 0x101d3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101d3c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d3c 5 1 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101d3c 5 1 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m8_effect_step 0x101d3c 1 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x101d41 [0x88, 0x4C, 0x24, 0x16] (StorePre 0x101d41 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101d41 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101d41 4 1 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101d41 4 1 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_effect_step 0x101d41 1 (by decide) (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x101d45 [0x88, 0x44, 0x24, 0x19] (StorePre 0x101d45 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101d45 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101d45 4 0 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101d45 4 0 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x101d45 0 (by decide) (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x101d49 [0x66, 0xC1, 0x44, 0x24, 0x17, 0x08] (StorePre 0x101d49 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x101d49 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x101d49 6 16 (.sib 4 none 0 (.d8 0x17)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x101d49 6 (.sib 4 none 0 (.d8 0x17)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x101d49 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x101d4f [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101d4f) (leaR64Effect 0x101d4f 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101d4f 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101d4f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x101d54 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x101d54) (leaR64Effect 0x101d54 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101d54 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101d54 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x101d59 [0xE8, 0x62, 0x17, 0x00, 0x00] (PushPre 0x101d59 5) (callEffect (fun _ => 0x1034c0) 0x101d5e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101d59 0x1034c0 0x101d5e).toInstrSpec (call_rel32_effect_step 0x101d59 0x1762 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d2f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d33) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d37) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d3c) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d41) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d45) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d49) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d4f) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d54) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d59) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f30 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 100), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c0) f30 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 102) (by decide) (by decide) rfl rfl

theorem rest_l101ccc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101ccc bytes_l101ccc) (entryMap (live .l101ccc))
      31 0x101ccc bytes_l101ccc b_l101ccc := by
  have f0 : InstrSpec 0x101ccc [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x101ccc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101ccc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ccc 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101ccc 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x101ccc 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101cd1 [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x101cd1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101cd1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101cd1 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101cd1 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x101cd1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101cd6 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x101cd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101cd6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101cd6 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101cd6 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101cd6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101cdb [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x101cdb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101cdb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101cdb 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101cdb 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101cdb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101ce0 [0x0F, 0xB6, 0x4C, 0x24, 0x1F] (LoadPre 0x101ce0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101ce0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101ce0 5 1 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101ce0 5 1 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_effect_step 0x101ce0 1 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101ce5 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x101ce5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101ce5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ce5 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ce5 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x101ce5 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101ce9 [0x88, 0x44, 0x24, 0x1F] (StorePre 0x101ce9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101ce9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ce9 4 0 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ce9 4 0 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x101ce9 0 (by decide) (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101ced [0x0F, 0xB7, 0x44, 0x24, 0x11] (LoadPre 0x101ced (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101ced + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101ced 5 0 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x101ced 5 0 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m16_effect_step 0x101ced 0 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101cf2 [0x66, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x101cf2) (rolR16Effect 0x101cf2 4 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x101cf2 4 0 8).toInstrSpec (rol_r16_imm8_effect_step 0x101cf2 0xc0 0x8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101cf6 [0x0F, 0xB7, 0x4C, 0x24, 0x1D] (LoadPre 0x101cf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101cf6 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101cf6 5 1 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x101cf6 5 1 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m16_effect_step 0x101cf6 1 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101cfb [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x101cfb) (rolR16Effect 0x101cfb 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x101cfb 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x101cfb 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101cff [0x0F, 0xB7, 0x54, 0x24, 0x13] (LoadPre 0x101cff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101cff + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101cff 5 2 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x101cff 5 2 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m16_effect_step 0x101cff 2 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101d04 [0x66, 0x89, 0x4C, 0x24, 0x11] (StorePre 0x101d04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101d04 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101d04 5 1 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101d04 5 1 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m16_r16_effect_step 0x101d04 1 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101d09 [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x101d09) (rolR16Effect 0x101d09 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x101d09 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x101d09 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101d0d [0x66, 0x89, 0x44, 0x24, 0x1D] (StorePre 0x101d0d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101d0d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101d0d 5 0 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101d0d 5 0 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_m16_r16_effect_step 0x101d0d 0 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101d12 [0x0F, 0xB7, 0x44, 0x24, 0x1B] (LoadPre 0x101d12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101d12 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101d12 5 0 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x101d12 5 0 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m16_effect_step 0x101d12 0 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101d17 [0x66, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x101d17) (rolR16Effect 0x101d17 4 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x101d17 4 0 8).toInstrSpec (rol_r16_imm8_effect_step 0x101d17 0xc0 0x8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101d1b [0x66, 0x89, 0x44, 0x24, 0x13] (StorePre 0x101d1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101d1b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101d1b 5 0 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101d1b 5 0 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m16_r16_effect_step 0x101d1b 0 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101d20 [0x66, 0x89, 0x54, 0x24, 0x1B] (StorePre 0x101d20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101d20 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101d20 5 2 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101d20 5 2 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_m16_r16_effect_step 0x101d20 2 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x101d25 [0x0F, 0xB6, 0x44, 0x24, 0x15] (LoadPre 0x101d25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101d25 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d25 5 0 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101d25 5 0 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (movzx_r32_m8_effect_step 0x101d25 0 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cd6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cdb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ced) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cfb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cff) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d04) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 65), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d09) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d0d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d12) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d17) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d1b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d20) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d25) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d2a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101ccc_1 code

theorem block_l101ccc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101ccc :=
  Rest.liftedBlock (rest_l101ccc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101ccc x hx)

theorem rest_l101d5e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d5e bytes_l101d5e) (entryMap (live .l101d5e))
      5 0x101d5e bytes_l101d5e b_l101d5e := by
  have f0 : InstrSpec 0x101d5e [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x101d5e) (movR64R64Effect 0x101d5e 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101d5e 2 15).toInstrSpec (mov_r64_r64_effect_step 0x101d5e 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101d61 [0x48, 0xC1, 0xEA, 0x04] (fun s => s.RIP = 0x101d61) (shrR64Effect 0x101d61 4 2 4)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x101d61 4 2 4).toInstrSpec (shr_r64_imm8_effect_step 0x101d61 0x48 0xea 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101d65 [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101d65) (leaR64Effect 0x101d65 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101d65 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101d65 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101d6a [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x101d6a) (movR64R64Effect 0x101d6a 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d6a 6 14).toInstrSpec (mov_r64_r64_effect_step 0x101d6a 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101d6d [0xE8, 0x0E, 0x7C, 0x00, 0x00] (PushPre 0x101d6d 5) (callEffect (fun _ => 0x109980) 0x101d72)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101d6d 0x109980 0x101d72).toInstrSpec (call_rel32_effect_step 0x101d6d 0x7c0e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d61) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d65) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d6a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d6d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109980) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l101d5e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d5e :=
  Rest.liftedBlock (rest_l101d5e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d5e x hx)

theorem rest_l101d72 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d72 bytes_l101d72) (entryMap (live .l101d72))
      3 0x101d72 bytes_l101d72 b_l101d72 := by
  have f0 : InstrSpec 0x101d72 [0x4D, 0x89, 0xFC] (fun s => s.RIP = 0x101d72) (movR64R64Effect 0x101d72 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x101d72 12 15).toInstrSpec (mov_r64_r64_effect_step 0x101d72 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101d75 [0x49, 0x83, 0xE4, 0x0F] (fun s => s.RIP = 0x101d75) (andR64Imm8Effect 0x101d75 12 0xf)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x101d75 12 0xf).toInstrSpec (and_r64_imm8_effect_step 0x101d75 0x49 0xe4 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d75) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d79) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x101d79 4 0xcb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101d72 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d72 :=
  Rest.liftedBlock (rest_l101d72 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d72 x hx)

theorem rest_l101d7f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d7f bytes_l101d7f) (entryMap (live .l101d7f))
      9 0x101d7f bytes_l101d7f b_l101d7f := by
  have f0 : InstrSpec 0x101d7f [0x48, 0xB8, 0xF0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d7f) (movR64Imm64Effect 0x101d7f 0 0xffffffff0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x101d7f 0 0xffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x101d7f 0x48 0xb8 (by decide) (by decide) 0xffffffff0) pre_rip
  have f1 : InstrSpec 0x101d89 [0x4C, 0x21, 0xF8] (fun s => s.RIP = 0x101d89) (andR64R64Effect 0x101d89 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101d89 0 15).toInstrSpec (and_r64_r64_effect_step 0x101d89 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101d8c [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x101d8c) (addR64R64Effect 0x101d8c 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101d8c 14 0).toInstrSpec (add_r64_r64_effect_step 0x101d8c 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101d8f [0xBA, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d8f) (movR32Imm32Effect 0x101d8f 5 2 0x10)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101d8f 5 2 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x101d8f 0xba (by decide) 0x10) pre_rip
  have f4 : InstrSpec 0x101d94 [0x4C, 0x29, 0xE2] (fun s => s.RIP = 0x101d94) (subR64R64Effect 0x101d94 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101d94 2 12).toInstrSpec (sub_r64_r64_effect_step 0x101d94 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101d97 [0x4A, 0x8D, 0x3C, 0x24] (fun s => s.RIP = 0x101d97) (leaR64Effect 0x101d97 7 (.sib 4 (some 12) 0 .none))
      [.gpr 4, .gpr 12] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101d97 7 (.sib 4 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x101d97 0x4a (by decide) 7 (.sib 4 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101d9b [0x48, 0x83, 0xC7, 0x40] (fun s => s.RIP = 0x101d9b) (addR64Imm8Effect 0x101d9b 7 0x40)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x101d9b 7 0x40).toInstrSpec (add_r64_imm8_effect_step 0x101d9b 0x48 0xc7 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101d9f [0x31, 0xF6] (fun s => s.RIP = 0x101d9f) (xorR32R32Effect 0x101d9f 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101d9f 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x101d9f 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x101da1 [0xFF, 0x15, 0x81, 0xF4, 0x0F, 0x00] (GoesTo (CallMemPre 0x101da1 (.rip 0xff481)) (callEffect (callMemPtr 0x101da1 (.rip 0xff481)) (0x101da1 + BitVec.ofNat 64 (callMemLen (.rip 0xff481)))) 0x103eb0) (callEffect (callMemPtr 0x101da1 (.rip 0xff481)) (0x101da1 + BitVec.ofNat 64 (callMemLen (.rip 0xff481))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101da1 (.rip 0xff481)).toInstrSpec (call_m64_effect_step 0x101da1 (.rip 0xff481) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d89) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d8c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d8f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d94) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d97) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d9b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d9f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101da1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l101d7f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d7f :=
  Rest.liftedBlock (rest_l101d7f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d7f x hx)

theorem rest_l101da7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101da7 bytes_l101da7) (entryMap (live .l101da7))
      4 0x101da7 bytes_l101da7 b_l101da7 := by
  have f0 : InstrSpec 0x101da7 [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x101da7) (leaR64Effect 0x101da7 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101da7 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x101da7 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101dac [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x101dac) (movR64R64Effect 0x101dac 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101dac 6 14).toInstrSpec (mov_r64_r64_effect_step 0x101dac 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101daf [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x101daf) (movR64R64Effect 0x101daf 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101daf 2 12).toInstrSpec (mov_r64_r64_effect_step 0x101daf 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101db2 [0xFF, 0x15, 0x50, 0xF4, 0x0F, 0x00] (GoesTo (CallMemPre 0x101db2 (.rip 0xff450)) (callEffect (callMemPtr 0x101db2 (.rip 0xff450)) (0x101db2 + BitVec.ofNat 64 (callMemLen (.rip 0xff450)))) 0x103f00) (callEffect (callMemPtr 0x101db2 (.rip 0xff450)) (0x101db2 + BitVec.ofNat 64 (callMemLen (.rip 0xff450))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101db2 (.rip 0xff450)).toInstrSpec (call_m64_effect_step 0x101db2 (.rip 0xff450) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101daf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101da7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101da7 :=
  Rest.liftedBlock (rest_l101da7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101da7 x hx)

theorem rest_l101db8_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x101db8 bytes_l101db8) [(0, 83), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x101e16 bytes_l101db8_1 b_l101db8_1 := by
  have f20 : InstrSpec 0x101e16 [0x0F, 0xB6, 0x4C, 0x24, 0x1A] (LoadPre 0x101e16 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101e16 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e16 5 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101e16 5 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (movzx_r32_m8_effect_step 0x101e16 1 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x101e1b [0x88, 0x4C, 0x24, 0x15] (StorePre 0x101e1b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101e1b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e1b 4 1 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e1b 4 1 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_effect_step 0x101e1b 1 (by decide) (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x101e1f [0x88, 0x44, 0x24, 0x1A] (StorePre 0x101e1f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101e1f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e1f 4 0 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e1f 4 0 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_effect_step 0x101e1f 0 (by decide) (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101e23 [0x0F, 0xB6, 0x44, 0x24, 0x16] (LoadPre 0x101e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101e23 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e23 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101e23 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m8_effect_step 0x101e23 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x101e28 [0x0F, 0xB6, 0x4C, 0x24, 0x19] (LoadPre 0x101e28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101e28 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e28 5 1 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101e28 5 1 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m8_effect_step 0x101e28 1 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x101e2d [0x88, 0x4C, 0x24, 0x16] (StorePre 0x101e2d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101e2d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e2d 4 1 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e2d 4 1 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_effect_step 0x101e2d 1 (by decide) (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x101e31 [0x88, 0x44, 0x24, 0x19] (StorePre 0x101e31 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101e31 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e31 4 0 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e31 4 0 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x101e31 0 (by decide) (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x101e35 [0x66, 0xC1, 0x44, 0x24, 0x17, 0x08] (StorePre 0x101e35 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x101e35 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x101e35 6 16 (.sib 4 none 0 (.d8 0x17)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x101e35 6 (.sib 4 none 0 (.d8 0x17)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x101e35 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x101e3b [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101e3b) (leaR64Effect 0x101e3b 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101e3b 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101e3b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x101e40 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x101e40) (leaR64Effect 0x101e40 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101e40 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101e40 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x101e45 [0xE8, 0x76, 0x16, 0x00, 0x00] (PushPre 0x101e45 5) (callEffect (fun _ => 0x1034c0) 0x101e4a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101e45 0x1034c0 0x101e4a).toInstrSpec (call_rel32_effect_step 0x101e45 0x1676 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1b) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e23) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 85), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e28) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e2d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e31) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e35) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e3b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e40) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 4), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e45) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f30 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 89), (1, 91), (2, 74), (3, 3), (4, 100), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c0) f30 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 102) (by decide) (by decide) rfl rfl

theorem rest_l101db8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101db8 bytes_l101db8) (entryMap (live .l101db8))
      31 0x101db8 bytes_l101db8 b_l101db8 := by
  have f0 : InstrSpec 0x101db8 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x101db8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101db8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101db8 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101db8 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x101db8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101dbd [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x101dbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101dbd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101dbd 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101dbd 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x101dbd 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101dc2 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x101dc2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101dc2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101dc2 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101dc2 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101dc2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101dc7 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x101dc7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101dc7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101dc7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101dc7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101dc7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101dcc [0x0F, 0xB6, 0x4C, 0x24, 0x1F] (LoadPre 0x101dcc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101dcc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101dcc 5 1 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101dcc 5 1 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_effect_step 0x101dcc 1 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101dd1 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x101dd1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101dd1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101dd1 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101dd1 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x101dd1 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101dd5 [0x88, 0x44, 0x24, 0x1F] (StorePre 0x101dd5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101dd5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101dd5 4 0 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101dd5 4 0 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x101dd5 0 (by decide) (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101dd9 [0x0F, 0xB7, 0x44, 0x24, 0x11] (LoadPre 0x101dd9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101dd9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101dd9 5 0 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x101dd9 5 0 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m16_effect_step 0x101dd9 0 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101dde [0x66, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x101dde) (rolR16Effect 0x101dde 4 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x101dde 4 0 8).toInstrSpec (rol_r16_imm8_effect_step 0x101dde 0xc0 0x8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101de2 [0x0F, 0xB7, 0x4C, 0x24, 0x1D] (LoadPre 0x101de2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101de2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101de2 5 1 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x101de2 5 1 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m16_effect_step 0x101de2 1 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101de7 [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x101de7) (rolR16Effect 0x101de7 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x101de7 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x101de7 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101deb [0x0F, 0xB7, 0x54, 0x24, 0x13] (LoadPre 0x101deb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101deb + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101deb 5 2 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x101deb 5 2 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m16_effect_step 0x101deb 2 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101df0 [0x66, 0x89, 0x4C, 0x24, 0x11] (StorePre 0x101df0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101df0 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101df0 5 1 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101df0 5 1 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m16_r16_effect_step 0x101df0 1 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101df5 [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x101df5) (rolR16Effect 0x101df5 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x101df5 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x101df5 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101df9 [0x66, 0x89, 0x44, 0x24, 0x1D] (StorePre 0x101df9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101df9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101df9 5 0 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101df9 5 0 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_m16_r16_effect_step 0x101df9 0 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101dfe [0x0F, 0xB7, 0x44, 0x24, 0x1B] (LoadPre 0x101dfe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101dfe + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101dfe 5 0 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x101dfe 5 0 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m16_effect_step 0x101dfe 0 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101e03 [0x66, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x101e03) (rolR16Effect 0x101e03 4 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x101e03 4 0 8).toInstrSpec (rol_r16_imm8_effect_step 0x101e03 0xc0 0x8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101e07 [0x66, 0x89, 0x44, 0x24, 0x13] (StorePre 0x101e07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101e07 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101e07 5 0 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101e07 5 0 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m16_r16_effect_step 0x101e07 0 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101e0c [0x66, 0x89, 0x54, 0x24, 0x1B] (StorePre 0x101e0c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101e0c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101e0c 5 2 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x101e0c 5 2 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_m16_r16_effect_step 0x101e0c 2 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x101e11 [0x0F, 0xB6, 0x44, 0x24, 0x15] (LoadPre 0x101e11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101e11 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e11 5 0 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101e11 5 0 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (movzx_r32_m8_effect_step 0x101e11 0 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dbd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dcc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dde) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101de2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101de7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101deb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 65), (1, 69), (2, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dfe) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e03) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e07) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e0c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e11) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 69), (2, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e16) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101db8_1 code

theorem block_l101db8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101db8 :=
  Rest.liftedBlock (rest_l101db8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101db8 x hx)

theorem rest_l101e4a_2 [Bindings] (code : CodeMap) :
    Rest (n := 118) code lifted (codeRange 0x101e4a bytes_l101e4a) [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x101ee1 bytes_l101e4a_2 b_l101e4a_2 := by
  have f40 : InstrSpec 0x101ee1 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x101ee1) (leaR64Effect 0x101ee1 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101ee1 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101ee1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x101ee6 [0xE8, 0xD5, 0x15, 0x00, 0x00] (PushPre 0x101ee6 5) (callEffect (fun _ => 0x1034c0) 0x101eeb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101ee6 0x1034c0 0x101eeb).toInstrSpec (call_rel32_effect_step 0x101ee6 0x15d5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (6, 118), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ee6) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 120), (5, 5), (6, 118), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c0) f41 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 122) (by decide) (by decide) rfl rfl

theorem rest_l101e4a_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x101e4a bytes_l101e4a) [(0, 85), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x101e8f bytes_l101e4a_1 b_l101e4a_1 := by
  have f20 : InstrSpec 0x101e8f [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x101e8f) (movR64R64Effect 0x101e8f 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x101e8f 1 15).toInstrSpec (mov_r64_r64_effect_step 0x101e8f 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x101e92 [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x101e92) (shrR64Effect 0x101e92 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101e92 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x101e92 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x101e96 [0x88, 0x4C, 0x24, 0x13] (StorePre 0x101e96 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101e96 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e96 4 1 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e96 4 1 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m8_r8_effect_step 0x101e96 1 (by decide) (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101e9a [0x88, 0x44, 0x24, 0x1C] (StorePre 0x101e9a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x101e9a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e9a 4 0 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e9a 4 0 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m8_r8_effect_step 0x101e9a 0 (by decide) (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x101e9e [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x101e9e) (movR64R64Effect 0x101e9e 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101e9e 0 3).toInstrSpec (mov_r64_r64_effect_step 0x101e9e 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x101ea1 [0x48, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x101ea1) (shrR64Effect 0x101ea1 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101ea1 4 0 32).toInstrSpec (shr_r64_imm8_effect_step 0x101ea1 0x48 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x101ea5 [0x41, 0xC1, 0xEF, 0x18] (fun s => s.RIP = 0x101ea5) (shrR32Effect 0x101ea5 4 15 24)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR32Effect_footprint 0x101ea5 4 15 24).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101ea5 0x41 0xef 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x101ea9 [0x44, 0x88, 0x7C, 0x24, 0x14] (StorePre 0x101ea9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x101ea9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x101ea9 5 15 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ea9 5 15 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101ea9 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x101eae [0x88, 0x44, 0x24, 0x1B] (StorePre 0x101eae 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101eae + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101eae 4 0 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101eae 4 0 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_m8_r8_effect_step 0x101eae 0 (by decide) (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x101eb2 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x101eb2) (movR64R64Effect 0x101eb2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101eb2 0 3).toInstrSpec (mov_r64_r64_effect_step 0x101eb2 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x101eb5 [0x48, 0xC1, 0xE8, 0x28] (fun s => s.RIP = 0x101eb5) (shrR64Effect 0x101eb5 4 0 40)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101eb5 4 0 40).toInstrSpec (shr_r64_imm8_effect_step 0x101eb5 0x48 0xe8 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x101eb9 [0xC6, 0x44, 0x24, 0x15, 0x00] (StorePre 0x101eb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101eb9 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x101eb9 (.sib 4 none 0 (.d8 0x15)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101eb9 (.sib 4 none 0 (.d8 0x15)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101eb9 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x101ebe [0x88, 0x44, 0x24, 0x1A] (StorePre 0x101ebe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101ebe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ebe 4 0 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ebe 4 0 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_effect_step 0x101ebe 0 (by decide) (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x101ec2 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x101ec2) (movR64R64Effect 0x101ec2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101ec2 0 3).toInstrSpec (mov_r64_r64_effect_step 0x101ec2 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x101ec5 [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x101ec5) (shrR64Effect 0x101ec5 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101ec5 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x101ec5 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x101ec9 [0x66, 0xC7, 0x44, 0x24, 0x16, 0x00, 0x00] (StorePre 0x101ec9 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101ec9 + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x101ec9 (.sib 4 none 0 (.d8 0x16)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x101ec9 (.sib 4 none 0 (.d8 0x16)) 0x0).toInstrSpec (mov_m16_imm16_effect_step 0x101ec9 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x101ed0 [0x88, 0x44, 0x24, 0x19] (StorePre 0x101ed0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101ed0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ed0 4 0 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ed0 4 0 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x101ed0 0 (by decide) (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x101ed4 [0x48, 0xC1, 0xEB, 0x38] (fun s => s.RIP = 0x101ed4) (shrR64Effect 0x101ed4 4 3 56)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x101ed4 4 3 56).toInstrSpec (shr_r64_imm8_effect_step 0x101ed4 0x48 0xeb 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x101ed8 [0x88, 0x5C, 0x24, 0x18] (StorePre 0x101ed8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101ed8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ed8 4 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ed8 4 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_effect_step 0x101ed8 3 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x101edc [0x48, 0x8D, 0x7C, 0x24, 0x50] (fun s => s.RIP = 0x101edc) (leaR64Effect 0x101edc 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101edc 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101edc 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (1, 87), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e92) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 85), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e96) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 85), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e9a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 85), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e9e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ea1) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ea5) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ea9) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eae) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eb2) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eb5) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eb9) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 103), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ebe) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 103), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ec2) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 107), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ec5) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ec9) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 109), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ed0) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 109), (1, 89), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ed4) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f37 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ed8) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101edc) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 109), (1, 89), (3, 113), (4, 4), (5, 5), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ee1) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101e4a_2 code

theorem rest_l101e4a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e4a bytes_l101e4a) (entryMap (live .l101e4a))
      42 0x101e4a bytes_l101e4a b_l101e4a := by
  have f0 : InstrSpec 0x101e4a [0x48, 0xC1, 0xE3, 0x03] (fun s => s.RIP = 0x101e4a) (shlR64Effect 0x101e4a 4 3 3)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x101e4a 4 3 3).toInstrSpec (shl_r64_imm8_effect_step 0x101e4a 0x48 0xe3 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101e4e [0x49, 0xC1, 0xE7, 0x03] (fun s => s.RIP = 0x101e4e) (shlR64Effect 0x101e4e 4 15 3)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64Effect_footprint 0x101e4e 4 15 3).toInstrSpec (shl_r64_imm8_effect_step 0x101e4e 0x49 0xe7 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e52 [0x48, 0x0F, 0xCB] (fun s => s.RIP = 0x101e52) (bswapR64Effect 0x101e52 3 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (bswapR64Effect_footprint 0x101e52 3 3).toInstrSpec (bswap_r64_effect_step 0x101e52 0x48 (by decide) 0xcb (by decide)) pre_rip
  have f3 : InstrSpec 0x101e55 [0x49, 0x0F, 0xCF] (fun s => s.RIP = 0x101e55) (bswapR64Effect 0x101e55 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (bswapR64Effect_footprint 0x101e55 3 15).toInstrSpec (bswap_r64_effect_step 0x101e55 0x49 (by decide) 0xcf (by decide)) pre_rip
  have f4 : InstrSpec 0x101e58 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x101e58) (movR64R64Effect 0x101e58 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101e58 0 15).toInstrSpec (mov_r64_r64_effect_step 0x101e58 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101e5b [0x48, 0xC1, 0xE8, 0x38] (fun s => s.RIP = 0x101e5b) (shrR64Effect 0x101e5b 4 0 56)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101e5b 4 0 56).toInstrSpec (shr_r64_imm8_effect_step 0x101e5b 0x48 0xe8 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101e5f [0x88, 0x44, 0x24, 0x10] (StorePre 0x101e5f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101e5f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e5f 4 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e5f 4 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x101e5f 0 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101e63 [0x88, 0x5C, 0x24, 0x1F] (StorePre 0x101e63 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101e63 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e63 4 3 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e63 4 3 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x101e63 3 (by decide) (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101e67 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x101e67) (movR64R64Effect 0x101e67 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101e67 0 15).toInstrSpec (mov_r64_r64_effect_step 0x101e67 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101e6a [0x48, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x101e6a) (shrR64Effect 0x101e6a 4 0 48)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x101e6a 4 0 48).toInstrSpec (shr_r64_imm8_effect_step 0x101e6a 0x48 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101e6e [0x88, 0x44, 0x24, 0x11] (StorePre 0x101e6e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101e6e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e6e 4 0 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e6e 4 0 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m8_r8_effect_step 0x101e6e 0 (by decide) (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x101e72 [0x88, 0x7C, 0x24, 0x1E] (StorePre 0x101e72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x101e72 + BitVec.ofNat 64 4)) 1) (movM8R8NoRexEffect 0x101e72 4 7 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x101e72 4 7 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (mov_m8_r8_norex_effect_step 0x101e72 7 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101e76 [0x89, 0xD8] (fun s => s.RIP = 0x101e76) (movR32R32Effect 0x101e76 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101e76 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x101e76 0xd8 (by decide)) pre_rip
  have f13 : InstrSpec 0x101e78 [0xC1, 0xE8, 0x10] (fun s => s.RIP = 0x101e78) (shrR32Effect 0x101e78 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x101e78 3 0 16).toInstrSpec (shr_r32_imm8_effect_step 0x101e78 0xe8 0x10 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101e7b [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x101e7b) (movR64R64Effect 0x101e7b 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x101e7b 1 15).toInstrSpec (mov_r64_r64_effect_step 0x101e7b 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101e7e [0x48, 0xC1, 0xE9, 0x28] (fun s => s.RIP = 0x101e7e) (shrR64Effect 0x101e7e 4 1 40)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101e7e 4 1 40).toInstrSpec (shr_r64_imm8_effect_step 0x101e7e 0x48 0xe9 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101e82 [0x88, 0x4C, 0x24, 0x12] (StorePre 0x101e82 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x101e82 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e82 4 1 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e82 4 1 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m8_r8_effect_step 0x101e82 1 (by decide) (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101e86 [0x88, 0x44, 0x24, 0x1D] (StorePre 0x101e86 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101e86 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e86 4 0 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101e86 4 0 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_m8_r8_effect_step 0x101e86 0 (by decide) (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101e8a [0x89, 0xD8] (fun s => s.RIP = 0x101e8a) (movR32R32Effect 0x101e8a 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101e8a 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x101e8a 0xd8 (by decide)) pre_rip
  have f19 : InstrSpec 0x101e8c [0xC1, 0xE8, 0x18] (fun s => s.RIP = 0x101e8c) (shrR32Effect 0x101e8c 3 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x101e8c 3 0 24).toInstrSpec (shr_r32_imm8_effect_step 0x101e8c 0xe8 0x18 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e4e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e52) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e55) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e58) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e5b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e5f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e63) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 63), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e67) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e72) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 69), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e76) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e78) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e7b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 77), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e7e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 75), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e82) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 75), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e86) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 75), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e8a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e8c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 79), (3, 57), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e8f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101e4a_1 code

theorem block_l101e4a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e4a :=
  Rest.liftedBlock (rest_l101e4a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e4a x hx)

theorem rest_l101eeb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101eeb bytes_l101eeb) (entryMap (live .l101eeb))
      11 0x101eeb bytes_l101eeb b_l101eeb := by
  have f0 : InstrSpec 0x101eeb [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x101eeb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101eeb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101eeb 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101eeb 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x101eeb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101ef0 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x101ef0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101ef0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ef0 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101ef0 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x101ef0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101ef5 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x101ef5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101ef5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ef5 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101ef5 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x101ef5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101efa [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x101efa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101efa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101efa 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101efa 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101efa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101eff [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x101eff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101eff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101eff 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101eff 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x101eff 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101f04 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x101f04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101f04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101f04 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101f04 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x101f04 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101f09 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x101f09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101f09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101f09 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101f09 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101f09 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101f0e [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x101f0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101f0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101f0e 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101f0e 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101f0e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101f13 [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x101f13) (leaR64Effect 0x101f13 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101f13 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x101f13 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101f18 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x101f18) (leaR64Effect 0x101f18 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101f18 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x101f18 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101f1d [0xE8, 0x7E, 0x15, 0x00, 0x00] (PushPre 0x101f1d 5) (callEffect (fun _ => 0x1034a0) 0x101f22)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101f1d 0x1034a0 0x101f22).toInstrSpec (call_rel32_effect_step 0x101f1d 0x157e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ef0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ef5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101efa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eff) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f04) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f09) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f0e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f13) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f18) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f1d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034a0) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l101eeb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101eeb :=
  Rest.liftedBlock (rest_l101eeb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101eeb x hx)

theorem rest_l101f22_3 [Bindings] (code : CodeMap) :
    Rest (n := 154) code lifted (codeRange 0x101f22 bytes_l101f22) [(0, 127), (1, 125), (2, 145), (3, 151), (4, 152), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x102028 bytes_l101f22_3 b_l101f22_3 := by
  have f60 : InstrSpec 0x102028 [0x41, 0x5C] (PopPre 0x102028) (popR64Effect 0x102028 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102028 2 12).toInstrSpec (pop_r64_rex_effect_step 0x102028 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f61 : InstrSpec 0x10202a [0x41, 0x5D] (PopPre 0x10202a) (popR64Effect 0x10202a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10202a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10202a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f62 : InstrSpec 0x10202c [0x41, 0x5E] (PopPre 0x10202c) (popR64Effect 0x10202c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10202c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10202c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f63 : InstrSpec 0x10202e [0x41, 0x5F] (PopPre 0x10202e) (popR64Effect 0x10202e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10202e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10202e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f64 : InstrSpec 0x102030 [0x5D] (PopPre 0x102030) (popR64Effect 0x102030 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102030 1 5).toInstrSpec (pop_r64_effect_step 0x102030 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f65 : InstrSpec 0x102031 [0xC3] (RetPre 0x102031) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102031).toInstrSpec (ret_effect_step 0x102031) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f60 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 155) f60 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 156) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 155), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10202a) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f61 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 158) f61 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 159) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 158), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10202c) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f62 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 161) f62 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 162) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 161), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10202e) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f63 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 164) f63 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 165) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 164), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102030) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f64 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 167) f64 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 168) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 167), (5, 166), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102031) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f65 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 170) f65 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 171) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 170), (5, 166), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) f65 (by decide) rfl rfl rfl (by decide)

theorem rest_l101f22_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x101f22 bytes_l101f22) [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]
      26 0x101fdb bytes_l101f22_2 b_l101f22_2 := by
  have f40 : InstrSpec 0x101fdb [0x44, 0x88, 0x00] (StorePre 0x101fdb 3 (fun s => AddrMode.addr (.base 0 .none) s (0x101fdb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101fdb 3 8 (.base 0 .none))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101fdb 3 8 (.base 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x101fdb 0x44 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x101fde [0x44, 0x88, 0x50, 0x01] (StorePre 0x101fde 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x101fde + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fde 4 10 (.base 0 (.d8 0x1)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101fde 4 10 (.base 0 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101fde 0x44 (by decide) 2 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x101fe2 [0x44, 0x88, 0x58, 0x02] (StorePre 0x101fe2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x101fe2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fe2 4 11 (.base 0 (.d8 0x2)))
      [.gpr 11, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101fe2 4 11 (.base 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101fe2 0x44 (by decide) 3 (.base 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x101fe6 [0x44, 0x88, 0x78, 0x03] (StorePre 0x101fe6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x101fe6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fe6 4 15 (.base 0 (.d8 0x3)))
      [.gpr 15, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101fe6 4 15 (.base 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101fe6 0x44 (by decide) 7 (.base 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x101fea [0x44, 0x88, 0x60, 0x04] (StorePre 0x101fea 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101fea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fea 4 12 (.base 0 (.d8 0x4)))
      [.gpr 12, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101fea 4 12 (.base 0 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101fea 0x44 (by decide) 4 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x101fee [0x44, 0x88, 0x68, 0x05] (StorePre 0x101fee 4 (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x101fee + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fee 4 13 (.base 0 (.d8 0x5)))
      [.gpr 13, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101fee 4 13 (.base 0 (.d8 0x5))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101fee 0x44 (by decide) 5 (.base 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x101ff2 [0x40, 0x88, 0x68, 0x06] (StorePre 0x101ff2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x101ff2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ff2 4 5 (.base 0 (.d8 0x6)))
      [.gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ff2 4 5 (.base 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101ff2 0x40 (by decide) 5 (.base 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x101ff6 [0x44, 0x88, 0x70, 0x07] (StorePre 0x101ff6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x101ff6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ff6 4 14 (.base 0 (.d8 0x7)))
      [.gpr 14, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ff6 4 14 (.base 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101ff6 0x44 (by decide) 6 (.base 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x101ffa [0x40, 0x88, 0x70, 0x08] (StorePre 0x101ffa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101ffa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ffa 4 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ffa 4 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101ffa 0x40 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x101ffe [0x88, 0x58, 0x09] (StorePre 0x101ffe 3 (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x101ffe + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101ffe 3 3 (.base 0 (.d8 0x9)))
      [.gpr 3, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ffe 3 3 (.base 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x101ffe 3 (by decide) (.base 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x102001 [0x44, 0x88, 0x48, 0x0A] (StorePre 0x102001 4 (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x102001 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x102001 4 9 (.base 0 (.d8 0xa)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x102001 4 9 (.base 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_rex_effect_step 0x102001 0x44 (by decide) 1 (.base 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x102005 [0x40, 0x88, 0x78, 0x0B] (StorePre 0x102005 4 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x102005 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x102005 4 7 (.base 0 (.d8 0xb)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x102005 4 7 (.base 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_rex_effect_step 0x102005 0x40 (by decide) 7 (.base 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x102009 [0x0F, 0xB6, 0x74, 0x24, 0x3E] (LoadPre 0x102009 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x102009 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102009 5 6 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x102009 5 6 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (movzx_r32_m8_effect_step 0x102009 6 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x10200e [0x40, 0x88, 0x70, 0x0C] (StorePre 0x10200e 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x10200e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10200e 4 6 (.base 0 (.d8 0xc)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10200e 4 6 (.base 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10200e 0x40 (by decide) 6 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x102012 [0x88, 0x50, 0x0D] (StorePre 0x102012 3 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x102012 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x102012 3 2 (.base 0 (.d8 0xd)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x102012 3 2 (.base 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_effect_step 0x102012 2 (by decide) (.base 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x102015 [0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x102015 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x102015 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102015 5 2 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x102015 5 2 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x102015 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f56 : InstrSpec 0x10201a [0x88, 0x50, 0x0E] (StorePre 0x10201a 3 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x10201a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10201a 3 2 (.base 0 (.d8 0xe)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10201a 3 2 (.base 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_effect_step 0x10201a 2 (by decide) (.base 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x10201d [0x88, 0x48, 0x0F] (StorePre 0x10201d 3 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x10201d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10201d 3 1 (.base 0 (.d8 0xf)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x10201d 3 1 (.base 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x10201d 1 (by decide) (.base 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f58 : InstrSpec 0x102020 [0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102020) (addR64Imm32Effect 0x102020 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x102020 4 0x88).toInstrSpec (add_r64_imm32_effect_step 0x102020 0x48 0xc4 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x102027 [0x5B] (PopPre 0x102027) (popR64Effect 0x102027 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102027 1 3).toInstrSpec (pop_r64_effect_step 0x102027 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 129) (RestInside.exec (n := 129) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fde) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fe2) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fe6) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.exec (n := 132) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fea) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fee) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.exec (n := 134) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ff2) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 135) (RestInside.exec (n := 135) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ff6) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ffa) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ffe) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102001) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.exec (n := 139) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102005) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102009) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10200e) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102012) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102015) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f55 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10201a) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10201d) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 107), (4, 4), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102020) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f58 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 107), (4, 149), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102027) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f59 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 152) f59 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 153) (ρ' := [(0, 127), (1, 125), (2, 145), (3, 151), (4, 152), (5, 101), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102028) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101f22_3 code

theorem rest_l101f22_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x101f22 bytes_l101f22) [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      46 0x101f8a bytes_l101f22_1 b_l101f22_1 := by
  have f20 : InstrSpec 0x101f8a [0x44, 0x32, 0x50, 0x01] (LoadPre 0x101f8a (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x101f8a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f8a 4 10 (.base 0 (.d8 0x1)))
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101f8a 4 10 (.base 0 (.d8 0x1))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101f8a 0x44 (by decide) 2 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x101f8e [0x44, 0x32, 0x58, 0x02] (LoadPre 0x101f8e (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x101f8e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f8e 4 11 (.base 0 (.d8 0x2)))
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101f8e 4 11 (.base 0 (.d8 0x2))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101f8e 0x44 (by decide) 3 (.base 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x101f92 [0x44, 0x32, 0x78, 0x03] (LoadPre 0x101f92 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x101f92 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f92 4 15 (.base 0 (.d8 0x3)))
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101f92 4 15 (.base 0 (.d8 0x3))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101f92 0x44 (by decide) 7 (.base 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x101f96 [0x44, 0x32, 0x60, 0x04] (LoadPre 0x101f96 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101f96 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f96 4 12 (.base 0 (.d8 0x4)))
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101f96 4 12 (.base 0 (.d8 0x4))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101f96 0x44 (by decide) 4 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x101f9a [0x44, 0x32, 0x68, 0x05] (LoadPre 0x101f9a (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x101f9a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f9a 4 13 (.base 0 (.d8 0x5)))
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101f9a 4 13 (.base 0 (.d8 0x5))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101f9a 0x44 (by decide) 5 (.base 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x101f9e [0x40, 0x32, 0x68, 0x06] (LoadPre 0x101f9e (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x101f9e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f9e 4 5 (.base 0 (.d8 0x6)))
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101f9e 4 5 (.base 0 (.d8 0x6))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101f9e 0x40 (by decide) 5 (.base 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x101fa2 [0x44, 0x32, 0x70, 0x07] (LoadPre 0x101fa2 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x101fa2 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101fa2 4 14 (.base 0 (.d8 0x7)))
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101fa2 4 14 (.base 0 (.d8 0x7))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101fa2 0x44 (by decide) 6 (.base 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x101fa6 [0x40, 0x32, 0x70, 0x08] (LoadPre 0x101fa6 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101fa6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101fa6 4 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101fa6 4 6 (.base 0 (.d8 0x8))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101fa6 0x40 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x101faa [0x32, 0x58, 0x09] (LoadPre 0x101faa (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x101faa + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101faa 3 3 (.base 0 (.d8 0x9)))
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101faa 3 3 (.base 0 (.d8 0x9))).toInstrSpec (xor_r8_m8_effect_step 0x101faa 3 (by decide) (.base 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x101fad [0x44, 0x32, 0x48, 0x0A] (LoadPre 0x101fad (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x101fad + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101fad 4 9 (.base 0 (.d8 0xa)))
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101fad 4 9 (.base 0 (.d8 0xa))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101fad 0x44 (by decide) 1 (.base 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x101fb1 [0x40, 0x32, 0x78, 0x0B] (LoadPre 0x101fb1 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x101fb1 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101fb1 4 7 (.base 0 (.d8 0xb)))
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101fb1 4 7 (.base 0 (.d8 0xb))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101fb1 0x40 (by decide) 7 (.base 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x101fb5 [0x32, 0x50, 0x0C] (LoadPre 0x101fb5 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x101fb5 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101fb5 3 2 (.base 0 (.d8 0xc)))
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101fb5 3 2 (.base 0 (.d8 0xc))).toInstrSpec (xor_r8_m8_effect_step 0x101fb5 2 (by decide) (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x101fb8 [0x88, 0x54, 0x24, 0x3E] (StorePre 0x101fb8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x101fb8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fb8 4 2 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101fb8 4 2 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (mov_m8_r8_effect_step 0x101fb8 2 (by decide) (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x101fbc [0x0F, 0xB6, 0x54, 0x24, 0x0F] (LoadPre 0x101fbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101fbc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101fbc 5 2 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x101fbc 5 2 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x101fbc 2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x101fc1 [0x32, 0x50, 0x0D] (LoadPre 0x101fc1 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x101fc1 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101fc1 3 2 (.base 0 (.d8 0xd)))
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101fc1 3 2 (.base 0 (.d8 0xd))).toInstrSpec (xor_r8_m8_effect_step 0x101fc1 2 (by decide) (.base 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x101fc4 [0x32, 0x48, 0x0E] (LoadPre 0x101fc4 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x101fc4 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101fc4 3 1 (.base 0 (.d8 0xe)))
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101fc4 3 1 (.base 0 (.d8 0xe))).toInstrSpec (xor_r8_m8_effect_step 0x101fc4 1 (by decide) (.base 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x101fc7 [0x88, 0x4C, 0x24, 0x0F] (StorePre 0x101fc7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101fc7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fc7 4 1 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101fc7 4 1 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x101fc7 1 (by decide) (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x101fcb [0x0F, 0xB6, 0x4C, 0x24, 0x3F] (LoadPre 0x101fcb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x101fcb + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101fcb 5 1 (.sib 4 none 0 (.d8 0x3f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101fcb 5 1 (.sib 4 none 0 (.d8 0x3f))).toInstrSpec (movzx_r32_m8_effect_step 0x101fcb 1 (.sib 4 none 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x101fd0 [0x32, 0x48, 0x0F] (LoadPre 0x101fd0 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x101fd0 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101fd0 3 1 (.base 0 (.d8 0xf)))
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101fd0 3 1 (.base 0 (.d8 0xf))).toInstrSpec (xor_r8_m8_effect_step 0x101fd0 1 (by decide) (.base 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x101fd3 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x101fd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101fd3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101fd3 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101fd3 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x101fd3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f8e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f92) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 73), (13, 77), (14, 85), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f96) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 77), (14, 85), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f9a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 85), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f9e) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 101), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 85), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fa2) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 101), (6, 83), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fa6) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 101), (6, 105), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101faa) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 107), (4, 4), (5, 101), (6, 105), (7, 71), (8, 89), (9, 75), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fad) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 107), (4, 4), (5, 101), (6, 105), (7, 71), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fb1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fb5) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 87), (1, 58), (2, 113), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fb8) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 87), (1, 58), (2, 113), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fbc) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 87), (1, 58), (2, 116), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fc1) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 87), (1, 58), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fc4) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 87), (1, 120), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fc7) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.exec (n := 122) (ρ' := [(0, 87), (1, 120), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fcb) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 87), (1, 123), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fd0) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 87), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fd3) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 127), (1, 125), (2, 118), (3, 107), (4, 4), (5, 101), (6, 105), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 97), (13, 99), (14, 103), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101fdb) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101f22_2 code

theorem rest_l101f22 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101f22 bytes_l101f22) (entryMap (live .l101f22))
      66 0x101f22 bytes_l101f22 b_l101f22 := by
  have f0 : InstrSpec 0x101f22 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x4F] (LoadPre 0x101f22 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x101f22 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f22 6 8 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x101f22 6 8 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101f22 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101f28 [0x0F, 0xB6, 0x44, 0x24, 0x40] (LoadPre 0x101f28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101f28 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f28 5 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101f28 5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (movzx_r32_m8_effect_step 0x101f28 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101f2d [0x88, 0x44, 0x24, 0x3F] (StorePre 0x101f2d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x101f2d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101f2d 4 0 (.sib 4 none 0 (.d8 0x3f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101f2d 4 0 (.sib 4 none 0 (.d8 0x3f))).toInstrSpec (mov_m8_r8_effect_step 0x101f2d 0 (by decide) (.sib 4 none 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101f31 [0x0F, 0xB6, 0x4C, 0x24, 0x41] (LoadPre 0x101f31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x101f31 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f31 5 1 (.sib 4 none 0 (.d8 0x41)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101f31 5 1 (.sib 4 none 0 (.d8 0x41))).toInstrSpec (movzx_r32_m8_effect_step 0x101f31 1 (.sib 4 none 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x101f36 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x4E] (LoadPre 0x101f36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x101f36 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f36 6 10 (.sib 4 none 0 (.d8 0x4e)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x101f36 6 10 (.sib 4 none 0 (.d8 0x4e))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101f36 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x4e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101f3c [0x0F, 0xB6, 0x44, 0x24, 0x42] (LoadPre 0x101f3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x101f3c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f3c 5 0 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101f3c 5 0 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (movzx_r32_m8_effect_step 0x101f3c 0 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101f41 [0x88, 0x44, 0x24, 0x0F] (StorePre 0x101f41 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101f41 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101f41 4 0 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101f41 4 0 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x101f41 0 (by decide) (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101f45 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x4D] (LoadPre 0x101f45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x101f45 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f45 6 11 (.sib 4 none 0 (.d8 0x4d)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x101f45 6 11 (.sib 4 none 0 (.d8 0x4d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101f45 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101f4b [0x0F, 0xB6, 0x54, 0x24, 0x43] (LoadPre 0x101f4b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x101f4b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f4b 5 2 (.sib 4 none 0 (.d8 0x43)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x101f4b 5 2 (.sib 4 none 0 (.d8 0x43))).toInstrSpec (movzx_r32_m8_effect_step 0x101f4b 2 (.sib 4 none 0 (.d8 0x43)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x101f50 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x4C] (LoadPre 0x101f50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x101f50 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f50 6 15 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x101f50 6 15 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101f50 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101f56 [0x0F, 0xB6, 0x7C, 0x24, 0x44] (LoadPre 0x101f56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x101f56 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f56 5 7 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x101f56 5 7 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (movzx_r32_m8_effect_step 0x101f56 7 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101f5b [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x4B] (LoadPre 0x101f5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x101f5b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f5b 6 12 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x101f5b 6 12 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101f5b 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101f61 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x45] (LoadPre 0x101f61 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x101f61 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f61 6 9 (.sib 4 none 0 (.d8 0x45)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x101f61 6 9 (.sib 4 none 0 (.d8 0x45))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101f61 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x45)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x101f67 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4A] (LoadPre 0x101f67 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x101f67 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f67 6 13 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x101f67 6 13 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101f67 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101f6d [0x0F, 0xB6, 0x5C, 0x24, 0x46] (LoadPre 0x101f6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x101f6d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f6d 5 3 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x101f6d 5 3 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (movzx_r32_m8_effect_step 0x101f6d 3 (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101f72 [0x0F, 0xB6, 0x6C, 0x24, 0x49] (LoadPre 0x101f72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x101f72 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f72 5 5 (.sib 4 none 0 (.d8 0x49)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x101f72 5 5 (.sib 4 none 0 (.d8 0x49))).toInstrSpec (movzx_r32_m8_effect_step 0x101f72 5 (.sib 4 none 0 (.d8 0x49)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101f77 [0x0F, 0xB6, 0x74, 0x24, 0x47] (LoadPre 0x101f77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x101f77 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f77 5 6 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x101f77 5 6 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (movzx_r32_m8_effect_step 0x101f77 6 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x101f7c [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x48] (LoadPre 0x101f7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101f7c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f7c 6 14 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x101f7c 6 14 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101f7c 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x101f82 [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x101f82 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101f82 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101f82 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101f82 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x101f82 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x101f87 [0x44, 0x32, 0x00] (LoadPre 0x101f87 (fun s => AddrMode.addr (.base 0 .none) s (0x101f87 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101f87 3 8 (.base 0 .none))
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101f87 3 8 (.base 0 .none)).toInstrSpec (xor_r8_m8_rex_effect_step 0x101f87 0x44 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (4, 4), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f31) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 58), (4, 4), (8, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f36) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 58), (4, 4), (8, 53), (10, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f3c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 58), (4, 4), (8, 53), (10, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f41) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 58), (4, 4), (8, 53), (10, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f45) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 58), (4, 4), (8, 53), (10, 60), (11, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f4b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (8, 53), (10, 60), (11, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f50) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (8, 53), (10, 60), (11, 65), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f56) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (7, 71), (8, 53), (10, 60), (11, 65), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f5b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (7, 71), (8, 53), (10, 60), (11, 65), (12, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f61) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f67) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 62), (1, 58), (2, 67), (4, 4), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f6d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 62), (1, 58), (2, 67), (3, 79), (4, 4), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f72) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 62), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f77) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 62), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f7c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 62), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f82) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 53), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f87) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 58), (2, 67), (3, 79), (4, 4), (5, 81), (6, 83), (7, 71), (8, 89), (9, 75), (10, 60), (11, 65), (12, 73), (13, 77), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101f8a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101f22_1 code

theorem block_l101f22 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101f22 :=
  Rest.liftedBlock (rest_l101f22 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101f22 x hx)

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

theorem_by block_l101c20_eval :
    program.runBlock (dialect code) ⟨.l101c20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101c86_eval :
    program.runBlock (dialect code) ⟨.l101c86, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101c93_eval :
    program.runBlock (dialect code) ⟨.l101c93, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101cbb_eval :
    program.runBlock (dialect code) ⟨.l101cbb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101ccc_eval :
    program.runBlock (dialect code) ⟨.l101ccc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d5e_eval :
    program.runBlock (dialect code) ⟨.l101d5e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d72_eval :
    program.runBlock (dialect code) ⟨.l101d72, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d7f_eval :
    program.runBlock (dialect code) ⟨.l101d7f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101da7_eval :
    program.runBlock (dialect code) ⟨.l101da7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101db8_eval :
    program.runBlock (dialect code) ⟨.l101db8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e4a_eval :
    program.runBlock (dialect code) ⟨.l101e4a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101eeb_eval :
    program.runBlock (dialect code) ⟨.l101eeb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101f22_eval :
    program.runBlock (dialect code) ⟨.l101f22, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
