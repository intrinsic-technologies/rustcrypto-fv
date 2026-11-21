import K256.Proofs.Generate.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Generate.LIR.Generated.Values

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

theorem rest_l105f30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105f30 bytes_l105f30) (entryMap (live .l105f30))
      14 0x105f30 bytes_l105f30 b_l105f30 := by
  have f0 : InstrSpec 0x105f30 [0x55] (PushPre 0x105f30 1) (pushR64Effect 0x105f30 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f30 1 5).toInstrSpec (push_r64_effect_step 0x105f30 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x105f31 [0x41, 0x57] (PushPre 0x105f31 2) (pushR64Effect 0x105f31 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f31 2 15).toInstrSpec (push_r64_rex_effect_step 0x105f31 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x105f33 [0x41, 0x56] (PushPre 0x105f33 2) (pushR64Effect 0x105f33 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f33 2 14).toInstrSpec (push_r64_rex_effect_step 0x105f33 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x105f35 [0x41, 0x55] (PushPre 0x105f35 2) (pushR64Effect 0x105f35 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f35 2 13).toInstrSpec (push_r64_rex_effect_step 0x105f35 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x105f37 [0x41, 0x54] (PushPre 0x105f37 2) (pushR64Effect 0x105f37 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f37 2 12).toInstrSpec (push_r64_rex_effect_step 0x105f37 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x105f39 [0x53] (PushPre 0x105f39 1) (pushR64Effect 0x105f39 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f39 1 3).toInstrSpec (push_r64_effect_step 0x105f39 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x105f3a [0x48, 0x81, 0xEC, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105f3a) (subR64Imm32Effect 0x105f3a 4 0x158)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x105f3a 4 0x158).toInstrSpec (sub_r64_imm32_effect_step 0x105f3a 0x48 0xec 0x158 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x105f41 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x105f41) (movR64R64Effect 0x105f41 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x105f41 14 6).toInstrSpec (mov_r64_r64_effect_step 0x105f41 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x105f44 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x105f44 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105f44 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f44 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105f44 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x105f44 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x105f49 [0x48, 0x8B, 0x2E] (LoadPre 0x105f49 (fun s => AddrMode.addr (.base 6 .none) s (0x105f49 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x105f49 5 (.base 6 .none))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x105f49 5 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x105f49 0x48 (by decide) 5 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x105f4c [0x4C, 0x8B, 0x6E, 0x08] (LoadPre 0x105f4c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x105f4c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105f4c 13 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x105f4c 13 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x105f4c 0x4c (by decide) 5 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x105f50 [0x4C, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105f50) (leaR64Effect 0x105f50 15 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x105f50 15 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x105f50 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x105f58 [0x4C, 0x8D, 0x64, 0x24, 0x68] (fun s => s.RIP = 0x105f58) (leaR64Effect 0x105f58 12 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x105f58 12 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x105f58 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f33) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f37) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f39) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f3a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f41) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f44) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f49) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f4c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 72), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f50) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 72), (14, 67), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f58) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 72), (14, 67), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f5d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 78) (jmp_rel32_effect_step 0x105f5d 0xa7 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l105f30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105f30 :=
  Rest.liftedBlock (rest_l105f30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105f30 x hx)

theorem rest_l105f70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105f70 bytes_l105f70) (entryMap (live .l105f70))
      19 0x105f70 bytes_l105f70 b_l105f70 := by
  have f0 : InstrSpec 0x105f70 [0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x105f70 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105f70 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105f70 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105f70 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x105f70 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105f78 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x105f78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105f78 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f78 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105f78 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x105f78 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105f7d [0x48, 0x8B, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x105f7d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105f7d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105f7d 1 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105f7d 1 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x105f7d 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105f85 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x105f85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105f85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f85 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105f85 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x105f85 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105f8a [0x48, 0x8B, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x105f8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105f8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105f8a 2 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x105f8a 2 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x105f8a 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105f92 [0x48, 0x8B, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x105f92 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x105f92 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105f92 6 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x105f92 6 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x105f92 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105f9a [0x48, 0x89, 0x74, 0x24, 0x30] (StorePre 0x105f9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105f9a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f9a 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105f9a 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x105f9a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105f9f [0x48, 0x89, 0x54, 0x24, 0x28] (StorePre 0x105f9f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105f9f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f9f 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105f9f 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x105f9f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105fa4 [0x48, 0x89, 0x54, 0x24, 0x48] (StorePre 0x105fa4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105fa4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105fa4 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105fa4 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x105fa4 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x105fa9 [0x48, 0x89, 0x74, 0x24, 0x50] (StorePre 0x105fa9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x105fa9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105fa9 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105fa9 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x105fa9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x105fae [0x48, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x105fae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x105fae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105fae 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105fae 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x105fae 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x105fb3 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x105fb3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x105fb3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105fb3 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105fb3 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x105fb3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105fb8 [0x48, 0xC7, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105fb8 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105fb8 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105fb8 (.sib 4 none 0 (.d32 0xf8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105fb8 (.sib 4 none 0 (.d32 0xf8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105fb8 0x48 (by decide) (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x105fc4 [0x48, 0xC7, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105fc4 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105fc4 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105fc4 (.sib 4 none 0 (.d32 0xf0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105fc4 (.sib 4 none 0 (.d32 0xf0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105fc4 0x48 (by decide) (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x105fd0 [0x48, 0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105fd0 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x105fd0 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105fd0 (.sib 4 none 0 (.d32 0xe8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105fd0 (.sib 4 none 0 (.d32 0xe8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105fd0 0x48 (by decide) (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x105fdc [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105fdc 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105fdc + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105fdc (.sib 4 none 0 (.d32 0xe0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105fdc (.sib 4 none 0 (.d32 0xe0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105fdc 0x48 (by decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x105fe8 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x105fe8) (leaR64Effect 0x105fe8 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105fe8 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x105fe8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x105fed [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x105fed) (movR64R64Effect 0x105fed 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105fed 6 15).toInstrSpec (mov_r64_r64_effect_step 0x105fed 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x105ff0 [0xE8, 0x8B, 0x42, 0x00, 0x00] (PushPre 0x105ff0 5) (callEffect (fun _ => 0x10a280) 0x105ff5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105ff0 0x10a280 0x105ff5).toInstrSpec (call_rel32_effect_step 0x105ff0 0x428b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f78) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f7d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f8a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f92) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f9a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f9f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fa4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fa9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fae) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fb3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fb8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fc4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fd0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fdc) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fe8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105fed) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 75), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ff0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 77), (5, 5), (6, 75), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l105f70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105f70 :=
  Rest.liftedBlock (rest_l105f70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105f70 x hx)

theorem rest_l105ff5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105ff5 bytes_l105ff5) (entryMap (live .l105ff5))
      4 0x105ff5 bytes_l105ff5 b_l105ff5 := by
  have f0 : InstrSpec 0x105ff5 [0xF6, 0xD0] (fun s => s.RIP = 0x105ff5) (notR8Effect 0x105ff5 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x105ff5 2 0).toInstrSpec (not_r8_effect_step 0x105ff5 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105ff7 [0x24, 0x01] (fun s => s.RIP = 0x105ff7) (andAlImm8Effect 0x105ff7 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x105ff7 0x1).toInstrSpec (and_al_imm8_effect_step 0x105ff7 0x1) pre_rip
  have f2 : InstrSpec 0x105ff9 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x105ff9) (movzxR32R8Effect 0x105ff9 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x105ff9 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x105ff9 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105ffc [0xE8, 0x4F, 0x1D, 0x02, 0x00] (PushPre 0x105ffc 5) (callEffect (fun _ => 0x127d50) 0x106001)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105ffc 0x127d50 0x106001).toInstrSpec (call_rel32_effect_step 0x105ffc 0x21d4f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ff7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ff9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ffc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105ff5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105ff5 :=
  Rest.liftedBlock (rest_l105ff5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105ff5 x hx)

theorem rest_l106001 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106001 bytes_l106001) (entryMap (live .l106001))
      3 0x106001 bytes_l106001 b_l106001 := by
  have f0 : InstrSpec 0x106001 [0x49, 0x83, 0xC5, 0xE0] (fun s => s.RIP = 0x106001) (addR64Imm8Effect 0x106001 13 0xe0)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106001 13 0xe0).toInstrSpec (add_r64_imm8_effect_step 0x106001 0x49 0xc5 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106005 [0x3C, 0x01] (fun s => s.RIP = 0x106005) (cmpAlImm8Effect 0x106005 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x106005 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x106005 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106005) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106007) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x106007 4 0x74) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106001 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106001 :=
  Rest.liftedBlock (rest_l106001 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106001 x hx)

theorem rest_l106009 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106009 bytes_l106009) (entryMap (live .l106009))
      2 0x106009 bytes_l106009 b_l106009 := by
  have f0 : InstrSpec 0x106009 [0x49, 0x83, 0xFD, 0x20] (fun s => s.RIP = 0x106009) (cmpR64Imm8Effect 0x106009 13 0x20)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x106009 13 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x106009 0x49 0xfd 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10600d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x10600d 2 0x69) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106009 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106009 :=
  Rest.liftedBlock (rest_l106009 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106009 x hx)

theorem rest_l10600f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10600f bytes_l10600f) (entryMap (live .l10600f))
      2 0x10600f bytes_l10600f b_l10600f := by
  have f0 : InstrSpec 0x10600f [0x48, 0x83, 0xC5, 0x20] (fun s => s.RIP = 0x10600f) (addR64Imm8Effect 0x10600f 5 0x20)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10600f 5 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10600f 0x48 0xc5 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106013 [0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106013) (fun _ => nopEffect 0x106013 13)
      [] [] [.rip] :=
    (nopEffect_footprint 0x106013 13).toInstrSpec (nop_m_effect_step 0x106013 [0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106013) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106020) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l10600f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10600f :=
  Rest.liftedBlock (rest_l10600f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10600f x hx)

theorem rest_l106020 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106020 bytes_l106020) (entryMap (live .l106020))
      14 0x106020 bytes_l106020 b_l106020 := by
  have f0 : InstrSpec 0x106020 [0x49, 0x8D, 0x5D, 0xE0] (fun s => s.RIP = 0x106020) (leaR64Effect 0x106020 3 (.base 13 (.d8 0xe0)))
      [.gpr 13] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x106020 3 (.base 13 (.d8 0xe0))).toInstrSpec (lea_r64_effect_step 0x106020 0x49 (by decide) 3 (.base 13 (.d8 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106024 [0x49, 0x89, 0x2E] (StorePre 0x106024 3 (fun s => AddrMode.addr (.base 14 .none) s (0x106024 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106024 5 (.base 14 .none))
      [.gpr 5, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x106024 5 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x106024 0x49 (by decide) 5 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106027 [0x49, 0x89, 0x5E, 0x08] (StorePre 0x106027 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x106027 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106027 3 (.base 14 (.d8 0x8)))
      [.gpr 3, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x106027 3 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x106027 0x49 (by decide) 3 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10602b [0x48, 0x8B, 0x45, 0xF8] (LoadPre 0x10602b (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x10602b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10602b 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10602b 0 (.base 5 (.d8 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x10602b 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10602f [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10602f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10602f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10602f 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10602f 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10602f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x106037 [0x48, 0x8B, 0x45, 0xF0] (LoadPre 0x106037 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x106037 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x106037 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x106037 0 (.base 5 (.d8 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x106037 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10603b [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x10603b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10603b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10603b 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10603b 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x10603b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x106040 [0x48, 0x8B, 0x45, 0xE0] (LoadPre 0x106040 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x106040 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x106040 0 (.base 5 (.d8 0xe0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x106040 0 (.base 5 (.d8 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x106040 0x48 (by decide) 0 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x106044 [0x48, 0x8B, 0x4D, 0xE8] (LoadPre 0x106044 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x106044 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x106044 1 (.base 5 (.d8 0xe8)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x106044 1 (.base 5 (.d8 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x106044 0x48 (by decide) 1 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x106048 [0x48, 0x89, 0x4C, 0x24, 0x70] (StorePre 0x106048 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x106048 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106048 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106048 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x106048 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10604d [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x10604d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10604d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10604d 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10604d 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x10604d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x106052 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x106052) (movR64R64Effect 0x106052 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106052 7 15).toInstrSpec (mov_r64_r64_effect_step 0x106052 0x4c 0xff (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x106055 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x106055) (movR64R64Effect 0x106055 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x106055 6 12).toInstrSpec (mov_r64_r64_effect_step 0x106055 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x106058 [0xE8, 0x03, 0x3E, 0x00, 0x00] (PushPre 0x106058 5) (callEffect (fun _ => 0x109e60) 0x10605d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106058 0x109e60 0x10605d).toInstrSpec (call_rel32_effect_step 0x106058 0x3e03 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106024) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106027) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10602b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10602f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106037) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10603b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106040) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106044) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 65), (2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106048) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 65), (2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10604d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 65), (2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106052) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 65), (2, 2), (3, 53), (4, 4), (5, 5), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106055) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 63), (1, 65), (2, 2), (3, 53), (4, 4), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106058) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 63), (1, 65), (2, 2), (3, 53), (4, 73), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e60) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l106020 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106020 :=
  Rest.liftedBlock (rest_l106020 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106020 x hx)

theorem rest_l10605d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10605d bytes_l10605d) (entryMap (live .l10605d))
      2 0x10605d bytes_l10605d b_l10605d := by
  have f0 : InstrSpec 0x10605d [0x80, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x01] (LoadPre 0x10605d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10605d + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x10605d 8 (.sib 4 none 0 (.d32 0x100)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10605d 8 (.sib 4 none 0 (.d32 0x100)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x10605d (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106065) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x106065 4 0xffffff05) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10605d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10605d :=
  Rest.liftedBlock (rest_l10605d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10605d x hx)

theorem rest_l10606b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10606b bytes_l10606b) (entryMap (live .l10606b))
      4 0x10606b bytes_l10606b b_l10606b := by
  have f0 : InstrSpec 0x10606b [0x48, 0x83, 0xC5, 0x20] (fun s => s.RIP = 0x10606b) (addR64Imm8Effect 0x10606b 5 0x20)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10606b 5 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10606b 0x48 0xc5 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10606f [0x49, 0x89, 0xDD] (fun s => s.RIP = 0x10606f) (movR64R64Effect 0x10606f 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10606f 13 3).toInstrSpec (mov_r64_r64_effect_step 0x10606f 0x49 0xdd (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106072 [0x48, 0x83, 0xFB, 0x20] (fun s => s.RIP = 0x106072) (cmpR64Imm8Effect 0x106072 3 0x20)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x106072 3 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x106072 0x48 0xfb 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10606f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106072) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106076) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x106076 3 0xa8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10606b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10606b :=
  Rest.liftedBlock (rest_l10606b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10606b x hx)

theorem rest_l106078 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106078 bytes_l106078) (entryMap (live .l106078))
      1 0x106078 bytes_l106078 b_l106078 := by
  have f0 : InstrSpec 0x106078 [0xE8, 0xB3, 0xA9, 0xFF, 0xFF] (PushPre 0x106078 5) (callEffect (fun _ => 0x100a30) 0x10607d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106078 0x100a30 0x10607d).toInstrSpec (call_rel32_effect_step 0x106078 0xffffa9b3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l106078 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106078 :=
  Rest.liftedBlock (rest_l106078 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106078 x hx)

theorem rest_l10607d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10607d bytes_l10607d) (entryMap (live .l10607d))
      12 0x10607d bytes_l10607d b_l10607d := by
  have f0 : InstrSpec 0x10607d [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x10607d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10607d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10607d 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10607d 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10607d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106082 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x106082 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106082 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106082 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106082 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x106082 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106087 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x106087 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106087 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106087 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x106087 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x106087 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10608c [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10608c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10608c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10608c 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10608c 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10608c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106091 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x106091 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106091 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106091 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x106091 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x106091 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x106096 [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x106096 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106096 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106096 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x106096 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x106096 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10609b [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x10609b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10609b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10609b 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10609b 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10609b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1060a0 [0x48, 0x89, 0x04, 0x24] (StorePre 0x1060a0 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1060a0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1060a0 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060a0 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1060a0 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1060a4 [0x4C, 0x8D, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1060a4) (leaR64Effect 0x1060a4 14 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x1060a4 14 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x1060a4 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1060ac [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x1060ac) (movR64R64Effect 0x1060ac 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1060ac 6 4).toInstrSpec (mov_r64_r64_effect_step 0x1060ac 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1060af [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1060af) (movR64R64Effect 0x1060af 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1060af 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1060af 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1060b2 [0xE8, 0xC9, 0x8D, 0x00, 0x00] (PushPre 0x1060b2 5) (callEffect (fun _ => 0x10ee80) 0x1060b7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1060b2 0x10ee80 0x1060b7).toInstrSpec (call_rel32_effect_step 0x1060b2 0x8dc9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106082) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106087) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10608c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106091) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106096) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10609b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060a0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060a4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060ac) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060af) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060b2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 71), (5, 5), (6, 67), (7, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee80) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l10607d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10607d :=
  Rest.liftedBlock (rest_l10607d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10607d x hx)

theorem rest_l1060b7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1060b7 bytes_l1060b7) (entryMap (live .l1060b7))
      3 0x1060b7 bytes_l1060b7 b_l1060b7 := by
  have f0 : InstrSpec 0x1060b7 [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1060b7) (leaR64Effect 0x1060b7 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1060b7 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x1060b7 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1060bf [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1060bf) (movR64R64Effect 0x1060bf 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1060bf 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1060bf 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1060c2 [0xE8, 0x89, 0x9D, 0x00, 0x00] (PushPre 0x1060c2 5) (callEffect (fun _ => 0x10fe50) 0x1060c7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1060c2 0x10fe50 0x1060c7).toInstrSpec (call_rel32_effect_step 0x1060c2 0x9d89 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060bf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060c2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1060b7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1060b7 :=
  Rest.liftedBlock (rest_l1060b7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1060b7 x hx)

theorem rest_l1060c7_1 [Bindings] (code : CodeMap) :
    Rest (n := 97) code lifted (codeRange 0x1060c7 bytes_l1060c7) [(0, 69), (1, 75), (2, 2), (3, 79), (4, 95), (5, 94), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x106117 bytes_l1060c7_1 b_l1060c7_1 := by
  have f20 : InstrSpec 0x106117 [0xC3] (RetPre 0x106117) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106117).toInstrSpec (ret_effect_step 0x106117) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f20 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 98) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 99) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 98), (5, 94), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) f20 (by decide) rfl rfl rfl (by decide)

theorem rest_l1060c7 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1060c7 bytes_l1060c7) (entryMap (live .l1060c7))
      21 0x1060c7 bytes_l1060c7 b_l1060c7 := by
  have f0 : InstrSpec 0x1060c7 [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x1060c7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1060c7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1060c7 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1060c7 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1060c7 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1060cb [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1060cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1060cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060cb 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1060cb 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1060cb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1060d0 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x1060d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1060d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060d0 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060d0 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1060d0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1060d5 [0x48, 0x89, 0x4C, 0x24, 0x70] (StorePre 0x1060d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1060d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060d5 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060d5 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1060d5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1060da [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1060da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1060da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060da 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1060da 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1060da 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1060df [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x1060df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1060df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060df 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060df 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1060df 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1060e4 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1060e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1060e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060e4 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1060e4 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1060e4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1060e9 [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1060e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1060e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1060e9 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1060e9 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1060e9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1060f1 [0x48, 0x8D, 0x74, 0x24, 0x68] (fun s => s.RIP = 0x1060f1) (leaR64Effect 0x1060f1 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1060f1 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x1060f1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1060f6 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1060f6) (movR32Imm32Effect 0x1060f6 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1060f6 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1060f6 0xb9 (by decide) 0xf) pre_rip
  have f10 : InstrSpec 0x1060fb [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1060fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1060fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060fb 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1060fb 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1060fb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x106100 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x106100) (movR64R64Effect 0x106100 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106100 7 0).toInstrSpec (mov_r64_r64_effect_step 0x106100 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x106103 [0xF3, 0x48, 0xA5] (RepPre 0x106103 (RepMovsqPre 0x106103)) (repMovsqEffect 0x106103)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x106103).toInstrSpecOfRuns (rep_movsq_runs hstride 0x106103 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x106106 [0x48, 0x81, 0xC4, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x106106) (addR64Imm32Effect 0x106106 4 0x158)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x106106 4 0x158).toInstrSpec (add_r64_imm32_effect_step 0x106106 0x48 0xc4 0x158 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10610d [0x5B] (PopPre 0x10610d) (popR64Effect 0x10610d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10610d 1 3).toInstrSpec (pop_r64_effect_step 0x10610d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x10610e [0x41, 0x5C] (PopPre 0x10610e) (popR64Effect 0x10610e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10610e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10610e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f16 : InstrSpec 0x106110 [0x41, 0x5D] (PopPre 0x106110) (popR64Effect 0x106110 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106110 2 13).toInstrSpec (pop_r64_rex_effect_step 0x106110 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f17 : InstrSpec 0x106112 [0x41, 0x5E] (PopPre 0x106112) (popR64Effect 0x106112 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106112 2 14).toInstrSpec (pop_r64_rex_effect_step 0x106112 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f18 : InstrSpec 0x106114 [0x41, 0x5F] (PopPre 0x106114) (popR64Effect 0x106114 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106114 2 15).toInstrSpec (pop_r64_rex_effect_step 0x106114 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f19 : InstrSpec 0x106116 [0x5D] (PopPre 0x106116) (popR64Effect 0x106116 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106116 1 5).toInstrSpec (pop_r64_effect_step 0x106116 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060cb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060d0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060d5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060da) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060df) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060e4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060e9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060f1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 55), (2, 2), (4, 4), (6, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060f6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 67), (2, 2), (4, 4), (6, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1060fb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 67), (2, 2), (4, 4), (6, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106100) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 67), (2, 2), (4, 4), (6, 65), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106103) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 75), (2, 2), (4, 4), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106106) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 75), (2, 2), (4, 77), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10610d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 80), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10610e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 83), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106110) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 86), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106112) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 89) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 89), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106114) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 92), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106116) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f19 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 96) (ρ' := [(0, 69), (1, 75), (2, 2), (3, 79), (4, 95), (5, 94), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106117) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1060c7_1 code

theorem block_l1060c7 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1060c7 :=
  Rest.liftedBlock (rest_l1060c7 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1060c7 x hx)

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

theorem_by block_l105f30_eval :
    program.runBlock (dialect code) ⟨.l105f30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105f70_eval :
    program.runBlock (dialect code) ⟨.l105f70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105ff5_eval :
    program.runBlock (dialect code) ⟨.l105ff5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106001_eval :
    program.runBlock (dialect code) ⟨.l106001, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106009_eval :
    program.runBlock (dialect code) ⟨.l106009, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10600f_eval :
    program.runBlock (dialect code) ⟨.l10600f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106020_eval :
    program.runBlock (dialect code) ⟨.l106020, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10605d_eval :
    program.runBlock (dialect code) ⟨.l10605d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10606b_eval :
    program.runBlock (dialect code) ⟨.l10606b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106078_eval :
    program.runBlock (dialect code) ⟨.l106078, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10607d_eval :
    program.runBlock (dialect code) ⟨.l10607d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1060b7_eval :
    program.runBlock (dialect code) ⟨.l1060b7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1060c7_eval :
    program.runBlock (dialect code) ⟨.l1060c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
