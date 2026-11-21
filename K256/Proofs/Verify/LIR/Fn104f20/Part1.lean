import K256.Proofs.Generate.LIR.CallPre
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

theorem rest_l104f20_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x104f20 bytes_l104f20) [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x104f77 bytes_l104f20_1 b_l104f20_1 := by
  have f20 : InstrSpec 0x104f77 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104f77 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104f77 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104f77 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104f77 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104f77 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x104f80 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104f80 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104f80 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104f80 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104f80 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104f80 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x104f89 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104f89 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104f89 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104f89 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104f89 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104f89 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x104f92 [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104f92) (leaR64Effect 0x104f92 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104f92 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x104f92 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x104f9a [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x104f9a) (leaR64Effect 0x104f9a 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104f9a 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x104f9a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x104f9f [0xE8, 0xDC, 0x52, 0x00, 0x00] (PushPre 0x104f9f 5) (callEffect (fun _ => 0x10a280) 0x104fa4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104f9f 0x10a280 0x104fa4).toInstrSpec (call_rel32_effect_step 0x104f9f 0x52dc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f80) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f89) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f92) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f9a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 93), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f9f) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 95), (5, 5), (6, 93), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f25 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 97) (by decide) (by decide) rfl rfl

theorem rest_l104f20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104f20 bytes_l104f20) (entryMap (live .l104f20))
      26 0x104f20 bytes_l104f20 b_l104f20 := by
  have f0 : InstrSpec 0x104f20 [0x41, 0x57] (PushPre 0x104f20 2) (pushR64Effect 0x104f20 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104f20 2 15).toInstrSpec (push_r64_rex_effect_step 0x104f20 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x104f22 [0x41, 0x56] (PushPre 0x104f22 2) (pushR64Effect 0x104f22 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104f22 2 14).toInstrSpec (push_r64_rex_effect_step 0x104f22 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x104f24 [0x41, 0x55] (PushPre 0x104f24 2) (pushR64Effect 0x104f24 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104f24 2 13).toInstrSpec (push_r64_rex_effect_step 0x104f24 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x104f26 [0x41, 0x54] (PushPre 0x104f26 2) (pushR64Effect 0x104f26 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104f26 2 12).toInstrSpec (push_r64_rex_effect_step 0x104f26 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x104f28 [0x53] (PushPre 0x104f28 1) (pushR64Effect 0x104f28 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104f28 1 3).toInstrSpec (push_r64_effect_step 0x104f28 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x104f29 [0x48, 0x81, 0xEC, 0xC0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104f29) (subR64Imm32Effect 0x104f29 4 0x1c0)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x104f29 4 0x1c0).toInstrSpec (sub_r64_imm32_effect_step 0x104f29 0x48 0xec 0x1c0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104f30 [0x4D, 0x89, 0xC7] (fun s => s.RIP = 0x104f30) (movR64R64Effect 0x104f30 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x104f30 15 8).toInstrSpec (mov_r64_r64_effect_step 0x104f30 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104f33 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x104f33) (movR64R64Effect 0x104f33 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x104f33 13 1).toInstrSpec (mov_r64_r64_effect_step 0x104f33 0x49 0xcd (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104f36 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x104f36) (movR64R64Effect 0x104f36 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x104f36 12 2).toInstrSpec (mov_r64_r64_effect_step 0x104f36 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x104f39 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x104f39) (movR64R64Effect 0x104f39 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x104f39 14 6).toInstrSpec (mov_r64_r64_effect_step 0x104f39 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x104f3c [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x104f3c) (movR64R64Effect 0x104f3c 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x104f3c 3 7).toInstrSpec (mov_r64_r64_effect_step 0x104f3c 0x48 0xfb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x104f3f [0x49, 0x8B, 0x40, 0x18] (LoadPre 0x104f3f (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x104f3f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104f3f 0 (.base 8 (.d8 0x18)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104f3f 0 (.base 8 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104f3f 0x49 (by decide) 0 (.base 8 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x104f43 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x104f43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104f43 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104f43 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104f43 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x104f43 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x104f4b [0x49, 0x8B, 0x40, 0x10] (LoadPre 0x104f4b (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x104f4b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104f4b 0 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104f4b 0 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104f4b 0x49 (by decide) 0 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x104f4f [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x104f4f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x104f4f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104f4f 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104f4f 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x104f4f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x104f57 [0x49, 0x8B, 0x00] (LoadPre 0x104f57 (fun s => AddrMode.addr (.base 8 .none) s (0x104f57 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104f57 0 (.base 8 .none))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104f57 0 (.base 8 .none)).toInstrSpec (mov_r64_m64_effect_step 0x104f57 0x49 (by decide) 0 (.base 8 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x104f5a [0x49, 0x8B, 0x48, 0x08] (LoadPre 0x104f5a (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x104f5a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104f5a 1 (.base 8 (.d8 0x8)))
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104f5a 1 (.base 8 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104f5a 0x49 (by decide) 1 (.base 8 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x104f5e [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x104f5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x104f5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104f5e 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104f5e 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x104f5e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x104f66 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x104f66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x104f66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104f66 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104f66 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x104f66 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x104f6e [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104f6e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104f6e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104f6e (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104f6e (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104f6e 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f22) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f24) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f26) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f28) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f29) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f30) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f33) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f36) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f39) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f3c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f3f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f43) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f4b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f4f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f57) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f5a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f5e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f66) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f6e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f77) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l104f20_1 code

theorem block_l104f20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104f20 :=
  Rest.liftedBlock (rest_l104f20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104f20 x hx)

theorem rest_l104fa4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104fa4 bytes_l104fa4) (entryMap (live .l104fa4))
      4 0x104fa4 bytes_l104fa4 b_l104fa4 := by
  have f0 : InstrSpec 0x104fa4 [0xF6, 0xD0] (fun s => s.RIP = 0x104fa4) (notR8Effect 0x104fa4 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x104fa4 2 0).toInstrSpec (not_r8_effect_step 0x104fa4 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104fa6 [0x24, 0x01] (fun s => s.RIP = 0x104fa6) (andAlImm8Effect 0x104fa6 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x104fa6 0x1).toInstrSpec (and_al_imm8_effect_step 0x104fa6 0x1) pre_rip
  have f2 : InstrSpec 0x104fa8 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x104fa8) (movzxR32R8Effect 0x104fa8 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x104fa8 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x104fa8 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104fab [0xE8, 0xA0, 0x2D, 0x02, 0x00] (PushPre 0x104fab 5) (callEffect (fun _ => 0x127d50) 0x104fb0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104fab 0x127d50 0x104fb0).toInstrSpec (call_rel32_effect_step 0x104fab 0x22da0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fa6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fa8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l104fa4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104fa4 :=
  Rest.liftedBlock (rest_l104fa4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104fa4 x hx)

theorem rest_l104fb0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104fb0 bytes_l104fb0) (entryMap (live .l104fb0))
      3 0x104fb0 bytes_l104fb0 b_l104fb0 := by
  have f0 : InstrSpec 0x104fb0 [0x88, 0x44, 0x24, 0x08] (StorePre 0x104fb0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104fb0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x104fb0 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x104fb0 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x104fb0 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104fb4 [0x3C, 0x01] (fun s => s.RIP = 0x104fb4) (cmpAlImm8Effect 0x104fb4 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x104fb4 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x104fb4 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fb4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fb6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x104fb6 5 0x3d7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104fb0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104fb0 :=
  Rest.liftedBlock (rest_l104fb0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104fb0 x hx)

theorem rest_l104fbc_1 [Bindings] (code : CodeMap) :
    Rest (n := 81) code lifted (codeRange 0x104fbc bytes_l104fbc) [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x10503f bytes_l104fbc_1 b_l104fbc_1 := by
  have f20 : InstrSpec 0x10503f [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10503f) (leaR64Effect 0x10503f 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10503f 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x10503f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x105047 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x105047) (leaR64Effect 0x105047 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105047 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105047 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10504c [0xE8, 0x2F, 0x52, 0x00, 0x00] (PushPre 0x10504c 5) (callEffect (fun _ => 0x10a280) 0x105051)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10504c 0x10a280 0x105051).toInstrSpec (call_rel32_effect_step 0x10504c 0x522f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105047) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (6, 83), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10504c) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 85), (5, 5), (6, 83), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f22 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 87) (by decide) (by decide) rfl rfl

theorem rest_l104fbc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104fbc bytes_l104fbc) (entryMap (live .l104fbc))
      23 0x104fbc bytes_l104fbc b_l104fbc := by
  have f0 : InstrSpec 0x104fbc [0x49, 0x8B, 0x07] (LoadPre 0x104fbc (fun s => AddrMode.addr (.base 15 .none) s (0x104fbc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104fbc 0 (.base 15 .none))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104fbc 0 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x104fbc 0x49 (by decide) 0 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104fbf [0x49, 0x8B, 0x4F, 0x08] (LoadPre 0x104fbf (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x104fbf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104fbf 1 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104fbf 1 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104fbf 0x49 (by decide) 1 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104fc3 [0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x104fc3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x104fc3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fc3 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104fc3 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x104fc3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104fcb [0x48, 0x89, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x104fcb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x104fcb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fcb 1 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104fcb 1 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x104fcb 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104fd3 [0x49, 0x8B, 0x47, 0x10] (LoadPre 0x104fd3 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x104fd3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104fd3 0 (.base 15 (.d8 0x10)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104fd3 0 (.base 15 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104fd3 0x49 (by decide) 0 (.base 15 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x104fd7 [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x104fd7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x104fd7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fd7 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104fd7 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x104fd7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x104fdf [0x49, 0x8B, 0x47, 0x18] (LoadPre 0x104fdf (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x104fdf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104fdf 0 (.base 15 (.d8 0x18)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104fdf 0 (.base 15 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104fdf 0x49 (by decide) 0 (.base 15 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x104fe3 [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x104fe3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x104fe3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fe3 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104fe3 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x104fe3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104feb [0x49, 0x8B, 0x47, 0x38] (LoadPre 0x104feb (fun s => AddrMode.addr (.base 15 (.d8 0x38)) s (0x104feb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104feb 0 (.base 15 (.d8 0x38)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104feb 0 (.base 15 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x104feb 0x49 (by decide) 0 (.base 15 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x104fef [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x104fef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104fef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fef 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104fef 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x104fef 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x104ff7 [0x49, 0x8B, 0x47, 0x30] (LoadPre 0x104ff7 (fun s => AddrMode.addr (.base 15 (.d8 0x30)) s (0x104ff7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104ff7 0 (.base 15 (.d8 0x30)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104ff7 0 (.base 15 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x104ff7 0x49 (by decide) 0 (.base 15 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x104ffb [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x104ffb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x104ffb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104ffb 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104ffb 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x104ffb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105003 [0x49, 0x8B, 0x47, 0x20] (LoadPre 0x105003 (fun s => AddrMode.addr (.base 15 (.d8 0x20)) s (0x105003 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105003 0 (.base 15 (.d8 0x20)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105003 0 (.base 15 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x105003 0x49 (by decide) 0 (.base 15 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x105007 [0x49, 0x8B, 0x4F, 0x28] (LoadPre 0x105007 (fun s => AddrMode.addr (.base 15 (.d8 0x28)) s (0x105007 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105007 1 (.base 15 (.d8 0x28)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105007 1 (.base 15 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x105007 0x49 (by decide) 1 (.base 15 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10500b [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x10500b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10500b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10500b 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10500b 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x10500b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x105013 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x105013 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105013 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105013 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105013 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x105013 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10501b [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10501b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10501b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10501b (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10501b (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10501b 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x105024 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105024 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105024 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105024 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105024 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105024 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10502d [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10502d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10502d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10502d (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10502d (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10502d 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x105036 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105036 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105036 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105036 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105036 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105036 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fbf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fc3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fcb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fd3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fd7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fdf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fe3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104feb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fef) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ff7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ffb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105003) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105007) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10500b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105013) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10501b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105024) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10502d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105036) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10503f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l104fbc_1 code

theorem block_l104fbc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104fbc :=
  Rest.liftedBlock (rest_l104fbc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104fbc x hx)

theorem rest_l105051 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105051 bytes_l105051) (entryMap (live .l105051))
      4 0x105051 bytes_l105051 b_l105051 := by
  have f0 : InstrSpec 0x105051 [0xF6, 0xD0] (fun s => s.RIP = 0x105051) (notR8Effect 0x105051 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x105051 2 0).toInstrSpec (not_r8_effect_step 0x105051 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105053 [0x24, 0x01] (fun s => s.RIP = 0x105053) (andAlImm8Effect 0x105053 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x105053 0x1).toInstrSpec (and_al_imm8_effect_step 0x105053 0x1) pre_rip
  have f2 : InstrSpec 0x105055 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x105055) (movzxR32R8Effect 0x105055 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x105055 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x105055 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105058 [0xE8, 0xF3, 0x2C, 0x02, 0x00] (PushPre 0x105058 5) (callEffect (fun _ => 0x127d50) 0x10505d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105058 0x127d50 0x10505d).toInstrSpec (call_rel32_effect_step 0x105058 0x22cf3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105053) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105055) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105058) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105051 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105051 :=
  Rest.liftedBlock (rest_l105051 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105051 x hx)

theorem rest_l10505d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10505d bytes_l10505d) (entryMap (live .l10505d))
      3 0x10505d bytes_l10505d b_l10505d := by
  have f0 : InstrSpec 0x10505d [0x88, 0x44, 0x24, 0x08] (StorePre 0x10505d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10505d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10505d 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10505d 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x10505d 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105061 [0x3C, 0x01] (fun s => s.RIP = 0x105061) (cmpAlImm8Effect 0x105061 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x105061 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x105061 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105061) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105063) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x105063 5 0x32a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10505d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10505d :=
  Rest.liftedBlock (rest_l10505d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10505d x hx)

theorem rest_l105069 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105069 bytes_l105069) (entryMap (live .l105069))
      11 0x105069 bytes_l105069 b_l105069 := by
  have f0 : InstrSpec 0x105069 [0x49, 0x8D, 0x47, 0x20] (fun s => s.RIP = 0x105069) (leaR64Effect 0x105069 0 (.base 15 (.d8 0x20)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x105069 0 (.base 15 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x105069 0x49 (by decide) 0 (.base 15 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10506d [0x48, 0x8B, 0x08] (LoadPre 0x10506d (fun s => AddrMode.addr (.base 0 .none) s (0x10506d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10506d 1 (.base 0 .none))
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10506d 1 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10506d 0x48 (by decide) 1 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x105070 [0x48, 0x8B, 0x50, 0x08] (LoadPre 0x105070 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x105070 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105070 2 (.base 0 (.d8 0x8)))
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x105070 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x105070 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105074 [0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x105074 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105074 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105074 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105074 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x105074 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10507c [0x48, 0x89, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x10507c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10507c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10507c 2 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10507c 2 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x10507c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x105084 [0x48, 0x8B, 0x48, 0x10] (LoadPre 0x105084 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x105084 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105084 1 (.base 0 (.d8 0x10)))
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105084 1 (.base 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x105084 0x48 (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105088 [0x48, 0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x105088 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105088 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105088 1 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105088 1 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x105088 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105090 [0x48, 0x8B, 0x40, 0x18] (LoadPre 0x105090 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x105090 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105090 0 (.base 0 (.d8 0x18)))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105090 0 (.base 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x105090 0x48 (by decide) 0 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x105094 [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x105094 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105094 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105094 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105094 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x105094 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10509c [0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10509c) (leaR64Effect 0x10509c 7 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10509c 7 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x10509c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1050a4 [0xE8, 0xC7, 0x50, 0x00, 0x00] (PushPre 0x1050a4 5) (callEffect (fun _ => 0x10a170) 0x1050a9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1050a4 0x10a170 0x1050a9).toInstrSpec (call_rel32_effect_step 0x1050a4 0x50c7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10506d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105070) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105074) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10507c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105084) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105088) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105090) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105094) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10509c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 61), (2, 57), (3, 3), (4, 4), (5, 5), (7, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050a4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 61), (2, 57), (3, 3), (4, 69), (5, 5), (7, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a170) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l105069 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105069 :=
  Rest.liftedBlock (rest_l105069 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105069 x hx)

theorem rest_l1050a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1050a9 bytes_l1050a9) (entryMap (live .l1050a9))
      2 0x1050a9 bytes_l1050a9 b_l1050a9 := by
  have f0 : InstrSpec 0x1050a9 [0x84, 0xC0] (fun s => s.RIP = 0x1050a9) (testR8R8Effect 0x1050a9 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1050a9 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1050a9 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1050ab 4 0x14) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1050a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1050a9 :=
  Rest.liftedBlock (rest_l1050a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1050a9 x hx)

theorem rest_l1050ad [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1050ad bytes_l1050ad) (entryMap (live .l1050ad))
      3 0x1050ad bytes_l1050ad b_l1050ad := by
  have f0 : InstrSpec 0x1050ad [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1050ad 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1050ad + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1050ad (.base 3 (.d8 0x8)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1050ad (.base 3 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1050ad 0x48 (by decide) (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1050b5 [0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1050b5 7 (fun s => AddrMode.addr (.base 3 .none) s (0x1050b5 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x1050b5 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1050b5 (.base 3 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x1050b5 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050b5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050bc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1050bc 0x2be (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1050ad [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1050ad :=
  Rest.liftedBlock (rest_l1050ad code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1050ad x hx)

theorem rest_l1050c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1050c1 bytes_l1050c1) (entryMap (live .l1050c1))
      18 0x1050c1 bytes_l1050c1 b_l1050c1 := by
  have f0 : InstrSpec 0x1050c1 [0xC6, 0x44, 0x24, 0x08, 0x01] (StorePre 0x1050c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1050c1 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1050c1 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1050c1 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1050c1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1050c6 [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x1050c6) (leaR64Effect 0x1050c6 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1050c6 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1050c6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1050cb [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x1050cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1050cb + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1050cb (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1050cb (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1050cb (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1050d0 [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x1050d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1050d0 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1050d0 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1050d0 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1050d0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1050d5 [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x1050d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1050d5 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1050d5 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1050d5 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1050d5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1050da [0x49, 0x83, 0xFD, 0x20] (fun s => s.RIP = 0x1050da) (cmpR64Imm8Effect 0x1050da 13 0x20)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1050da 13 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x1050da 0x49 0xfd 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1050de [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1050de) (movR32Imm32Effect 0x1050de 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1050de 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x1050de 0xbe (by decide) 0x20) pre_rip
  have f7 : InstrSpec 0x1050e3 [0x49, 0x0F, 0x42, 0xF5] (fun s => s.RIP = 0x1050e3) (atFlags (condHolds 2) (cmovR64R64Effect 0x1050e3 4 6 13))
      [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x1050e3 4 6 13 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1050e3 2 0x49 (by decide) 0xf5 (by decide) c)) pre_rip
  have f8 : InstrSpec 0x1050e7 [0xC7, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00] (StorePre 0x1050e7 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1050e7 + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x1050e7 11 (.sib 4 none 0 (.d32 0x140)) 0x100)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1050e7 11 (.sib 4 none 0 (.d32 0x140)) 0x100).toInstrSpec (mov_m32_imm32_effect_step 0x1050e7 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide) 0x100) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1050f2 [0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1050f2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1050f2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1050f2 (.sib 4 none 0 (.d32 0xa0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1050f2 (.sib 4 none 0 (.d32 0xa0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1050f2 0x48 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1050fe [0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1050fe 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1050fe + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1050fe (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1050fe (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1050fe 0x48 (by decide) (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10510a [0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10510a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10510a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10510a (.sib 4 none 0 (.d32 0x90)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10510a (.sib 4 none 0 (.d32 0x90)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10510a 0x48 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105116 [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105116 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105116 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105116 (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105116 (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105116 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x105122 [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105122) (leaR64Effect 0x105122 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x105122 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x105122 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10512a [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10512a) (movR32Imm32Effect 0x10512a 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10512a 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10512a 0xb9 (by decide) 0x4) pre_rip
  have f15 : InstrSpec 0x10512f [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10512f) (movR64R64Effect 0x10512f 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10512f 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10512f 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x105132 [0x41, 0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105132) (movR32Imm32Effect 0x105132 6 8 0x100)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x105132 6 8 0x100).toInstrSpec (mov_r32_imm32_rex_effect_step 0x105132 0x41 0xb8 (by decide) (by decide) 0x100) pre_rip
  have f17 : InstrSpec 0x105138 [0xE8, 0x33, 0x2C, 0x02, 0x00] (PushPre 0x105138 5) (callEffect (fun _ => 0x127d70) 0x10513d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105138 0x127d70 0x10513d).toInstrSpec (call_rel32_effect_step 0x105138 0x22c33 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050c6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050cb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050d0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050d5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050da) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050de) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050e3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050e7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050f2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050fe) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10510a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105116) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105122) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 54), (2, 70), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10512a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 54), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10512f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 54), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 63), (7, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105132) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 54), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 63), (7, 74), (8, 76), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105138) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 54), (1, 72), (2, 70), (3, 3), (4, 78), (5, 5), (6, 63), (7, 74), (8, 76), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f17 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l1050c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1050c1 :=
  Rest.liftedBlock (rest_l1050c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1050c1 x hx)

theorem rest_l10513d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10513d bytes_l10513d) (entryMap (live .l10513d))
      2 0x10513d bytes_l10513d b_l10513d := by
  have f0 : InstrSpec 0x10513d [0x3C, 0xFF] (fun s => s.RIP = 0x10513d) (cmpAlImm8Effect 0x10513d 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x10513d 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x10513d 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10513f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10513f 5 0x26a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10513d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10513d :=
  Rest.liftedBlock (rest_l10513d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10513d x hx)

theorem rest_l105145 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105145 bytes_l105145) (entryMap (live .l105145))
      11 0x105145 bytes_l105145 b_l105145 := by
  have f0 : InstrSpec 0x105145 [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x105145 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x105145 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105145 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105145 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x105145 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10514d [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10514d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10514d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10514d 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10514d 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10514d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105152 [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x105152 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x105152 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105152 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105152 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x105152 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10515a [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x10515a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10515a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10515a 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10515a 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10515a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10515f [0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10515f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10515f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10515f 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10515f 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x10515f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105167 [0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x105167 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105167 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105167 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105167 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x105167 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10516f [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x10516f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10516f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10516f 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10516f 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10516f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105174 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x105174 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105174 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105174 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105174 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x105174 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105179 [0x48, 0x8D, 0xBC, 0x24, 0x60, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105179) (leaR64Effect 0x105179 7 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105179 7 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (lea_r64_effect_step 0x105179 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x105181 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x105181) (leaR64Effect 0x105181 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105181 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105181 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x105186 [0xE8, 0xF5, 0x4D, 0x00, 0x00] (PushPre 0x105186 5) (callEffect (fun _ => 0x109f80) 0x10518b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105186 0x109f80 0x10518b).toInstrSpec (call_rel32_effect_step 0x105186 0x4df5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10514d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105152) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10515a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10515f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105167) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10516f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105174) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105179) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105181) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105186) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f80) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l105145 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105145 :=
  Rest.liftedBlock (rest_l105145 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105145 x hx)

theorem rest_l10518b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10518b bytes_l10518b) (entryMap (live .l10518b))
      3 0x10518b bytes_l10518b b_l10518b := by
  have f0 : InstrSpec 0x10518b [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x10518b) (leaR64Effect 0x10518b 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10518b 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10518b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105190 [0x48, 0x8D, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105190) (leaR64Effect 0x105190 6 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105190 6 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x105190 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105198 [0xE8, 0x23, 0x4F, 0x00, 0x00] (PushPre 0x105198 5) (callEffect (fun _ => 0x10a0c0) 0x10519d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105198 0x10a0c0 0x10519d).toInstrSpec (call_rel32_effect_step 0x105198 0x4f23 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105190) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105198) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0c0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10518b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10518b :=
  Rest.liftedBlock (rest_l10518b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10518b x hx)

theorem rest_l10519d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10519d bytes_l10519d) (entryMap (live .l10519d))
      4 0x10519d bytes_l10519d b_l10519d := by
  have f0 : InstrSpec 0x10519d [0x0F, 0xB6, 0x44, 0x24, 0x28] (LoadPre 0x10519d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10519d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10519d 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10519d 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x10519d 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1051a2 [0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1051a2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1051a2 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1051a2 7 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1051a2 7 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m8_r8_effect_step 0x1051a2 0 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1051a9 [0x3C, 0x01] (fun s => s.RIP = 0x1051a9) (cmpAlImm8Effect 0x1051a9 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1051a9 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x1051a9 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x1051ab 5 0x21a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10519d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10519d :=
  Rest.liftedBlock (rest_l10519d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10519d x hx)

theorem rest_l1051b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1051b1 bytes_l1051b1) (entryMap (live .l1051b1))
      17 0x1051b1 bytes_l1051b1 b_l1051b1 := by
  have f0 : InstrSpec 0x1051b1 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1051b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1051b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1051b1 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1051b1 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1051b1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1051b6 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x1051b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1051b6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1051b6 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1051b6 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1051b6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1051bb [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x1051bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1051bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1051bb 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1051bb 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x1051bb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1051c3 [0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x1051c3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1051c3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1051c3 1 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1051c3 1 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x1051c3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1051cb [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x1051cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1051cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1051cb 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1051cb 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1051cb 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1051d0 [0x48, 0x89, 0x94, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x1051d0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1051d0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1051d0 2 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1051d0 2 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x1051d0 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1051d8 [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x1051d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1051d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1051d8 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1051d8 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1051d8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1051dd [0x48, 0x89, 0xB4, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x1051dd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1051dd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1051dd 6 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1051dd 6 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x1051dd 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1051e5 [0x48, 0x89, 0x74, 0x24, 0x20] (StorePre 0x1051e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1051e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1051e5 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1051e5 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1051e5 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1051ea [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x1051ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1051ea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1051ea 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1051ea 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1051ea 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1051ef [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x1051ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1051ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1051ef 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1051ef 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1051ef 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1051f4 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x1051f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1051f4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1051f4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1051f4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1051f4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1051f9 [0x4C, 0x8D, 0xA4, 0x24, 0x80, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1051f9) (leaR64Effect 0x1051f9 12 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x1051f9 12 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (lea_r64_effect_step 0x1051f9 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x105201 [0x48, 0x8D, 0xB4, 0x24, 0x60, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105201) (leaR64Effect 0x105201 6 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105201 6 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (lea_r64_effect_step 0x105201 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x105209 [0x48, 0x8D, 0x54, 0x24, 0x08] (fun s => s.RIP = 0x105209) (leaR64Effect 0x105209 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x105209 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105209 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10520e [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10520e) (movR64R64Effect 0x10520e 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10520e 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10520e 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x105211 [0xE8, 0x4A, 0x4D, 0x00, 0x00] (PushPre 0x105211 5) (callEffect (fun _ => 0x109f60) 0x105216)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105211 0x109f60 0x105216).toInstrSpec (call_rel32_effect_step 0x105211 0x4d4a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051b6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051bb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051cb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051d0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051d8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051dd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051e5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051ea) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051ef) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051f4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051f9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105201) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 71), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105209) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 55), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10520e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 55), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 75), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105211) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 55), (2, 73), (3, 3), (4, 77), (5, 5), (6, 71), (7, 75), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f60) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l1051b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1051b1 :=
  Rest.liftedBlock (rest_l1051b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1051b1 x hx)

theorem rest_l105216 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105216 bytes_l105216) (entryMap (live .l105216))
      13 0x105216 bytes_l105216 b_l105216 := by
  have f0 : InstrSpec 0x105216 [0x49, 0x8B, 0x47, 0x18] (LoadPre 0x105216 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x105216 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105216 0 (.base 15 (.d8 0x18)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105216 0 (.base 15 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x105216 0x49 (by decide) 0 (.base 15 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10521a [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10521a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10521a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10521a 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10521a 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10521a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10521f [0x49, 0x8B, 0x47, 0x10] (LoadPre 0x10521f (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x10521f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10521f 0 (.base 15 (.d8 0x10)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10521f 0 (.base 15 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10521f 0x49 (by decide) 0 (.base 15 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105223 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x105223 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105223 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105223 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105223 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x105223 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105228 [0x49, 0x8B, 0x07] (LoadPre 0x105228 (fun s => AddrMode.addr (.base 15 .none) s (0x105228 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x105228 0 (.base 15 .none))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105228 0 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x105228 0x49 (by decide) 0 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10522b [0x49, 0x8B, 0x4F, 0x08] (LoadPre 0x10522b (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x10522b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10522b 1 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10522b 1 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10522b 0x49 (by decide) 1 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10522f [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x10522f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10522f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10522f 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10522f 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10522f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105234 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x105234 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105234 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105234 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105234 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x105234 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105239 [0x4C, 0x8D, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105239) (leaR64Effect 0x105239 15 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x105239 15 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (lea_r64_effect_step 0x105239 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x105241 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x105241) (leaR64Effect 0x105241 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105241 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105241 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x105246 [0x48, 0x8D, 0x94, 0x24, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105246) (leaR64Effect 0x105246 2 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x105246 2 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (lea_r64_effect_step 0x105246 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10524e [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10524e) (movR64R64Effect 0x10524e 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10524e 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10524e 0x4c 0xff (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x105251 [0xE8, 0x0A, 0x4D, 0x00, 0x00] (PushPre 0x105251 5) (callEffect (fun _ => 0x109f60) 0x105256)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105251 0x109f60 0x105256).toInstrSpec (call_rel32_effect_step 0x105251 0x4d0a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10521a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10521f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105223) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105228) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10522b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10522f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105234) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105239) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105241) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105246) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10524e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105251) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 73), (5, 5), (6, 67), (7, 71), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f60) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l105216 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105216 :=
  Rest.liftedBlock (rest_l105216 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105216 x hx)

theorem rest_l105256 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105256 bytes_l105256) (entryMap (live .l105256))
      6 0x105256 bytes_l105256 b_l105256 := by
  have f0 : InstrSpec 0x105256 [0x4C, 0x8D, 0x6C, 0x24, 0x08] (fun s => s.RIP = 0x105256) (leaR64Effect 0x105256 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x105256 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105256 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10525b [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x10525b) (movR64R64Effect 0x10525b 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10525b 7 13).toInstrSpec (mov_r64_r64_effect_step 0x10525b 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10525e [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10525e) (movR64R64Effect 0x10525e 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10525e 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10525e 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105261 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x105261) (movR64R64Effect 0x105261 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105261 2 15).toInstrSpec (mov_r64_r64_effect_step 0x105261 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x105264 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x105264) (movR64R64Effect 0x105264 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x105264 1 14).toInstrSpec (mov_r64_r64_effect_step 0x105264 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x105267 [0xE8, 0xB4, 0xA8, 0x00, 0x00] (PushPre 0x105267 5) (callEffect (fun _ => 0x10fb20) 0x10526c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105267 0x10fb20 0x10526c).toInstrSpec (call_rel32_effect_step 0x105267 0xa8b4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10525b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10525e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105261) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105264) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105267) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb20) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l105256 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105256 :=
  Rest.liftedBlock (rest_l105256 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105256 x hx)

theorem rest_l10526c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10526c bytes_l10526c) (entryMap (live .l10526c))
      4 0x10526c bytes_l10526c b_l10526c := by
  have f0 : InstrSpec 0x10526c [0x4C, 0x8D, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10526c) (leaR64Effect 0x10526c 14 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10526c 14 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x10526c 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105274 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x105274) (movR64R64Effect 0x105274 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105274 7 14).toInstrSpec (mov_r64_r64_effect_step 0x105274 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105277 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x105277) (movR64R64Effect 0x105277 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105277 6 13).toInstrSpec (mov_r64_r64_effect_step 0x105277 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10527a [0xE8, 0xD1, 0xAB, 0x00, 0x00] (PushPre 0x10527a 5) (callEffect (fun _ => 0x10fe50) 0x10527f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10527a 0x10fe50 0x10527f).toInstrSpec (call_rel32_effect_step 0x10527a 0xabd1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105274) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105277) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10527a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10526c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10526c :=
  Rest.liftedBlock (rest_l10526c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10526c x hx)

theorem rest_l10527f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10527f bytes_l10527f) (entryMap (live .l10527f))
      4 0x10527f bytes_l10527f b_l10527f := by
  have f0 : InstrSpec 0x10527f [0x4C, 0x8D, 0xBC, 0x24, 0x40, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10527f) (leaR64Effect 0x10527f 15 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10527f 15 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (lea_r64_effect_step 0x10527f 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105287 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x105287) (movR64R64Effect 0x105287 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105287 7 15).toInstrSpec (mov_r64_r64_effect_step 0x105287 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10528a [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10528a) (movR64R64Effect 0x10528a 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10528a 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10528a 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10528d [0xE8, 0xBE, 0xB0, 0x01, 0x00] (PushPre 0x10528d 5) (callEffect (fun _ => 0x120350) 0x105292)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10528d 0x120350 0x105292).toInstrSpec (call_rel32_effect_step 0x10528d 0x1b0be (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105287) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10528a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10528d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120350) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10527f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10527f :=
  Rest.liftedBlock (rest_l10527f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10527f x hx)

theorem rest_l105292 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105292 bytes_l105292) (entryMap (live .l105292))
      16 0x105292 bytes_l105292 b_l105292 := by
  have f0 : InstrSpec 0x105292 [0xC6, 0x44, 0x24, 0x08, 0x01] (StorePre 0x105292 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105292 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105292 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105292 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x105292 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105297 [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x105297) (leaR64Effect 0x105297 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x105297 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105297 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10529c [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x10529c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10529c + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10529c (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10529c (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10529c (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1052a1 [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x1052a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1052a1 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1052a1 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1052a1 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1052a1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1052a6 [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x1052a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1052a6 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1052a6 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1052a6 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1052a6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1052ab [0xC7, 0x84, 0x24, 0x84, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00] (StorePre 0x1052ab 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x1052ab + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x1052ab 11 (.sib 4 none 0 (.d32 0x84)) 0x100)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1052ab 11 (.sib 4 none 0 (.d32 0x84)) 0x100).toInstrSpec (mov_m32_imm32_effect_step 0x1052ab (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide) 0x100) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1052b6 [0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1052b6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1052b6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1052b6 (.sib 4 none 0 (.d32 0xa0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1052b6 (.sib 4 none 0 (.d32 0xa0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1052b6 0x48 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1052c2 [0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1052c2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1052c2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1052c2 (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1052c2 (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1052c2 0x48 (by decide) (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1052ce [0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1052ce 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1052ce + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1052ce (.sib 4 none 0 (.d32 0x90)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1052ce (.sib 4 none 0 (.d32 0x90)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1052ce 0x48 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1052da [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1052da 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1052da + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1052da (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1052da (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1052da 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1052e6 [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1052e6) (leaR64Effect 0x1052e6 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1052e6 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x1052e6 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1052ee [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1052ee) (movR32Imm32Effect 0x1052ee 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1052ee 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x1052ee 0xbe (by decide) 0x20) pre_rip
  have f12 : InstrSpec 0x1052f3 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1052f3) (movR32Imm32Effect 0x1052f3 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1052f3 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x1052f3 0xb9 (by decide) 0x4) pre_rip
  have f13 : InstrSpec 0x1052f8 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x1052f8) (movR64R64Effect 0x1052f8 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1052f8 7 15).toInstrSpec (mov_r64_r64_effect_step 0x1052f8 0x4c 0xff (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1052fb [0x41, 0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1052fb) (movR32Imm32Effect 0x1052fb 6 8 0x100)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x1052fb 6 8 0x100).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1052fb 0x41 0xb8 (by decide) (by decide) 0x100) pre_rip
  have f15 : InstrSpec 0x105301 [0xE8, 0x6A, 0x2A, 0x02, 0x00] (PushPre 0x105301 5) (callEffect (fun _ => 0x127d70) 0x105306)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105301 0x127d70 0x105306).toInstrSpec (call_rel32_effect_step 0x105301 0x22a6a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105297) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10529c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052a6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052ab) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052b6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052c2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052ce) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052da) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052e6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 54), (2, 64), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052ee) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 54), (2, 64), (3, 3), (4, 4), (5, 5), (6, 66), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052f3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 68), (2, 64), (3, 3), (4, 4), (5, 5), (6, 66), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052f8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 54), (1, 68), (2, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052fb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 54), (1, 68), (2, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 70), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105301) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 54), (1, 68), (2, 64), (3, 3), (4, 74), (5, 5), (6, 66), (7, 70), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 76) (by decide) (by decide) rfl rfl

theorem block_l105292 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105292 :=
  Rest.liftedBlock (rest_l105292 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105292 x hx)

theorem rest_l105306 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105306 bytes_l105306) (entryMap (live .l105306))
      2 0x105306 bytes_l105306 b_l105306 := by
  have f0 : InstrSpec 0x105306 [0x3C, 0xFF] (fun s => s.RIP = 0x105306) (cmpAlImm8Effect 0x105306 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x105306 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x105306 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105308) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x105308 5 0xc7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105306 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105306 :=
  Rest.liftedBlock (rest_l105306 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105306 x hx)

theorem rest_l10530e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10530e bytes_l10530e) (entryMap (live .l10530e))
      12 0x10530e bytes_l10530e b_l10530e := by
  have f0 : InstrSpec 0x10530e [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x10530e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10530e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10530e 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10530e 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x10530e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105316 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x105316 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105316 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105316 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105316 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x105316 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10531b [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x10531b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10531b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10531b 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10531b 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x10531b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105323 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x105323 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105323 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105323 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105323 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x105323 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105328 [0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x105328 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105328 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105328 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105328 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x105328 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105330 [0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x105330 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105330 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105330 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105330 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x105330 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105338 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x105338 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105338 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105338 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105338 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x105338 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10533d [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10533d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10533d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10533d 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10533d 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10533d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105342 [0x4C, 0x8D, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105342) (leaR64Effect 0x105342 14 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x105342 14 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x105342 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10534a [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x10534a) (leaR64Effect 0x10534a 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10534a 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10534a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10534f [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10534f) (movR64R64Effect 0x10534f 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10534f 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10534f 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x105352 [0xE8, 0x29, 0x4C, 0x00, 0x00] (PushPre 0x105352 5) (callEffect (fun _ => 0x109f80) 0x105357)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105352 0x109f80 0x105357).toInstrSpec (call_rel32_effect_step 0x105352 0x4c29 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105316) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10531b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105323) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105328) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105330) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105338) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10533d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105342) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10534a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10534f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105352) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 71), (5, 5), (6, 67), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f80) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l10530e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10530e :=
  Rest.liftedBlock (rest_l10530e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10530e x hx)

theorem rest_l105357 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105357 bytes_l105357) (entryMap (live .l105357))
      3 0x105357 bytes_l105357 b_l105357 := by
  have f0 : InstrSpec 0x105357 [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105357) (leaR64Effect 0x105357 7 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105357 7 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x105357 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10535f [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10535f) (movR64R64Effect 0x10535f 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10535f 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10535f 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105362 [0xE8, 0x39, 0x4F, 0x00, 0x00] (PushPre 0x105362 5) (callEffect (fun _ => 0x10a2a0) 0x105367)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105362 0x10a2a0 0x105367).toInstrSpec (call_rel32_effect_step 0x105362 0x4f39 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10535f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105362) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2a0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l105357 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105357 :=
  Rest.liftedBlock (rest_l105357 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105357 x hx)

theorem rest_l105367 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105367 bytes_l105367) (entryMap (live .l105367))
      2 0x105367 bytes_l105367 b_l105367 := by
  have f0 : InstrSpec 0x105367 [0x84, 0xC0] (fun s => s.RIP = 0x105367) (testR8R8Effect 0x105367 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x105367 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x105367 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105369) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x105369 4 0x4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105367 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105367 :=
  Rest.liftedBlock (rest_l105367 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105367 x hx)

theorem rest_l10536b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10536b bytes_l10536b) (entryMap (live .l10536b))
      2 0x10536b bytes_l10536b b_l10536b := by
  have f0 : InstrSpec 0x10536b [0x31, 0xC0] (fun s => s.RIP = 0x10536b) (xorR32R32Effect 0x10536b 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10536b 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10536b 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10536d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x10536d 0xd (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10536b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10536b :=
  Rest.liftedBlock (rest_l10536b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10536b x hx)

theorem rest_l10536f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10536f bytes_l10536f) (entryMap (live .l10536f))
      2 0x10536f bytes_l10536f b_l10536f := by
  have f0 : InstrSpec 0x10536f [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10536f 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10536f + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10536f (.base 3 (.d8 0x8)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10536f (.base 3 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10536f 0x48 (by decide) (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105377 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105377) (movR32Imm32Effect 0x105377 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x105377 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x105377 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105377) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10537c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l10536f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10536f :=
  Rest.liftedBlock (rest_l10536f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10536f x hx)

theorem rest_l10537c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10537c bytes_l10537c) (entryMap (live .l10537c))
      1 0x10537c bytes_l10537c b_l10537c := by
  have f0 : InstrSpec 0x10537c [0x48, 0x89, 0x03] (StorePre 0x10537c 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10537c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10537c 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10537c 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10537c 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10537f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l10537c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10537c :=
  Rest.liftedBlock (rest_l10537c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10537c x hx)

theorem rest_l10537f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10537f bytes_l10537f) (entryMap (live .l10537f))
      8 0x10537f bytes_l10537f b_l10537f := by
  have f0 : InstrSpec 0x10537f [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10537f) (movR64R64Effect 0x10537f 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10537f 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10537f 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105382 [0x48, 0x81, 0xC4, 0xC0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105382) (addR64Imm32Effect 0x105382 4 0x1c0)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x105382 4 0x1c0).toInstrSpec (add_r64_imm32_effect_step 0x105382 0x48 0xc4 0x1c0 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105389 [0x5B] (PopPre 0x105389) (popR64Effect 0x105389 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x105389 1 3).toInstrSpec (pop_r64_effect_step 0x105389 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10538a [0x41, 0x5C] (PopPre 0x10538a) (popR64Effect 0x10538a 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10538a 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10538a 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10538c [0x41, 0x5D] (PopPre 0x10538c) (popR64Effect 0x10538c 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10538c 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10538c 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10538e [0x41, 0x5E] (PopPre 0x10538e) (popR64Effect 0x10538e 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10538e 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10538e 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x105390 [0x41, 0x5F] (PopPre 0x105390) (popR64Effect 0x105390 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x105390 2 15).toInstrSpec (pop_r64_rex_effect_step 0x105390 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x105392 [0xC3] (RetPre 0x105392) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x105392).toInstrSpec (ret_effect_step 0x105392) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105382) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105389) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10538a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10538c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10538e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105390) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105392) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l10537f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10537f :=
  Rest.liftedBlock (rest_l10537f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10537f x hx)

theorem rest_l105393 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105393 bytes_l105393) (entryMap (live .l105393))
      1 0x105393 bytes_l105393 b_l105393 := by
  have f0 : InstrSpec 0x105393 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x105393) (leaR64Effect 0x105393 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105393 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105393 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)]) (p' := 0x105398) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l105393 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105393 :=
  Rest.liftedBlock (rest_l105393 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105393 x hx)

theorem rest_l105398 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105398 bytes_l105398) (entryMap (live .l105398))
      5 0x105398 bytes_l105398 b_l105398 := by
  have f0 : InstrSpec 0x105398 [0x31, 0xFF] (fun s => s.RIP = 0x105398) (xorR32R32Effect 0x105398 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105398 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x105398 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x10539a [0x48, 0xC7, 0xC2, 0xE8, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x10539a) (movR64Imm32Effect 0x10539a 2 0x2022e8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10539a 2 0x2022e8).toInstrSpec (mov_r64_imm32_effect_step 0x10539a 0x48 0xc2 (by decide) (by decide) (by decide) 0x2022e8) pre_rip
  have f2 : InstrSpec 0x1053a1 [0x31, 0xC9] (fun s => s.RIP = 0x1053a1) (xorR32R32Effect 0x1053a1 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053a1 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1053a1 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x1053a3 [0x49, 0xC7, 0xC1, 0xF0, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x1053a3) (movR64Imm32Effect 0x1053a3 9 0x2022f0)
      [] [] [.reg 9, .rip] :=
    (movR64Imm32Effect_footprint 0x1053a3 9 0x2022f0).toInstrSpec (mov_r64_imm32_effect_step 0x1053a3 0x49 0xc1 (by decide) (by decide) (by decide) 0x2022f0) pre_rip
  have f4 : InstrSpec 0x1053aa [0xE8, 0x59, 0x00, 0x01, 0x00] (PushPre 0x1053aa 5) (callEffect (fun _ => 0x115408) 0x1053af)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1053aa 0x115408 0x1053af).toInstrSpec (call_rel32_effect_step 0x1053aa 0x10059 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x10539a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x1053a1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x1053a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59)]) (p' := 0x1053aa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 57), (2, 55), (4, 61), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59)]) (p' := 0x115408) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l105398 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105398 :=
  Rest.liftedBlock (rest_l105398 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105398 x hx)

theorem rest_l1053af [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1053af bytes_l1053af) (entryMap (live .l1053af))
      4 0x1053af bytes_l1053af b_l1053af := by
  have f0 : InstrSpec 0x1053af [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00] (StorePre 0x1053af 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1053af + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053af (.sib 4 none 0 (.d8 0x8)) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1053af (.sib 4 none 0 (.d8 0x8)) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x1053af 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1053b8 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x1053b8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1053b8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053b8 (.sib 4 none 0 (.d8 0x10)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1053b8 (.sib 4 none 0 (.d8 0x10)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x1053b8 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1053c1 [0x48, 0x8D, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1053c1) (leaR64Effect 0x1053c1 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1053c1 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (lea_r64_effect_step 0x1053c1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1053b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1053c1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x1053c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x1053c9 0x24 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1053af [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1053af :=
  Rest.liftedBlock (rest_l1053af code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1053af x hx)

theorem rest_l1053cb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1053cb bytes_l1053cb) (entryMap (live .l1053cb))
      2 0x1053cb bytes_l1053cb b_l1053cb := by
  have f0 : InstrSpec 0x1053cb [0x48, 0x8D, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1053cb) (leaR64Effect 0x1053cb 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1053cb 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x1053cb 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)]) (p' := 0x1053d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1053d3 0xc3 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1053cb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1053cb :=
  Rest.liftedBlock (rest_l1053cb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1053cb x hx)

theorem rest_l1053d5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1053d5 bytes_l1053d5) (entryMap (live .l1053d5))
      3 0x1053d5 bytes_l1053d5 b_l1053d5 := by
  have f0 : InstrSpec 0x1053d5 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00] (StorePre 0x1053d5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1053d5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053d5 (.sib 4 none 0 (.d8 0x8)) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1053d5 (.sib 4 none 0 (.d8 0x8)) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x1053d5 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1053de [0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x1053de 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1053de + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053de (.sib 4 none 0 (.d8 0x10)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1053de (.sib 4 none 0 (.d8 0x10)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x1053de 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1053e7 [0x48, 0x8D, 0x84, 0x24, 0x84, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1053e7) (leaR64Effect 0x1053e7 0 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1053e7 0 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (lea_r64_effect_step 0x1053e7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1053de) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1053e7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x1053ef) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l1053d5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1053d5 :=
  Rest.liftedBlock (rest_l1053d5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1053d5 x hx)

theorem rest_l1053ef [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1053ef bytes_l1053ef) (entryMap (live .l1053ef))
      6 0x1053ef bytes_l1053ef b_l1053ef := by
  have f0 : InstrSpec 0x1053ef [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x1053ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1053ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1053ef 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1053ef 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1053ef 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1053f4 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x1053f4 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1053f4 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053f4 (.sib 4 none 0 (.d8 0x20)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1053f4 (.sib 4 none 0 (.d8 0x20)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x1053f4 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1053fd [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x1053fd) (leaR64Effect 0x1053fd 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1053fd 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1053fd 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105402 [0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00] (fun s => s.RIP = 0x105402) (movR64Imm32Effect 0x105402 7 0x20028f)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x105402 7 0x20028f).toInstrSpec (mov_r64_imm32_effect_step 0x105402 0x48 0xc7 (by decide) (by decide) (by decide) 0x20028f) pre_rip
  have f4 : InstrSpec 0x105409 [0x48, 0xC7, 0xC2, 0x18, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x105409) (movR64Imm32Effect 0x105409 2 0x202518)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x105409 2 0x202518).toInstrSpec (mov_r64_imm32_effect_step 0x105409 0x48 0xc2 (by decide) (by decide) (by decide) 0x202518) pre_rip
  have f5 : InstrSpec 0x105410 [0xE8, 0x5B, 0x43, 0x02, 0x00] (PushPre 0x105410 5) (callEffect (fun _ => 0x129770) 0x105415)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105410 0x129770 0x105415).toInstrSpec (call_rel32_effect_step 0x105410 0x2435b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (4, 4), (5, 5)]) (p' := 0x1053f4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5)]) (p' := 0x1053fd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 55)]) (p' := 0x105402) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 55), (7, 57)]) (p' := 0x105409) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (4, 4), (5, 5), (6, 55), (7, 57)]) (p' := 0x105410) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (4, 61), (5, 5), (6, 55), (7, 57)]) (p' := 0x129770) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1053ef [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1053ef :=
  Rest.liftedBlock (rest_l1053ef code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1053ef x hx)

theorem rest_l105415_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x105415 bytes_l105415) [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x105495 bytes_l105415_1 b_l105415_1 := by
  have f20 : InstrSpec 0x105495 [0xC6, 0x84, 0x24, 0x27, 0x02, 0x00, 0x00, 0x00] (StorePre 0x105495 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x105495 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x105495 (.sib 4 none 0 (.d32 0x227)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105495 (.sib 4 none 0 (.d32 0x227)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x105495 (.sib 4 none 0 (.d32 0x227)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10549d [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x10549d) (testR64R64Effect 0x10549d 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10549d 1 1).toInstrSpec (test_r64_r64_effect_step 0x10549d 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10549d) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f21 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054a0) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 87) (jcc_rel32_effect_step 0x1054a0 4 0x119) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l105415 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105415 bytes_l105415) (entryMap (live .l105415))
      23 0x105415 bytes_l105415 b_l105415 := by
  have f0 : InstrSpec 0x105415 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105415) (fun _ => nopEffect 0x105415 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x105415 10).toInstrSpec (nop_m_effect_step 0x105415 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10541f [0x90] (fun s => s.RIP = 0x10541f) (fun _ => nopEffect 0x10541f 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10541f 1).toInstrSpec (nop_effect_step 0x10541f) pre_rip
  have f2 : InstrSpec 0x105420 [0x55] (PushPre 0x105420 1) (pushR64Effect 0x105420 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105420 1 5).toInstrSpec (push_r64_effect_step 0x105420 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x105421 [0x41, 0x57] (PushPre 0x105421 2) (pushR64Effect 0x105421 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105421 2 15).toInstrSpec (push_r64_rex_effect_step 0x105421 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x105423 [0x41, 0x56] (PushPre 0x105423 2) (pushR64Effect 0x105423 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105423 2 14).toInstrSpec (push_r64_rex_effect_step 0x105423 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x105425 [0x41, 0x55] (PushPre 0x105425 2) (pushR64Effect 0x105425 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105425 2 13).toInstrSpec (push_r64_rex_effect_step 0x105425 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x105427 [0x41, 0x54] (PushPre 0x105427 2) (pushR64Effect 0x105427 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105427 2 12).toInstrSpec (push_r64_rex_effect_step 0x105427 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x105429 [0x53] (PushPre 0x105429 1) (pushR64Effect 0x105429 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105429 1 3).toInstrSpec (push_r64_effect_step 0x105429 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10542a [0x48, 0x81, 0xEC, 0xF8, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10542a) (subR64Imm32Effect 0x10542a 4 0x2f8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10542a 4 0x2f8).toInstrSpec (sub_r64_imm32_effect_step 0x10542a 0x48 0xec 0x2f8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x105431 [0x48, 0x89, 0xB4, 0x24, 0x58, 0x01, 0x00, 0x00] (StorePre 0x105431 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x105431 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105431 6 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105431 6 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_m64_r64_effect_step 0x105431 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x105439 [0x48, 0x89, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00] (StorePre 0x105439 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x105439 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105439 7 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105439 7 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_m64_r64_effect_step 0x105439 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x105441 [0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B] (fun s => s.RIP = 0x105441) (movR64Imm64Effect 0x105441 0 0x5be0cd191f83d9ab)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x105441 0 0x5be0cd191f83d9ab).toInstrSpec (mov_r64_imm64_effect_step 0x105441 0x48 0xb8 (by decide) (by decide) 0x5be0cd191f83d9ab) pre_rip
  have f12 : InstrSpec 0x10544b [0x48, 0x89, 0x84, 0x24, 0x40, 0x02, 0x00, 0x00] (StorePre 0x10544b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x240)) s (0x10544b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10544b 0 (.sib 4 none 0 (.d32 0x240)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10544b 0 (.sib 4 none 0 (.d32 0x240))).toInstrSpec (mov_m64_r64_effect_step 0x10544b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x240)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x105453 [0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B] (fun s => s.RIP = 0x105453) (movR64Imm64Effect 0x105453 0 0x9b05688c510e527f)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x105453 0 0x9b05688c510e527f).toInstrSpec (mov_r64_imm64_effect_step 0x105453 0x48 0xb8 (by decide) (by decide) 0x9b05688c510e527f) pre_rip
  have f14 : InstrSpec 0x10545d [0x48, 0x89, 0x84, 0x24, 0x38, 0x02, 0x00, 0x00] (StorePre 0x10545d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x238)) s (0x10545d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10545d 0 (.sib 4 none 0 (.d32 0x238)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10545d 0 (.sib 4 none 0 (.d32 0x238))).toInstrSpec (mov_m64_r64_effect_step 0x10545d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x238)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x105465 [0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5] (fun s => s.RIP = 0x105465) (movR64Imm64Effect 0x105465 0 0xa54ff53a3c6ef372)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x105465 0 0xa54ff53a3c6ef372).toInstrSpec (mov_r64_imm64_effect_step 0x105465 0x48 0xb8 (by decide) (by decide) 0xa54ff53a3c6ef372) pre_rip
  have f16 : InstrSpec 0x10546f [0x48, 0x89, 0x84, 0x24, 0x30, 0x02, 0x00, 0x00] (StorePre 0x10546f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x230)) s (0x10546f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10546f 0 (.sib 4 none 0 (.d32 0x230)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10546f 0 (.sib 4 none 0 (.d32 0x230))).toInstrSpec (mov_m64_r64_effect_step 0x10546f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x230)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x105477 [0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB] (fun s => s.RIP = 0x105477) (movR64Imm64Effect 0x105477 0 0xbb67ae856a09e667)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x105477 0 0xbb67ae856a09e667).toInstrSpec (mov_r64_imm64_effect_step 0x105477 0x48 0xb8 (by decide) (by decide) 0xbb67ae856a09e667) pre_rip
  have f18 : InstrSpec 0x105481 [0x48, 0x89, 0x84, 0x24, 0x28, 0x02, 0x00, 0x00] (StorePre 0x105481 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x105481 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105481 0 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105481 0 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (mov_m64_r64_effect_step 0x105481 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x105489 [0x48, 0xC7, 0x84, 0x24, 0x48, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105489 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x105489 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105489 (.sib 4 none 0 (.d32 0x248)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105489 (.sib 4 none 0 (.d32 0x248)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105489 0x48 (by decide) (.sib 4 none 0 (.d32 0x248)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10541f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105420) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105421) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105423) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105425) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105427) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105429) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10542a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105431) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105439) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105441) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10544b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105453) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10545d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105465) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10546f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105477) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105481) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105489) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105495) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l105415_1 code

theorem block_l105415 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105415 :=
  Rest.liftedBlock (rest_l105415 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105415 x hx)

theorem rest_l1054a6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1054a6 bytes_l1054a6) (entryMap (live .l1054a6))
      6 0x1054a6 bytes_l1054a6 b_l1054a6 := by
  have f0 : InstrSpec 0x1054a6 [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x1054a6) (movR64R64Effect 0x1054a6 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1054a6 3 1).toInstrSpec (mov_r64_r64_effect_step 0x1054a6 0x48 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1054a9 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x1054a9) (movR64R64Effect 0x1054a9 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1054a9 14 2).toInstrSpec (mov_r64_r64_effect_step 0x1054a9 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1054ac [0x48, 0xC1, 0xE3, 0x04] (fun s => s.RIP = 0x1054ac) (shlR64Effect 0x1054ac 4 3 4)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x1054ac 4 3 4).toInstrSpec (shl_r64_imm8_effect_step 0x1054ac 0x48 0xe3 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1054b0 [0x48, 0x01, 0xD3] (fun s => s.RIP = 0x1054b0) (addR64R64Effect 0x1054b0 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1054b0 3 2).toInstrSpec (add_r64_r64_effect_step 0x1054b0 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1054b3 [0x4C, 0x8D, 0x3D, 0x66, 0x53, 0x02, 0x00] (fun s => s.RIP = 0x1054b3) (leaR64Effect 0x1054b3 15 (.rip 0x25366))
      [] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1054b3 15 (.rip 0x25366)).toInstrSpec (lea_r64_effect_step 0x1054b3 0x4c (by decide) 7 (.rip 0x25366) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054a9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054ac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054b3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054ba) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 63) (jmp_rel8_effect_step 0x1054ba 0x2d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1054a6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1054a6 :=
  Rest.liftedBlock (rest_l1054a6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1054a6 x hx)

theorem rest_l1054c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1054c0 bytes_l1054c0) (entryMap (live .l1054c0))
      4 0x1054c0 bytes_l1054c0 b_l1054c0 := by
  have f0 : InstrSpec 0x1054c0 [0x4A, 0x8D, 0x3C, 0x24] (fun s => s.RIP = 0x1054c0) (leaR64Effect 0x1054c0 7 (.sib 4 (some 12) 0 .none))
      [.gpr 4, .gpr 12] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1054c0 7 (.sib 4 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1054c0 0x4a (by decide) 7 (.sib 4 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1054c4 [0x48, 0x81, 0xC7, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1054c4) (addR64Imm32Effect 0x1054c4 7 0x1e8)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1054c4 7 0x1e8).toInstrSpec (add_r64_imm32_effect_step 0x1054c4 0x48 0xc7 0x1e8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1054cb [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x1054cb) (movR64R64Effect 0x1054cb 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1054cb 2 5).toInstrSpec (mov_r64_r64_effect_step 0x1054cb 0x48 0xea (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1054ce [0x41, 0xFF, 0xD7] (GoesTo (CallPre 0x1054ce 3 (fun s => (Operand.reg 15 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1054d1) 0x12a820) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1054d1)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x1054ce 15 0x1054d1).toInstrSpec (call_r64_rex_effect_step 0x1054ce 0x41 0xd7 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 15 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054cb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054ce) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1054c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1054c0 :=
  Rest.liftedBlock (rest_l1054c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1054c0 x hx)

theorem rest_l1054d1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1054d1 bytes_l1054d1) (entryMap (live .l1054d1))
      5 0x1054d1 bytes_l1054d1 b_l1054d1 := by
  have f0 : InstrSpec 0x1054d1 [0x44, 0x00, 0xE5] (fun s => s.RIP = 0x1054d1) (addR8R8Effect 0x1054d1 3 5 12)
      [.gpr 5, .gpr 12] [] [.reg 5, .flags, .rip] :=
    (addR8R8Effect_footprint 0x1054d1 3 5 12).toInstrSpec (add_r8_r8_rex_effect_step 0x1054d1 0x44 0xe5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1054d4 [0x40, 0x88, 0xAC, 0x24, 0x27, 0x02, 0x00, 0x00] (StorePre 0x1054d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x1054d4 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1054d4 8 5 (.sib 4 none 0 (.d32 0x227)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1054d4 8 5 (.sib 4 none 0 (.d32 0x227))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1054d4 0x40 (by decide) 5 (.sib 4 none 0 (.d32 0x227)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1054dc [0x49, 0x83, 0xC6, 0x10] (fun s => s.RIP = 0x1054dc) (addR64Imm8Effect 0x1054dc 14 0x10)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1054dc 14 0x10).toInstrSpec (add_r64_imm8_effect_step 0x1054dc 0x49 0xc6 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1054e0 [0x49, 0x39, 0xDE] (fun s => s.RIP = 0x1054e0) (cmpR64R64Effect 0x1054e0 14 3)
      [.gpr 14, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1054e0 14 3).toInstrSpec (cmp_r64_r64_effect_step 0x1054e0 0x49 0xde (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054dc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054e0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054e3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x1054e3 4 0xd6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1054d1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1054d1 :=
  Rest.liftedBlock (rest_l1054d1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1054d1 x hx)

theorem rest_l1054e9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1054e9 bytes_l1054e9) (entryMap (live .l1054e9))
      8 0x1054e9 bytes_l1054e9 b_l1054e9 := by
  have f0 : InstrSpec 0x1054e9 [0x49, 0x8B, 0x36] (LoadPre 0x1054e9 (fun s => AddrMode.addr (.base 14 .none) s (0x1054e9 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1054e9 6 (.base 14 .none))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1054e9 6 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1054e9 0x49 (by decide) 6 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1054ec [0x49, 0x8B, 0x6E, 0x08] (LoadPre 0x1054ec (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1054ec + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1054ec 5 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x1054ec 5 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1054ec 0x49 (by decide) 5 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1054f0 [0x44, 0x0F, 0xB6, 0xA4, 0x24, 0x27, 0x02, 0x00, 0x00] (LoadPre 0x1054f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x1054f0 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1054f0 9 12 (.sib 4 none 0 (.d32 0x227)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1054f0 9 12 (.sib 4 none 0 (.d32 0x227))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1054f0 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x227)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1054f9 [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1054f9) (movR32Imm32Effect 0x1054f9 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1054f9 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x1054f9 0xba (by decide) 0x40) pre_rip
  have f4 : InstrSpec 0x1054fe [0x4C, 0x29, 0xE2] (fun s => s.RIP = 0x1054fe) (subR64R64Effect 0x1054fe 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1054fe 2 12).toInstrSpec (sub_r64_r64_effect_step 0x1054fe 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x105501 [0x49, 0x89, 0xED] (fun s => s.RIP = 0x105501) (movR64R64Effect 0x105501 13 5)
      [.gpr 5] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x105501 13 5).toInstrSpec (mov_r64_r64_effect_step 0x105501 0x49 0xed (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x105504 [0x49, 0x29, 0xD5] (fun s => s.RIP = 0x105504) (subR64R64Effect 0x105504 13 2)
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x105504 13 2).toInstrSpec (sub_r64_r64_effect_step 0x105504 0x49 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054ec) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 55), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054f0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 55), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054f9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 55), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054fe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105501) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105504) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 65), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105507) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x105507 2 0xb7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1054e9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1054e9 :=
  Rest.liftedBlock (rest_l1054e9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1054e9 x hx)

theorem rest_l105509 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105509 bytes_l105509) (entryMap (live .l105509))
      2 0x105509 bytes_l105509 b_l105509 := by
  have f0 : InstrSpec 0x105509 [0x4D, 0x85, 0xE4] (fun s => s.RIP = 0x105509) (testR64R64Effect 0x105509 12 12)
      [.gpr 12, .gpr 12] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x105509 12 12).toInstrSpec (test_r64_r64_effect_step 0x105509 0x4d 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10550c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10550c 4 0x9f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105509 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105509 :=
  Rest.liftedBlock (rest_l105509 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105509 x hx)

theorem rest_l105512 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105512 bytes_l105512) (entryMap (live .l105512))
      4 0x105512 bytes_l105512 b_l105512 := by
  have f0 : InstrSpec 0x105512 [0x48, 0x8D, 0x2C, 0x16] (fun s => s.RIP = 0x105512) (leaR64Effect 0x105512 5 (.sib 6 (some 2) 0 .none))
      [.gpr 6, .gpr 2] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x105512 5 (.sib 6 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x105512 0x48 (by decide) 5 (.sib 6 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105516 [0x4A, 0x8D, 0x3C, 0x24] (fun s => s.RIP = 0x105516) (leaR64Effect 0x105516 7 (.sib 4 (some 12) 0 .none))
      [.gpr 4, .gpr 12] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105516 7 (.sib 4 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x105516 0x4a (by decide) 7 (.sib 4 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10551a [0x48, 0x81, 0xC7, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10551a) (addR64Imm32Effect 0x10551a 7 0x1e8)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10551a 7 0x1e8).toInstrSpec (add_r64_imm32_effect_step 0x10551a 0x48 0xc7 0x1e8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105521 [0x41, 0xFF, 0xD7] (GoesTo (CallPre 0x105521 3 (fun s => (Operand.reg 15 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x105524) 0x12a820) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x105524)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x105521 15 0x105524).toInstrSpec (call_r64_rex_effect_step 0x105521 0x41 0xd7 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 15 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105516) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10551a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105521) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 53), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105512 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105512 :=
  Rest.liftedBlock (rest_l105512 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105512 x hx)

theorem rest_l105524 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105524 bytes_l105524) (entryMap (live .l105524))
      5 0x105524 bytes_l105524 b_l105524 := by
  have f0 : InstrSpec 0x105524 [0x48, 0xFF, 0x84, 0x24, 0x48, 0x02, 0x00, 0x00] (StorePre 0x105524 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x105524 + BitVec.ofNat 64 8)) 8) (incMEffect 0x105524 8 64 (.sib 4 none 0 (.d32 0x248)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x105524 8 (.sib 4 none 0 (.d32 0x248))).toInstrSpec (inc_m64_effect_step 0x105524 0x48 (by decide) (.sib 4 none 0 (.d32 0x248)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10552c [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10552c) (movR32Imm32Effect 0x10552c 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10552c 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10552c 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x105531 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x105531) (leaR64Effect 0x105531 7 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105531 7 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (lea_r64_effect_step 0x105531 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105539 [0x48, 0x8D, 0xB4, 0x24, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105539) (leaR64Effect 0x105539 6 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105539 6 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (lea_r64_effect_step 0x105539 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x105541 [0xE8, 0x9A, 0xC3, 0x01, 0x00] (PushPre 0x105541 5) (callEffect (fun _ => 0x1218e0) 0x105546)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105541 0x1218e0 0x105546).toInstrSpec (call_rel32_effect_step 0x105541 0x1c39a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10552c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105531) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105539) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105541) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l105524 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105524 :=
  Rest.liftedBlock (rest_l105524 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105524 x hx)

theorem rest_l105546 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105546 bytes_l105546) (entryMap (live .l105546))
      5 0x105546 bytes_l105546 b_l105546 := by
  have f0 : InstrSpec 0x105546 [0xC6, 0x84, 0x24, 0x27, 0x02, 0x00, 0x00, 0x00] (StorePre 0x105546 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x105546 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x105546 (.sib 4 none 0 (.d32 0x227)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105546 (.sib 4 none 0 (.d32 0x227)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x105546 (.sib 4 none 0 (.d32 0x227)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10554e [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x10554e) (movR64R64Effect 0x10554e 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10554e 6 5).toInstrSpec (mov_r64_r64_effect_step 0x10554e 0x48 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105551 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x105551) (movR64R64Effect 0x105551 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105551 2 13).toInstrSpec (mov_r64_r64_effect_step 0x105551 0x4c 0xea (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105554 [0x48, 0xC1, 0xEA, 0x06] (fun s => s.RIP = 0x105554) (shrR64Effect 0x105554 4 2 6)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x105554 4 2 6).toInstrSpec (shr_r64_imm8_effect_step 0x105554 0x48 0xea 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10554e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105551) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105554) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 59) f3 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x105554 4 2 6 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105558) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x105558 4 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105546 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105546 :=
  Rest.liftedBlock (rest_l105546 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105546 x hx)

theorem rest_l10555a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10555a bytes_l10555a) (entryMap (live .l10555a))
      4 0x10555a bytes_l10555a b_l10555a := by
  have f0 : InstrSpec 0x10555a [0x48, 0x01, 0x94, 0x24, 0x48, 0x02, 0x00, 0x00] (StorePre 0x10555a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x10555a + BitVec.ofNat 64 8)) 8) (addMREffect 0x10555a 8 64 2 (.sib 4 none 0 (.d32 0x248)))
      [.gpr 2, .gpr 4] [] [.flags, .rip] :=
    (addMREffect64_footprint 0x10555a 8 2 (.sib 4 none 0 (.d32 0x248))).toInstrSpec (add_m64_r64_effect_step 0x10555a 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x248)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105562 [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x105562) (leaR64Effect 0x105562 7 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105562 7 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (lea_r64_effect_step 0x105562 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10556a [0x48, 0x89, 0xF5] (fun s => s.RIP = 0x10556a) (movR64R64Effect 0x10556a 5 6)
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10556a 5 6).toInstrSpec (mov_r64_r64_effect_step 0x10556a 0x48 0xf5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10556d [0xE8, 0x6E, 0xC3, 0x01, 0x00] (PushPre 0x10556d 5) (callEffect (fun _ => 0x1218e0) 0x105572)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10556d 0x1218e0 0x105572).toInstrSpec (call_rel32_effect_step 0x10556d 0x1c36e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105562) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10556a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 56), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10556d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 56), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 60) (by decide) (by decide) rfl rfl

theorem block_l10555a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10555a :=
  Rest.liftedBlock (rest_l10555a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10555a x hx)

theorem rest_l105572 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105572 bytes_l105572) (entryMap (live .l105572))
      1 0x105572 bytes_l105572 b_l105572 := by
  have f0 : InstrSpec 0x105572 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x105572) (movR64R64Effect 0x105572 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105572 6 5).toInstrSpec (mov_r64_r64_effect_step 0x105572 0x48 0xee (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105575) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l105572 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105572 :=
  Rest.liftedBlock (rest_l105572 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105572 x hx)

theorem rest_l105575 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105575 bytes_l105575) (entryMap (live .l105575))
      9 0x105575 bytes_l105575 b_l105575 := by
  have f0 : InstrSpec 0x105575 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x105575) (movR64R64Effect 0x105575 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x105575 0 13).toInstrSpec (mov_r64_r64_effect_step 0x105575 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105578 [0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x105578) (movR64Imm64Effect 0x105578 1 0x7fffffffffffffc0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x105578 1 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x105578 0x48 0xb9 (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f2 : InstrSpec 0x105582 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x105582) (andR64R64Effect 0x105582 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x105582 0 1).toInstrSpec (and_r64_r64_effect_step 0x105582 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105585 [0x41, 0x83, 0xE5, 0x3F] (fun s => s.RIP = 0x105585) (andR32Imm8Effect 0x105585 4 13 0x3f)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x105585 4 13 0x3f).toInstrSpec (and_r32_imm8_rex_effect_step 0x105585 0x41 0xe5 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x105589 [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x105589) (addR64R64Effect 0x105589 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x105589 6 0).toInstrSpec (add_r64_r64_effect_step 0x105589 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10558c [0x44, 0x88, 0xAC, 0x24, 0x27, 0x02, 0x00, 0x00] (StorePre 0x10558c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x10558c + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x10558c 8 13 (.sib 4 none 0 (.d32 0x227)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10558c 8 13 (.sib 4 none 0 (.d32 0x227))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10558c 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0x227)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x105594 [0x48, 0x8D, 0xBC, 0x24, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105594) (leaR64Effect 0x105594 7 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105594 7 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (lea_r64_effect_step 0x105594 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10559c [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x10559c) (movR64R64Effect 0x10559c 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10559c 2 13).toInstrSpec (mov_r64_r64_effect_step 0x10559c 0x4c 0xea (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10559f [0x41, 0xFF, 0xD7] (GoesTo (CallPre 0x10559f 3 (fun s => (Operand.reg 15 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1055a2) 0x12a820) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1055a2)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10559f 15 0x1055a2).toInstrSpec (call_r64_rex_effect_step 0x10559f 0x41 0xd7 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 15 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105578) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105582) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105585) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105589) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10558c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105594) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 61), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10559c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 55), (2, 66), (3, 3), (4, 4), (5, 5), (6, 61), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10559f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 55), (2, 66), (3, 3), (4, 68), (5, 5), (6, 61), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l105575 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105575 :=
  Rest.liftedBlock (rest_l105575 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105575 x hx)

theorem rest_l1055a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1055a2 bytes_l1055a2) (entryMap (live .l1055a2))
      3 0x1055a2 bytes_l1055a2 b_l1055a2 := by
  have f0 : InstrSpec 0x1055a2 [0x49, 0x83, 0xC6, 0x10] (fun s => s.RIP = 0x1055a2) (addR64Imm8Effect 0x1055a2 14 0x10)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1055a2 14 0x10).toInstrSpec (add_r64_imm8_effect_step 0x1055a2 0x49 0xc6 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1055a6 [0x49, 0x39, 0xDE] (fun s => s.RIP = 0x1055a6) (cmpR64R64Effect 0x1055a6 14 3)
      [.gpr 14, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1055a6 14 3).toInstrSpec (cmp_r64_r64_effect_step 0x1055a6 0x49 0xde (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055a6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1055a9 5 0xffffff3a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1055a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1055a2 :=
  Rest.liftedBlock (rest_l1055a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1055a2 x hx)

theorem rest_l1055af [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1055af bytes_l1055af) (entryMap (live .l1055af))
      1 0x1055af bytes_l1055af b_l1055af := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1055af 0xe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1055af [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1055af :=
  Rest.liftedBlock (rest_l1055af code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1055af x hx)

theorem rest_l1055b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1055b1 bytes_l1055b1) (entryMap (live .l1055b1))
      4 0x1055b1 bytes_l1055b1 b_l1055b1 := by
  have f0 : InstrSpec 0x1055b1 [0x49, 0x89, 0xED] (fun s => s.RIP = 0x1055b1) (movR64R64Effect 0x1055b1 13 5)
      [.gpr 5] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1055b1 13 5).toInstrSpec (mov_r64_r64_effect_step 0x1055b1 0x49 0xed (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1055b4 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1055b4) (movR64R64Effect 0x1055b4 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1055b4 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1055b4 0x4c 0xea (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1055b7 [0x48, 0xC1, 0xEA, 0x06] (fun s => s.RIP = 0x1055b7) (shrR64Effect 0x1055b7 4 2 6)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x1055b7 4 2 6).toInstrSpec (shr_r64_imm8_effect_step 0x1055b7 0x48 0xea 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055b7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 58) f2 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x1055b7 4 2 6 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055bb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x1055bb 5 0x9d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1055b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1055b1 :=
  Rest.liftedBlock (rest_l1055b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1055b1 x hx)

theorem rest_l1055bd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1055bd bytes_l1055bd) (entryMap (live .l1055bd))
      1 0x1055bd bytes_l1055bd b_l1055bd := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1055bd 0xb6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1055bd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1055bd :=
  Rest.liftedBlock (rest_l1055bd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1055bd x hx)

theorem rest_l1055bf [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1055bf bytes_l1055bf) (entryMap (live .l1055bf))
      19 0x1055bf bytes_l1055bf b_l1055bf := by
  have f0 : InstrSpec 0x1055bf [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x1055bf) (leaR64Effect 0x1055bf 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1055bf 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1055bf 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1055c4 [0x48, 0x8D, 0xB4, 0x24, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1055c4) (leaR64Effect 0x1055c4 6 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1055c4 6 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (lea_r64_effect_step 0x1055c4 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1055cc [0xB9, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1055cc) (movR32Imm32Effect 0x1055cc 5 1 0xd)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1055cc 5 1 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x1055cc 0xb9 (by decide) 0xd) pre_rip
  have f3 : InstrSpec 0x1055d1 [0xF3, 0x48, 0xA5] (RepPre 0x1055d1 (RepMovsqPre 0x1055d1)) (repMovsqEffect 0x1055d1)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1055d1).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1055d1 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x1055d4 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x47] (LoadPre 0x1055d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x1055d4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1055d4 6 15 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1055d4 6 15 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1055d4 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1055da [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x1055da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1055da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1055da 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1055da 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1055da 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1055df [0x48, 0xC1, 0xE0, 0x09] (fun s => s.RIP = 0x1055df) (shlR64Effect 0x1055df 4 0 9)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x1055df 4 0 9).toInstrSpec (shl_r64_imm8_effect_step 0x1055df 0x48 0xe0 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1055e3 [0x4D, 0x89, 0xFE] (fun s => s.RIP = 0x1055e3) (movR64R64Effect 0x1055e3 14 15)
      [.gpr 15] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1055e3 14 15).toInstrSpec (mov_r64_r64_effect_step 0x1055e3 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1055e6 [0x42, 0xC6, 0x44, 0x3C, 0x08, 0x80] (StorePre 0x1055e6 6 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d8 0x8)) s (0x1055e6 + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x1055e6 (.sib 4 (some 15) 0 (.d8 0x8)) 0x80)
      [.gpr 4, .gpr 15] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1055e6 (.sib 4 (some 15) 0 (.d8 0x8)) 0x80).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1055e6 0x42 (by decide) (.sib 4 (some 15) 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1055ec [0x4A, 0x8D, 0x3C, 0x3C] (fun s => s.RIP = 0x1055ec) (leaR64Effect 0x1055ec 7 (.sib 4 (some 15) 0 .none))
      [.gpr 4, .gpr 15] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1055ec 7 (.sib 4 (some 15) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1055ec 0x4a (by decide) 7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1055f0 [0x48, 0x83, 0xC7, 0x09] (fun s => s.RIP = 0x1055f0) (addR64Imm8Effect 0x1055f0 7 0x9)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1055f0 7 0x9).toInstrSpec (add_r64_imm8_effect_step 0x1055f0 0x48 0xc7 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1055f4 [0x41, 0xC1, 0xE7, 0x03] (fun s => s.RIP = 0x1055f4) (shlR32Effect 0x1055f4 4 15 3)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR32Effect_footprint 0x1055f4 4 15 3).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1055f4 0x41 0xe7 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1055f8 [0x49, 0x09, 0xC7] (fun s => s.RIP = 0x1055f8) (orR64R64Effect 0x1055f8 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1055f8 15 0).toInstrSpec (or_r64_r64_effect_step 0x1055f8 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1055fb [0x48, 0x8D, 0x5C, 0x24, 0x48] (fun s => s.RIP = 0x1055fb) (leaR64Effect 0x1055fb 3 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1055fb 3 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x1055fb 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x105600 [0x49, 0x0F, 0xCF] (fun s => s.RIP = 0x105600) (bswapR64Effect 0x105600 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (bswapR64Effect_footprint 0x105600 3 15).toInstrSpec (bswap_r64_effect_step 0x105600 0x49 (by decide) 0xcf (by decide)) pre_rip
  have f15 : InstrSpec 0x105603 [0x49, 0x83, 0xF6, 0x3F] (fun s => s.RIP = 0x105603) (xorR64Imm8Effect 0x105603 14 0x3f)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x105603 14 0x3f).toInstrSpec (xor_r64_imm8_effect_step 0x105603 0x49 0xf6 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x105607 [0x31, 0xF6] (fun s => s.RIP = 0x105607) (xorR32R32Effect 0x105607 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105607 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x105607 0xf6 (by decide)) pre_rip
  have f17 : InstrSpec 0x105609 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x105609) (movR64R64Effect 0x105609 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105609 2 14).toInstrSpec (mov_r64_r64_effect_step 0x105609 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10560c [0xFF, 0x15, 0xFE, 0xE7, 0x0F, 0x00] (GoesTo (CallMemPre 0x10560c (.rip 0xfe7fe)) (callEffect (callMemPtr 0x10560c (.rip 0xfe7fe)) (0x10560c + BitVec.ofNat 64 (callMemLen (.rip 0xfe7fe)))) 0x12a700) (callEffect (callMemPtr 0x10560c (.rip 0xfe7fe)) (0x10560c + BitVec.ofNat 64 (callMemLen (.rip 0xfe7fe))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10560c (.rip 0xfe7fe)).toInstrSpec (call_m64_effect_step 0x10560c (.rip 0xfe7fe) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055cc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055d1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055d4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055da) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055df) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055e3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055e6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055ec) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055f0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055f4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055f8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055fb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105600) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105603) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105607) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105609) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 65), (2, 86), (3, 78), (4, 4), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10560c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 65), (2, 86), (3, 78), (4, 88), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f18 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 90) (by decide) (by decide) rfl rfl

theorem block_l1055bf [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1055bf :=
  Rest.liftedBlock (rest_l1055bf hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1055bf x hx)

theorem rest_l105612 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105612 bytes_l105612) (entryMap (live .l105612))
      2 0x105612 bytes_l105612 b_l105612 := by
  have f0 : InstrSpec 0x105612 [0x49, 0x83, 0xFE, 0x07] (fun s => s.RIP = 0x105612) (cmpR64Imm8Effect 0x105612 14 0x7)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x105612 14 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x105612 0x49 0xfe 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105616) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x105616 7 0xbc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105612 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105612 :=
  Rest.liftedBlock (rest_l105612 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105612 x hx)

theorem rest_l10561c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10561c bytes_l10561c) (entryMap (live .l10561c))
      20 0x10561c bytes_l10561c b_l10561c := by
  have f0 : InstrSpec 0x10561c [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x10561c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10561c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10561c 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10561c 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10561c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105621 [0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x105621 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x105621 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105621 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105621 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x105621 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105629 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x105629 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105629 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105629 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105629 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x105629 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10562e [0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x10562e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10562e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10562e 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10562e 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x10562e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105636 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x105636 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105636 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105636 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105636 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x105636 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10563b [0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x10563b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10563b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10563b 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10563b 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x10563b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x105643 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x105643 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105643 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105643 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105643 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x105643 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105648 [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x105648 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x105648 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105648 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105648 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x105648 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105650 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x105650 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105650 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105650 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105650 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x105650 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x105655 [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x105655 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105655 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105655 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105655 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x105655 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10565d [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10565d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10565d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10565d 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10565d 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10565d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x105662 [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x105662 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x105662 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105662 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105662 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x105662 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10566a [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10566a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10566a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10566a 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10566a 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10566a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10566f [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x10566f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10566f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10566f 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10566f 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10566f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x105674 [0x48, 0x89, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x105674 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105674 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105674 1 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105674 1 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x105674 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10567c [0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x10567c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10567c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10567c 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10567c 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x10567c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x105684 [0x48, 0x8D, 0xB4, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105684) (leaR64Effect 0x105684 6 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105684 6 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x105684 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10568c [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10568c) (movR32Imm32Effect 0x10568c 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10568c 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10568c 0xba (by decide) 0x1) pre_rip
  have f18 : InstrSpec 0x105691 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x105691) (movR64R64Effect 0x105691 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105691 7 3).toInstrSpec (mov_r64_r64_effect_step 0x105691 0x48 0xdf (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x105694 [0xE8, 0x47, 0xC2, 0x01, 0x00] (PushPre 0x105694 5) (callEffect (fun _ => 0x1218e0) 0x105699)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105694 0x1218e0 0x105699).toInstrSpec (call_rel32_effect_step 0x105694 0x1c247 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105621) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105629) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10562e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105636) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10563b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105643) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105648) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105650) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105655) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10565d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105662) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10566a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10566f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105674) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10567c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105684) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10568c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105691) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105694) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l10561c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10561c :=
  Rest.liftedBlock (rest_l10561c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10561c x hx)

theorem rest_l105699 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105699 bytes_l105699) (entryMap (live .l105699))
      7 0x105699 bytes_l105699 b_l105699 := by
  have f0 : InstrSpec 0x105699 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105699 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105699 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105699 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105699 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105699 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1056a2 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1056a2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1056a2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056a2 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1056a2 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1056a2 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1056ab [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1056ab 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1056ab + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056ab (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1056ab (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1056ab 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1056b4 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1056b4 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1056b4 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056b4 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1056b4 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1056b4 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1056bd [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1056bd 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1056bd + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056bd (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1056bd (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1056bd 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1056c6 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1056c6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1056c6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056c6 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1056c6 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1056c6 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1056cf [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1056cf 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1056cf + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056cf (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1056cf (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1056cf 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056ab) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056bd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056c6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056cf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056d8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l105699 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105699 :=
  Rest.liftedBlock (rest_l105699 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105699 x hx)

theorem rest_l1056d8_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x1056d8 bytes_l1056d8) [(0, 70), (1, 72), (2, 78), (3, 3), (4, 4), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 76), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x105753 bytes_l1056d8_1 b_l1056d8_1 := by
  have f20 : InstrSpec 0x105753 [0xE8, 0x88, 0xC1, 0x01, 0x00] (PushPre 0x105753 5) (callEffect (fun _ => 0x1218e0) 0x105758)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105753 0x1218e0 0x105758).toInstrSpec (call_rel32_effect_step 0x105753 0x1c188 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 84), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 76), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f20 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 86) (by decide) (by decide) rfl rfl

theorem rest_l1056d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1056d8 bytes_l1056d8) (entryMap (live .l1056d8))
      21 0x1056d8 bytes_l1056d8 b_l1056d8 := by
  have f0 : InstrSpec 0x1056d8 [0x4C, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x1056d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1056d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1056d8 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1056d8 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1056d8 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1056dd [0x4C, 0x89, 0xBC, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x1056dd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1056dd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1056dd 15 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1056dd 15 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x1056dd 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1056e5 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x1056e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1056e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1056e5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1056e5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1056e5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1056ea [0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x1056ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1056ea + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1056ea 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1056ea 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x1056ea 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1056f2 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x1056f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1056f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1056f2 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1056f2 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1056f2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1056f7 [0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x1056f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1056f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1056f7 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1056f7 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x1056f7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1056ff [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1056ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1056ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1056ff 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1056ff 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1056ff 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105704 [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x105704 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x105704 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105704 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105704 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x105704 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10570c [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10570c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10570c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10570c 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10570c 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10570c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x105711 [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x105711 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105711 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105711 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105711 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x105711 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x105719 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x105719 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105719 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105719 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105719 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x105719 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10571e [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x10571e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10571e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10571e 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10571e 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x10571e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105726 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x105726 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105726 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105726 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105726 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x105726 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10572b [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x10572b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10572b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10572b 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10572b 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10572b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x105730 [0x48, 0x89, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x105730 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105730 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105730 1 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105730 1 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x105730 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x105738 [0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x105738 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105738 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105738 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105738 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x105738 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x105740 [0x4C, 0x8D, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105740) (leaR64Effect 0x105740 13 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x105740 13 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x105740 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x105748 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105748) (movR32Imm32Effect 0x105748 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x105748 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x105748 0xba (by decide) 0x1) pre_rip
  have f18 : InstrSpec 0x10574d [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10574d) (movR64R64Effect 0x10574d 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10574d 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10574d 0x48 0xdf (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x105750 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x105750) (movR64R64Effect 0x105750 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105750 6 13).toInstrSpec (mov_r64_r64_effect_step 0x105750 0x4c 0xee (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056e5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056ea) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056f2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056f7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056ff) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105704) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10570c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105711) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105719) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10571e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105726) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10572b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105730) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105738) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105740) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f16 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 76), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105748) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 76), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10574d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 4), (5, 5), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 76), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105750) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 4), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 76), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105753) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1056d8_1 code

theorem block_l1056d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1056d8 :=
  Rest.liftedBlock (rest_l1056d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1056d8 x hx)

theorem rest_l105758_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x105758 bytes_l105758) [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      14 0x1057aa bytes_l105758_1 b_l105758_1 := by
  have f20 : InstrSpec 0x1057aa [0x89, 0xBC, 0x24, 0x70, 0x01, 0x00, 0x00] (StorePre 0x1057aa 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x1057aa + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1057aa 7 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1057aa 7 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_m32_r32_low_effect_step 0x1057aa 7 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1057b1 [0x44, 0x89, 0x84, 0x24, 0x74, 0x01, 0x00, 0x00] (StorePre 0x1057b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x174)) s (0x1057b1 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1057b1 8 (.sib 4 none 0 (.d32 0x174)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1057b1 8 (.sib 4 none 0 (.d32 0x174))).toInstrSpec (mov_m32_r32_effect_step 0x1057b1 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x174)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1057b9 [0x44, 0x89, 0x8C, 0x24, 0x78, 0x01, 0x00, 0x00] (StorePre 0x1057b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1057b9 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1057b9 9 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1057b9 9 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_m32_r32_effect_step 0x1057b9 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x1057c1 [0x44, 0x89, 0x94, 0x24, 0x7C, 0x01, 0x00, 0x00] (StorePre 0x1057c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x17c)) s (0x1057c1 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1057c1 10 (.sib 4 none 0 (.d32 0x17c)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1057c1 10 (.sib 4 none 0 (.d32 0x17c))).toInstrSpec (mov_m32_r32_effect_step 0x1057c1 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0x17c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x1057c9 [0x48, 0xB8, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC, 0xAE, 0xBA] (fun s => s.RIP = 0x1057c9) (movR64Imm64Effect 0x1057c9 0 0xbaaedce6af48a03b)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1057c9 0 0xbaaedce6af48a03b).toInstrSpec (mov_r64_imm64_effect_step 0x1057c9 0x48 0xb8 (by decide) (by decide) 0xbaaedce6af48a03b) pre_rip
  have f25 : InstrSpec 0x1057d3 [0x48, 0x89, 0x84, 0x24, 0x58, 0x02, 0x00, 0x00] (StorePre 0x1057d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x258)) s (0x1057d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1057d3 0 (.sib 4 none 0 (.d32 0x258)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1057d3 0 (.sib 4 none 0 (.d32 0x258))).toInstrSpec (mov_m64_r64_effect_step 0x1057d3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x258)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x1057db [0x48, 0xB8, 0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E, 0xD2, 0xBF] (fun s => s.RIP = 0x1057db) (movR64Imm64Effect 0x1057db 0 0xbfd25e8cd0364141)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1057db 0 0xbfd25e8cd0364141).toInstrSpec (mov_r64_imm64_effect_step 0x1057db 0x48 0xb8 (by decide) (by decide) 0xbfd25e8cd0364141) pre_rip
  have f27 : InstrSpec 0x1057e5 [0x48, 0x89, 0x84, 0x24, 0x50, 0x02, 0x00, 0x00] (StorePre 0x1057e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x1057e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1057e5 0 (.sib 4 none 0 (.d32 0x250)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1057e5 0 (.sib 4 none 0 (.d32 0x250))).toInstrSpec (mov_m64_r64_effect_step 0x1057e5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x250)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x1057ed [0x48, 0xC7, 0x84, 0x24, 0x68, 0x02, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (StorePre 0x1057ed 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x268)) s (0x1057ed + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1057ed (.sib 4 none 0 (.d32 0x268)) 0xffffffff)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1057ed (.sib 4 none 0 (.d32 0x268)) 0xffffffff).toInstrSpec (mov_m64_imm32_effect_step 0x1057ed 0x48 (by decide) (.sib 4 none 0 (.d32 0x268)) (by decide) (by decide) (by decide) 0xffffffff) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x1057f9 [0x48, 0xC7, 0x84, 0x24, 0x60, 0x02, 0x00, 0x00, 0xFE, 0xFF, 0xFF, 0xFF] (StorePre 0x1057f9 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x1057f9 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1057f9 (.sib 4 none 0 (.d32 0x260)) 0xfffffffe)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1057f9 (.sib 4 none 0 (.d32 0x260)) 0xfffffffe).toInstrSpec (mov_m64_imm32_effect_step 0x1057f9 0x48 (by decide) (.sib 4 none 0 (.d32 0x260)) (by decide) (by decide) (by decide) 0xfffffffe) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x105805 [0x4C, 0x8D, 0x64, 0x24, 0x08] (fun s => s.RIP = 0x105805) (leaR64Effect 0x105805 12 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x105805 12 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105805 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10580a [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10580a) (movR64R64Effect 0x10580a 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10580a 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10580a 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10580d [0x48, 0x8B, 0xB4, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x10580d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10580d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10580d 6 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10580d 6 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_r64_m64_effect_step 0x10580d 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x105815 [0xE8, 0x16, 0x46, 0x00, 0x00] (PushPre 0x105815 5) (callEffect (fun _ => 0x109e30) 0x10581a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105815 0x109e30 0x10581a).toInstrSpec (call_rel32_effect_step 0x105815 0x4616 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057b1) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057b9) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c1) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057c9) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057d3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 93), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057db) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 96), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057e5) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 96), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057ed) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 96), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057f9) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 96), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105805) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f30 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 96), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 101), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10580a) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f31 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 96), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 103), (8, 75), (9, 79), (10, 83), (11, 11), (12, 101), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10580d) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f32 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 96), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 105), (7, 103), (8, 75), (9, 79), (10, 83), (11, 11), (12, 101), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105815) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f33 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 96), (1, 59), (2, 63), (3, 3), (4, 107), (5, 5), (6, 105), (7, 103), (8, 75), (9, 79), (10, 83), (11, 11), (12, 101), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e30) f33 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 109) (by decide) (by decide) rfl rfl

theorem rest_l105758 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105758 bytes_l105758) (entryMap (live .l105758))
      34 0x105758 bytes_l105758 b_l105758 := by
  have f0 : InstrSpec 0x105758 [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x105758 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105758 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105758 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x105758 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x105758 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10575c [0x8B, 0x4C, 0x24, 0x4C] (LoadPre 0x10575c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10575c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10575c 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x10575c 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x10575c 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x105760 [0x0F, 0xC8] (fun s => s.RIP = 0x105760) (bswapR32Effect 0x105760 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR32Effect_footprint 0x105760 2 0).toInstrSpec (bswap_r32_effect_step 0x105760 0xc8 (by decide)) pre_rip
  have f3 : InstrSpec 0x105762 [0x0F, 0xC9] (fun s => s.RIP = 0x105762) (bswapR32Effect 0x105762 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR32Effect_footprint 0x105762 2 1).toInstrSpec (bswap_r32_effect_step 0x105762 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x105764 [0x8B, 0x54, 0x24, 0x50] (LoadPre 0x105764 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x105764 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105764 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x105764 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x105764 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105768 [0x0F, 0xCA] (fun s => s.RIP = 0x105768) (bswapR32Effect 0x105768 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR32Effect_footprint 0x105768 2 2).toInstrSpec (bswap_r32_effect_step 0x105768 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x10576a [0x8B, 0x74, 0x24, 0x54] (LoadPre 0x10576a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x10576a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10576a 6 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x10576a 6 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_low_effect_step 0x10576a 6 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10576e [0x0F, 0xCE] (fun s => s.RIP = 0x10576e) (bswapR32Effect 0x10576e 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR32Effect_footprint 0x10576e 2 6).toInstrSpec (bswap_r32_effect_step 0x10576e 0xce (by decide)) pre_rip
  have f8 : InstrSpec 0x105770 [0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x105770 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x105770 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105770 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x105770 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r32_m32_low_effect_step 0x105770 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x105774 [0x0F, 0xCF] (fun s => s.RIP = 0x105774) (bswapR32Effect 0x105774 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR32Effect_footprint 0x105774 2 7).toInstrSpec (bswap_r32_effect_step 0x105774 0xcf (by decide)) pre_rip
  have f10 : InstrSpec 0x105776 [0x44, 0x8B, 0x44, 0x24, 0x5C] (LoadPre 0x105776 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x105776 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x105776 8 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x105776 8 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_r32_m32_effect_step 0x105776 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10577b [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x10577b) (bswapR32Effect 0x10577b 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x10577b 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x10577b 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f12 : InstrSpec 0x10577e [0x44, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x10577e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10577e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x10577e 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x10577e 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r32_m32_effect_step 0x10577e 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x105783 [0x41, 0x0F, 0xC9] (fun s => s.RIP = 0x105783) (bswapR32Effect 0x105783 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (bswapR32Effect_footprint 0x105783 3 9).toInstrSpec (bswap_r32_rex_effect_step 0x105783 0x41 (by decide) 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x105786 [0x44, 0x8B, 0x54, 0x24, 0x64] (LoadPre 0x105786 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x105786 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x105786 10 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x105786 10 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_r32_m32_effect_step 0x105786 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10578b [0x41, 0x0F, 0xCA] (fun s => s.RIP = 0x10578b) (bswapR32Effect 0x10578b 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR32Effect_footprint 0x10578b 3 10).toInstrSpec (bswap_r32_rex_effect_step 0x10578b 0x41 (by decide) 0xca (by decide)) pre_rip
  have f16 : InstrSpec 0x10578e [0x89, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (StorePre 0x10578e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10578e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10578e 0 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10578e 0 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_m32_r32_low_effect_step 0x10578e 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x105795 [0x89, 0x8C, 0x24, 0x64, 0x01, 0x00, 0x00] (StorePre 0x105795 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x164)) s (0x105795 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105795 1 (.sib 4 none 0 (.d32 0x164)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105795 1 (.sib 4 none 0 (.d32 0x164))).toInstrSpec (mov_m32_r32_low_effect_step 0x105795 1 (.sib 4 none 0 (.d32 0x164)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10579c [0x89, 0x94, 0x24, 0x68, 0x01, 0x00, 0x00] (StorePre 0x10579c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10579c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10579c 2 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10579c 2 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_m32_r32_low_effect_step 0x10579c 2 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1057a3 [0x89, 0xB4, 0x24, 0x6C, 0x01, 0x00, 0x00] (StorePre 0x1057a3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16c)) s (0x1057a3 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1057a3 6 (.sib 4 none 0 (.d32 0x16c)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1057a3 6 (.sib 4 none 0 (.d32 0x16c))).toInstrSpec (mov_m32_r32_low_effect_step 0x1057a3 6 (.sib 4 none 0 (.d32 0x16c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10575c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105760) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105762) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105764) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105768) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10576a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 65), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10576e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105770) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 69), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105774) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105776) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 73), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10577b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10577e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 77), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105783) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105786) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 81), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10578b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10578e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105795) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10579c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057a3) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057aa) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l105758_1 code

theorem block_l105758 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105758 :=
  Rest.liftedBlock (rest_l105758 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105758 x hx)

theorem rest_l10581a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10581a bytes_l10581a) (entryMap (live .l10581a))
      10 0x10581a bytes_l10581a b_l10581a := by
  have f0 : InstrSpec 0x10581a [0x48, 0x8D, 0x84, 0x24, 0x50, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10581a) (leaR64Effect 0x10581a 0 (.sib 4 none 0 (.d32 0x250)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10581a 0 (.sib 4 none 0 (.d32 0x250))).toInstrSpec (lea_r64_effect_step 0x10581a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x250)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105822 [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x105822) (leaR64Effect 0x105822 7 (.sib 4 none 0 (.d32 0x2b0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105822 7 (.sib 4 none 0 (.d32 0x2b0))).toInstrSpec (lea_r64_effect_step 0x105822 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x2b0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10582a [0x48, 0x8D, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10582a) (leaR64Effect 0x10582a 1 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x10582a 1 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (lea_r64_effect_step 0x10582a 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105832 [0xBA, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105832) (movR32Imm32Effect 0x105832 5 2 0x20)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x105832 5 2 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x105832 0xba (by decide) 0x20) pre_rip
  have f4 : InstrSpec 0x105837 [0x41, 0xB8, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105837) (movR32Imm32Effect 0x105837 6 8 0x20)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x105837 6 8 0x20).toInstrSpec (mov_r32_imm32_rex_effect_step 0x105837 0x41 0xb8 (by decide) (by decide) 0x20) pre_rip
  have f5 : InstrSpec 0x10583d [0x41, 0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10583d) (movR32Imm32Effect 0x10583d 6 9 0x1)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x10583d 6 9 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10583d 0x41 0xb9 (by decide) (by decide) 0x1) pre_rip
  have f6 : InstrSpec 0x105843 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x105843) (movR64R64Effect 0x105843 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105843 6 12).toInstrSpec (mov_r64_r64_effect_step 0x105843 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x105846 [0x50] (PushPre 0x105846 1) (pushR64Effect 0x105846 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105846 1 0).toInstrSpec (push_r64_effect_step 0x105846 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x105847 [0x6A, 0x00] (PushPre 0x105847 2) (pushImm8Effect 0x105847 2 0x0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (pushImm8Effect_footprint 0x105847 2 0x0).toInstrSpec (push_imm8_effect_step 0x105847 0x0) (StorePre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x105849 [0xE8, 0x52, 0xB6, 0xFF, 0xFF] (PushPre 0x105849 5) (callEffect (fun _ => 0x100ea0) 0x10584e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105849 0x100ea0 0x10584e).toInstrSpec (call_rel32_effect_step 0x105849 0xffffb652 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105822) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10582a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105832) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105837) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (7, 55), (8, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10583d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (7, 55), (8, 61), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105843) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 65), (7, 55), (8, 61), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105846) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 67), (5, 5), (6, 65), (7, 55), (8, 61), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105847) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 69), (5, 5), (6, 65), (7, 55), (8, 61), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105849) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 57), (2, 59), (3, 3), (4, 71), (5, 5), (6, 65), (7, 55), (8, 61), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea0) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l10581a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10581a :=
  Rest.liftedBlock (rest_l10581a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10581a x hx)

theorem rest_l10584e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10584e bytes_l10584e) (entryMap (live .l10584e))
      5 0x10584e bytes_l10584e b_l10584e := by
  have f0 : InstrSpec 0x10584e [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x10584e) (addR64Imm8Effect 0x10584e 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10584e 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10584e 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105852 [0x48, 0x8D, 0x9C, 0x24, 0xC8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105852) (leaR64Effect 0x105852 3 (.sib 4 none 0 (.d32 0x1c8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x105852 3 (.sib 4 none 0 (.d32 0x1c8))).toInstrSpec (lea_r64_effect_step 0x105852 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x1c8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10585a [0x48, 0x8D, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10585a) (leaR64Effect 0x10585a 5 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x10585a 5 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x10585a 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105862 [0x4C, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105862) (leaR64Effect 0x105862 15 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x105862 15 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x105862 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105852) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 55), (4, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10585a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 55), (4, 53), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105862) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 55), (4, 53), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10586a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x10586a 0x1a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10584e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10584e :=
  Rest.liftedBlock (rest_l10584e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10584e x hx)

theorem rest_l105870 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105870 bytes_l105870) (entryMap (live .l105870))
      4 0x105870 bytes_l105870 b_l105870 := by
  have f0 : InstrSpec 0x105870 [0x48, 0x8D, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105870) (leaR64Effect 0x105870 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x105870 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x105870 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105878 [0x4C, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105878) (leaR64Effect 0x105878 15 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x105878 15 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x105878 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105880 [0x4C, 0x89, 0xED] (fun s => s.RIP = 0x105880) (movR64R64Effect 0x105880 5 13)
      [.gpr 13] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x105880 5 13).toInstrSpec (mov_r64_r64_effect_step 0x105880 0x4c 0xed (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105883 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x105883) (movR64R64Effect 0x105883 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x105883 13 0).toInstrSpec (mov_r64_r64_effect_step 0x105883 0x49 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105878) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105880) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105883) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105886) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l105870 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105870 :=
  Rest.liftedBlock (rest_l105870 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105870 x hx)

theorem rest_l105886 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105886 bytes_l105886) (entryMap (live .l105886))
      8 0x105886 bytes_l105886 b_l105886 := by
  have f0 : InstrSpec 0x105886 [0x48, 0xC7, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105886 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x105886 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105886 (.sib 4 none 0 (.d32 0x198)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105886 (.sib 4 none 0 (.d32 0x198)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105886 0x48 (by decide) (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105892 [0x48, 0xC7, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105892 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x105892 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105892 (.sib 4 none 0 (.d32 0x190)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105892 (.sib 4 none 0 (.d32 0x190)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105892 0x48 (by decide) (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10589e [0x48, 0xC7, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10589e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10589e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10589e (.sib 4 none 0 (.d32 0x188)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10589e (.sib 4 none 0 (.d32 0x188)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10589e 0x48 (by decide) (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1058aa [0x48, 0xC7, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1058aa 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x1058aa + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1058aa (.sib 4 none 0 (.d32 0x180)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1058aa (.sib 4 none 0 (.d32 0x180)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1058aa 0x48 (by decide) (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1058b6 [0xBA, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1058b6) (movR32Imm32Effect 0x1058b6 5 2 0x20)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1058b6 5 2 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x1058b6 0xba (by decide) 0x20) pre_rip
  have f5 : InstrSpec 0x1058bb [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x1058bb) (leaR64Effect 0x1058bb 7 (.sib 4 none 0 (.d32 0x2b0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1058bb 7 (.sib 4 none 0 (.d32 0x2b0))).toInstrSpec (lea_r64_effect_step 0x1058bb 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x2b0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1058c3 [0x48, 0x8D, 0xB4, 0x24, 0x80, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1058c3) (leaR64Effect 0x1058c3 6 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1058c3 6 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (lea_r64_effect_step 0x1058c3 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1058cb [0xE8, 0x70, 0xB1, 0xFF, 0xFF] (PushPre 0x1058cb 5) (callEffect (fun _ => 0x100a40) 0x1058d0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1058cb 0x100a40 0x1058d0).toInstrSpec (call_rel32_effect_step 0x1058cb 0xffffb170 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105892) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10589e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058aa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058b6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058bb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 57), (3, 3), (4, 4), (5, 5), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058c3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 57), (3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058cb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 57), (3, 3), (4, 63), (5, 5), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a40) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l105886 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105886 :=
  Rest.liftedBlock (rest_l105886 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105886 x hx)

theorem rest_l1058d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1058d0 bytes_l1058d0) (entryMap (live .l1058d0))
      11 0x1058d0 bytes_l1058d0 b_l1058d0 := by
  have f0 : InstrSpec 0x1058d0 [0x48, 0x8B, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00] (LoadPre 0x1058d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x1058d0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1058d0 0 (.sib 4 none 0 (.d32 0x198)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1058d0 0 (.sib 4 none 0 (.d32 0x198))).toInstrSpec (mov_r64_m64_effect_step 0x1058d0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1058d8 [0x48, 0x89, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00] (StorePre 0x1058d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x1058d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1058d8 0 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1058d8 0 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_m64_r64_effect_step 0x1058d8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1058e0 [0x48, 0x8B, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00] (LoadPre 0x1058e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x1058e0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1058e0 0 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1058e0 0 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (mov_r64_m64_effect_step 0x1058e0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1058e8 [0x48, 0x89, 0x84, 0x24, 0xD8, 0x01, 0x00, 0x00] (StorePre 0x1058e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x1058e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1058e8 0 (.sib 4 none 0 (.d32 0x1d8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1058e8 0 (.sib 4 none 0 (.d32 0x1d8))).toInstrSpec (mov_m64_r64_effect_step 0x1058e8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1058f0 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00] (LoadPre 0x1058f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x1058f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1058f0 0 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1058f0 0 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_r64_m64_effect_step 0x1058f0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1058f8 [0x48, 0x8B, 0x8C, 0x24, 0x88, 0x01, 0x00, 0x00] (LoadPre 0x1058f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x1058f8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1058f8 1 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1058f8 1 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_r64_m64_effect_step 0x1058f8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105900 [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x105900 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x105900 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105900 1 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105900 1 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x105900 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105908 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00] (StorePre 0x105908 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x105908 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105908 0 (.sib 4 none 0 (.d32 0x1c8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105908 0 (.sib 4 none 0 (.d32 0x1c8))).toInstrSpec (mov_m64_r64_effect_step 0x105908 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1c8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105910 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x105910) (movR64R64Effect 0x105910 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105910 7 12).toInstrSpec (mov_r64_r64_effect_step 0x105910 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x105913 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x105913) (movR64R64Effect 0x105913 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105913 6 3).toInstrSpec (mov_r64_r64_effect_step 0x105913 0x48 0xde (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x105916 [0xE8, 0x45, 0x45, 0x00, 0x00] (PushPre 0x105916 5) (callEffect (fun _ => 0x109e60) 0x10591b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105916 0x109e60 0x10591b).toInstrSpec (call_rel32_effect_step 0x105916 0x4545 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058e0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058e8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058f0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1058f8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105900) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105908) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105910) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105913) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105916) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e60) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l1058d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1058d0 :=
  Rest.liftedBlock (rest_l1058d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1058d0 x hx)

theorem rest_l10591b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10591b bytes_l10591b) (entryMap (live .l10591b))
      10 0x10591b bytes_l10591b b_l10591b := by
  have f0 : InstrSpec 0x10591b [0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10591b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10591b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10591b (.sib 4 none 0 (.d32 0xb8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10591b (.sib 4 none 0 (.d32 0xb8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10591b 0x48 (by decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105927 [0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105927 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x105927 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105927 (.sib 4 none 0 (.d32 0xb0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105927 (.sib 4 none 0 (.d32 0xb0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105927 0x48 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105933 [0x48, 0xC7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105933 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x105933 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105933 (.sib 4 none 0 (.d32 0xa8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105933 (.sib 4 none 0 (.d32 0xa8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105933 0x48 (by decide) (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10593f [0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10593f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10593f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10593f (.sib 4 none 0 (.d32 0xa0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10593f (.sib 4 none 0 (.d32 0xa0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10593f 0x48 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10594b [0x44, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x10594b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10594b + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x10594b 14 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x10594b 14 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_effect_step 0x10594b 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105950 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x105950) (movR64R64Effect 0x105950 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105950 7 5).toInstrSpec (mov_r64_r64_effect_step 0x105950 0x48 0xef (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x105953 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x105953) (movR64R64Effect 0x105953 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105953 6 15).toInstrSpec (mov_r64_r64_effect_step 0x105953 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x105956 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x105956) (movR64R64Effect 0x105956 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105956 2 12).toInstrSpec (mov_r64_r64_effect_step 0x105956 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x105959 [0x44, 0x89, 0xF1] (fun s => s.RIP = 0x105959) (movR32R32Effect 0x105959 3 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105959 3 1 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x105959 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10595c [0xE8, 0xBF, 0x48, 0x00, 0x00] (PushPre 0x10595c 5) (callEffect (fun _ => 0x10a220) 0x105961)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10595c 0x10a220 0x105961).toInstrSpec (call_rel32_effect_step 0x10595c 0x48bf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105927) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105933) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10593f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10594b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105950) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 59), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105953) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105956) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 63), (3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105959) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 65), (2, 63), (3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10595c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 65), (2, 63), (3, 3), (4, 67), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a220) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l10591b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10591b :=
  Rest.liftedBlock (rest_l10591b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10591b x hx)

theorem rest_l105961 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105961 bytes_l105961) (entryMap (live .l105961))
      7 0x105961 bytes_l105961 b_l105961 := by
  have f0 : InstrSpec 0x105961 [0x48, 0xC7, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105961 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105961 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105961 (.sib 4 none 0 (.d32 0x118)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105961 (.sib 4 none 0 (.d32 0x118)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105961 0x48 (by decide) (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10596d [0x48, 0xC7, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10596d 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10596d + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10596d (.sib 4 none 0 (.d32 0x110)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10596d (.sib 4 none 0 (.d32 0x110)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10596d 0x48 (by decide) (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105979 [0x48, 0xC7, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105979 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105979 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105979 (.sib 4 none 0 (.d32 0x108)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105979 (.sib 4 none 0 (.d32 0x108)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105979 0x48 (by decide) (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x105985 [0x48, 0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105985 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105985 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105985 (.sib 4 none 0 (.d32 0x100)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105985 (.sib 4 none 0 (.d32 0x100)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105985 0x48 (by decide) (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105991 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x105991) (movR64R64Effect 0x105991 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105991 7 5).toInstrSpec (mov_r64_r64_effect_step 0x105991 0x48 0xef (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x105994 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x105994) (movR64R64Effect 0x105994 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105994 6 13).toInstrSpec (mov_r64_r64_effect_step 0x105994 0x4c 0xee (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x105997 [0xE8, 0xE4, 0x48, 0x00, 0x00] (PushPre 0x105997 5) (callEffect (fun _ => 0x10a280) 0x10599c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105997 0x10a280 0x10599c).toInstrSpec (call_rel32_effect_step 0x105997 0x48e4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10596d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105979) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105985) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105991) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105994) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105997) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l105961 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105961 :=
  Rest.liftedBlock (rest_l105961 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105961 x hx)

theorem rest_l10599c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10599c bytes_l10599c) (entryMap (live .l10599c))
      4 0x10599c bytes_l10599c b_l10599c := by
  have f0 : InstrSpec 0x10599c [0xF6, 0xD0] (fun s => s.RIP = 0x10599c) (notR8Effect 0x10599c 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x10599c 2 0).toInstrSpec (not_r8_effect_step 0x10599c 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10599e [0x24, 0x01] (fun s => s.RIP = 0x10599e) (andAlImm8Effect 0x10599e 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10599e 0x1).toInstrSpec (and_al_imm8_effect_step 0x10599e 0x1) pre_rip
  have f2 : InstrSpec 0x1059a0 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1059a0) (movzxR32R8Effect 0x1059a0 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1059a0 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1059a0 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1059a3 [0xE8, 0xA8, 0x23, 0x02, 0x00] (PushPre 0x1059a3 5) (callEffect (fun _ => 0x127d50) 0x1059a8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1059a3 0x127d50 0x1059a8).toInstrSpec (call_rel32_effect_step 0x1059a3 0x223a8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10599e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10599c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10599c :=
  Rest.liftedBlock (rest_l10599c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10599c x hx)

theorem rest_l1059a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1059a8 bytes_l1059a8) (entryMap (live .l1059a8))
      11 0x1059a8 bytes_l1059a8 b_l1059a8 := by
  have f0 : InstrSpec 0x1059a8 [0x48, 0x8B, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x1059a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1059a8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059a8 1 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1059a8 1 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x1059a8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1059b0 [0x48, 0x8B, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x1059b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1059b0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059b0 2 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1059b0 2 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x1059b0 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1059b8 [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1059b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1059b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1059b8 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1059b8 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1059b8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1059c0 [0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1059c0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1059c0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1059c0 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1059c0 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1059c0 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1059c8 [0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x1059c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1059c8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059c8 1 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1059c8 1 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x1059c8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1059d0 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1059d0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1059d0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1059d0 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1059d0 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1059d0 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1059d8 [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1059d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1059d8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059d8 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1059d8 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1059d8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1059e0 [0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1059e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1059e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1059e0 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1059e0 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1059e0 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1059e8 [0x44, 0x20, 0xF0] (fun s => s.RIP = 0x1059e8) (andR8R8Effect 0x1059e8 3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (andR8R8Effect_footprint 0x1059e8 3 0 14).toInstrSpec (and_r8_r8_rex_effect_step 0x1059e8 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1059eb [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1059eb) (movzxR32R8Effect 0x1059eb 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1059eb 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1059eb 0xf8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1059ee [0xE8, 0x5D, 0x23, 0x02, 0x00] (PushPre 0x1059ee 5) (callEffect (fun _ => 0x127d50) 0x1059f3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1059ee 0x127d50 0x1059f3).toInstrSpec (call_rel32_effect_step 0x1059ee 0x2235d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059b8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059c0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059c8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059d0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059d8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059e0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059e8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059eb) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059ee) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 69), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l1059a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1059a8 :=
  Rest.liftedBlock (rest_l1059a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1059a8 x hx)

theorem rest_l1059f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1059f3 bytes_l1059f3) (entryMap (live .l1059f3))
      2 0x1059f3 bytes_l1059f3 b_l1059f3 := by
  have f0 : InstrSpec 0x1059f3 [0x3C, 0x01] (fun s => s.RIP = 0x1059f3) (cmpAlImm8Effect 0x1059f3 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1059f3 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x1059f3 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1059f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1059f5 5 0xfffffe8b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1059f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1059f3 :=
  Rest.liftedBlock (rest_l1059f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1059f3 x hx)

theorem rest_l1059fb_1 [Bindings] (code : CodeMap) :
    Rest (n := 80) code lifted (codeRange 0x1059fb bytes_l1059fb) [(0, 59), (1, 76), (3, 3), (4, 4), (5, 5), (6, 74), (7, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x105a9c bytes_l1059fb_1 b_l1059fb_1 := by
  have f20 : InstrSpec 0x105a9c [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x105a9c) (movR64R64Effect 0x105a9c 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105a9c 2 13).toInstrSpec (mov_r64_r64_effect_step 0x105a9c 0x4c 0xea (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x105a9f [0x41, 0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105a9f) (movR32Imm32Effect 0x105a9f 6 8 0x100)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x105a9f 6 8 0x100).toInstrSpec (mov_r32_imm32_rex_effect_step 0x105a9f 0x41 0xb8 (by decide) (by decide) 0x100) pre_rip
  have f22 : InstrSpec 0x105aa5 [0xE8, 0xC6, 0x22, 0x02, 0x00] (PushPre 0x105aa5 5) (callEffect (fun _ => 0x127d70) 0x105aaa)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105aa5 0x127d70 0x105aaa).toInstrSpec (call_rel32_effect_step 0x105aa5 0x222c6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 59), (1, 76), (2, 80), (3, 3), (4, 4), (5, 5), (6, 74), (7, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a9f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f21 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 59), (1, 76), (2, 80), (3, 3), (4, 4), (5, 5), (6, 74), (7, 78), (8, 82), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aa5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 59), (1, 76), (2, 80), (3, 3), (4, 84), (5, 5), (6, 74), (7, 78), (8, 82), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f22 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 86) (by decide) (by decide) rfl rfl

theorem rest_l1059fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1059fb bytes_l1059fb) (entryMap (live .l1059fb))
      23 0x1059fb bytes_l1059fb b_l1059fb := by
  have f0 : InstrSpec 0x1059fb [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x1059fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1059fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059fb 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1059fb 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x1059fb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105a03 [0x48, 0x89, 0x84, 0x24, 0x88, 0x02, 0x00, 0x00] (StorePre 0x105a03 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x288)) s (0x105a03 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105a03 0 (.sib 4 none 0 (.d32 0x288)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105a03 0 (.sib 4 none 0 (.d32 0x288))).toInstrSpec (mov_m64_r64_effect_step 0x105a03 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x288)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105a0b [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x105a0b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105a0b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105a0b 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105a0b 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x105a0b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105a13 [0x48, 0x89, 0x84, 0x24, 0x80, 0x02, 0x00, 0x00] (StorePre 0x105a13 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x280)) s (0x105a13 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105a13 0 (.sib 4 none 0 (.d32 0x280)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105a13 0 (.sib 4 none 0 (.d32 0x280))).toInstrSpec (mov_m64_r64_effect_step 0x105a13 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x280)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105a1b [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x105a1b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x105a1b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105a1b 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105a1b 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x105a1b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105a23 [0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x105a23 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105a23 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105a23 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105a23 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x105a23 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105a2b [0x48, 0x89, 0x8C, 0x24, 0x78, 0x02, 0x00, 0x00] (StorePre 0x105a2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x278)) s (0x105a2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105a2b 1 (.sib 4 none 0 (.d32 0x278)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105a2b 1 (.sib 4 none 0 (.d32 0x278))).toInstrSpec (mov_m64_r64_effect_step 0x105a2b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x278)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105a33 [0x48, 0x89, 0x84, 0x24, 0x70, 0x02, 0x00, 0x00] (StorePre 0x105a33 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x270)) s (0x105a33 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105a33 0 (.sib 4 none 0 (.d32 0x270)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105a33 0 (.sib 4 none 0 (.d32 0x270))).toInstrSpec (mov_m64_r64_effect_step 0x105a33 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x270)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105a3b [0xC6, 0x44, 0x24, 0x08, 0x01] (StorePre 0x105a3b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105a3b + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105a3b (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105a3b (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x105a3b (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x105a40 [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x105a40 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105a40 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105a40 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105a40 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x105a40 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x105a45 [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x105a45 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105a45 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105a45 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105a45 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x105a45 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x105a4a [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x105a4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105a4a + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105a4a (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105a4a (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x105a4a (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105a4f [0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00] (StorePre 0x105a4f 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105a4f + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x105a4f 11 (.sib 4 none 0 (.d32 0xc0)) 0x100)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x105a4f 11 (.sib 4 none 0 (.d32 0xc0)) 0x100).toInstrSpec (mov_m32_imm32_effect_step 0x105a4f (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x100) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x105a5a [0x48, 0xC7, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105a5a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105a5a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105a5a (.sib 4 none 0 (.d32 0x118)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105a5a (.sib 4 none 0 (.d32 0x118)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105a5a 0x48 (by decide) (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x105a66 [0x48, 0xC7, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105a66 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x105a66 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105a66 (.sib 4 none 0 (.d32 0x110)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105a66 (.sib 4 none 0 (.d32 0x110)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105a66 0x48 (by decide) (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x105a72 [0x48, 0xC7, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105a72 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105a72 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105a72 (.sib 4 none 0 (.d32 0x108)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105a72 (.sib 4 none 0 (.d32 0x108)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105a72 0x48 (by decide) (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x105a7e [0x48, 0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105a7e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105a7e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105a7e (.sib 4 none 0 (.d32 0x100)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105a7e (.sib 4 none 0 (.d32 0x100)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105a7e 0x48 (by decide) (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x105a8a [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105a8a) (movR32Imm32Effect 0x105a8a 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x105a8a 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x105a8a 0xbe (by decide) 0x20) pre_rip
  have f18 : InstrSpec 0x105a8f [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105a8f) (movR32Imm32Effect 0x105a8f 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x105a8f 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x105a8f 0xb9 (by decide) 0x4) pre_rip
  have f19 : InstrSpec 0x105a94 [0x48, 0x8D, 0xBC, 0x24, 0x60, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105a94) (leaR64Effect 0x105a94 7 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105a94 7 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (lea_r64_effect_step 0x105a94 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a03) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a0b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a13) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a1b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a23) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a2b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a33) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a3b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a40) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a45) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a4a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a4f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a5a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a66) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a72) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a7e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a8a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a8f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 59), (1, 76), (3, 3), (4, 4), (5, 5), (6, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a94) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 59), (1, 76), (3, 3), (4, 4), (5, 5), (6, 74), (7, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105a9c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1059fb_1 code

theorem block_l1059fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1059fb :=
  Rest.liftedBlock (rest_l1059fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1059fb x hx)

theorem rest_l105aaa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105aaa bytes_l105aaa) (entryMap (live .l105aaa))
      3 0x105aaa bytes_l105aaa b_l105aaa := by
  have f0 : InstrSpec 0x105aaa [0x3C, 0xFF] (fun s => s.RIP = 0x105aaa) (cmpAlImm8Effect 0x105aaa 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x105aaa 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x105aaa 0xff) pre_rip
  have f1 : InstrSpec 0x105aac [0x4C, 0x8D, 0xAC, 0x24, 0x90, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x105aac) (leaR64Effect 0x105aac 13 (.sib 4 none 0 (.d32 0x290)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x105aac 13 (.sib 4 none 0 (.d32 0x290))).toInstrSpec (lea_r64_effect_step 0x105aac 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x290)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ab4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x105ab4 5 0x400) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105aaa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105aaa :=
  Rest.liftedBlock (rest_l105aaa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105aaa x hx)

theorem rest_l105aba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105aba bytes_l105aba) (entryMap (live .l105aba))
      12 0x105aba bytes_l105aba b_l105aba := by
  have f0 : InstrSpec 0x105aba [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x105aba) (movR64R64Effect 0x105aba 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x105aba 15 3).toInstrSpec (mov_r64_r64_effect_step 0x105aba 0x49 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105abd [0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (LoadPre 0x105abd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105abd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105abd 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105abd 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_r64_m64_effect_step 0x105abd 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x105ac5 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x105ac5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105ac5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ac5 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105ac5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x105ac5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x105aca [0x48, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x105aca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x105aca + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105aca 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105aca 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_r64_m64_effect_step 0x105aca 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x105ad2 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x105ad2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105ad2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ad2 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105ad2 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x105ad2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x105ad7 [0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x105ad7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105ad7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105ad7 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105ad7 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_r64_m64_effect_step 0x105ad7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105adf [0x48, 0x8B, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00] (LoadPre 0x105adf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105adf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105adf 1 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105adf 1 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_r64_m64_effect_step 0x105adf 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105ae7 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x105ae7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105ae7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ae7 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105ae7 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x105ae7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105aec [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x105aec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105aec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105aec 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105aec 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x105aec 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x105af1 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x105af1) (movR64R64Effect 0x105af1 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105af1 7 13).toInstrSpec (mov_r64_r64_effect_step 0x105af1 0x4c 0xef (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x105af4 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x105af4) (movR64R64Effect 0x105af4 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105af4 6 12).toInstrSpec (mov_r64_r64_effect_step 0x105af4 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x105af7 [0xE8, 0x84, 0x44, 0x00, 0x00] (PushPre 0x105af7 5) (callEffect (fun _ => 0x109f80) 0x105afc)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105af7 0x109f80 0x105afc).toInstrSpec (call_rel32_effect_step 0x105af7 0x4484 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105abd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ac5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aca) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ad2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ad7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105adf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ae7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aec) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105af1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105af4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (6, 69), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105af7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 71), (5, 5), (6, 69), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f80) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l105aba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105aba :=
  Rest.liftedBlock (rest_l105aba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105aba x hx)

theorem rest_l105afc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105afc bytes_l105afc) (entryMap (live .l105afc))
      4 0x105afc bytes_l105afc b_l105afc := by
  have f0 : InstrSpec 0x105afc [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x105afc) (movR64R64Effect 0x105afc 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105afc 7 12).toInstrSpec (mov_r64_r64_effect_step 0x105afc 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105aff [0x48, 0x8D, 0x9C, 0x24, 0x70, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x105aff) (leaR64Effect 0x105aff 3 (.sib 4 none 0 (.d32 0x270)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x105aff 3 (.sib 4 none 0 (.d32 0x270))).toInstrSpec (lea_r64_effect_step 0x105aff 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x270)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105b07 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x105b07) (movR64R64Effect 0x105b07 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105b07 6 3).toInstrSpec (mov_r64_r64_effect_step 0x105b07 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105b0a [0xE8, 0x71, 0x42, 0x00, 0x00] (PushPre 0x105b0a 5) (callEffect (fun _ => 0x109d80) 0x105b0f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105b0a 0x109d80 0x105b0f).toInstrSpec (call_rel32_effect_step 0x105b0a 0x4271 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105aff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 55), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b07) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 55), (4, 4), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b0a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 55), (4, 59), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105afc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105afc :=
  Rest.liftedBlock (rest_l105afc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105afc x hx)

theorem rest_l105b0f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105b0f bytes_l105b0f) (entryMap (live .l105b0f))
      4 0x105b0f bytes_l105b0f b_l105b0f := by
  have f0 : InstrSpec 0x105b0f [0x0F, 0xB6, 0x44, 0x24, 0x28] (LoadPre 0x105b0f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105b0f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x105b0f 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x105b0f 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x105b0f 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105b14 [0x88, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x105b14 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105b14 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x105b14 7 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x105b14 7 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m8_r8_effect_step 0x105b14 0 (by decide) (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105b1b [0x3C, 0x01] (fun s => s.RIP = 0x105b1b) (cmpAlImm8Effect 0x105b1b 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x105b1b 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x105b1b 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b14) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b1b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b1d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x105b1d 5 0x3b0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105b0f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105b0f :=
  Rest.liftedBlock (rest_l105b0f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105b0f x hx)

theorem rest_l105b23 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105b23 bytes_l105b23) (entryMap (live .l105b23))
      11 0x105b23 bytes_l105b23 b_l105b23 := by
  have f0 : InstrSpec 0x105b23 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x105b23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b23 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105b23 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105b23 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x105b23 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105b28 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x105b28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105b28 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105b28 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105b28 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x105b28 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x105b2d [0x48, 0x89, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00] (StorePre 0x105b2d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x105b2d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105b2d 0 (.sib 4 none 0 (.d32 0x1a8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105b2d 0 (.sib 4 none 0 (.d32 0x1a8))).toInstrSpec (mov_m64_r64_effect_step 0x105b2d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1a8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x105b35 [0x48, 0x89, 0x8C, 0x24, 0xB0, 0x01, 0x00, 0x00] (StorePre 0x105b35 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x105b35 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105b35 1 (.sib 4 none 0 (.d32 0x1b0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105b35 1 (.sib 4 none 0 (.d32 0x1b0))).toInstrSpec (mov_m64_r64_effect_step 0x105b35 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1b0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105b3d [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x105b3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105b3d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105b3d 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105b3d 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x105b3d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105b42 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x01, 0x00, 0x00] (StorePre 0x105b42 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x105b42 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105b42 0 (.sib 4 none 0 (.d32 0x1b8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105b42 0 (.sib 4 none 0 (.d32 0x1b8))).toInstrSpec (mov_m64_r64_effect_step 0x105b42 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1b8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x105b4a [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x105b4a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105b4a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105b4a 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105b4a 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x105b4a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105b4f [0x48, 0x89, 0x84, 0x24, 0xC0, 0x01, 0x00, 0x00] (StorePre 0x105b4f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x105b4f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105b4f 0 (.sib 4 none 0 (.d32 0x1c0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105b4f 0 (.sib 4 none 0 (.d32 0x1c0))).toInstrSpec (mov_m64_r64_effect_step 0x105b4f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1c0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105b57 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x105b57) (movR64R64Effect 0x105b57 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105b57 7 12).toInstrSpec (mov_r64_r64_effect_step 0x105b57 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x105b5a [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x105b5a) (movR64R64Effect 0x105b5a 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105b5a 6 3).toInstrSpec (mov_r64_r64_effect_step 0x105b5a 0x48 0xde (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x105b5d [0xE8, 0x1E, 0x93, 0x00, 0x00] (PushPre 0x105b5d 5) (callEffect (fun _ => 0x10ee80) 0x105b62)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105b5d 0x10ee80 0x105b62).toInstrSpec (call_rel32_effect_step 0x105b5d 0x931e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b3d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b42) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b4a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b4f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b57) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b5a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b5d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee80) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l105b23 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105b23 :=
  Rest.liftedBlock (rest_l105b23 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105b23 x hx)

theorem rest_l105b62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105b62 bytes_l105b62) (entryMap (live .l105b62))
      4 0x105b62 bytes_l105b62 b_l105b62 := by
  have f0 : InstrSpec 0x105b62 [0x48, 0x8D, 0x9C, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105b62) (leaR64Effect 0x105b62 3 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x105b62 3 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x105b62 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105b6a [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x105b6a) (movR64R64Effect 0x105b6a 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105b6a 7 3).toInstrSpec (mov_r64_r64_effect_step 0x105b6a 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105b6d [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x105b6d) (movR64R64Effect 0x105b6d 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105b6d 6 12).toInstrSpec (mov_r64_r64_effect_step 0x105b6d 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105b70 [0xE8, 0xDB, 0xA2, 0x00, 0x00] (PushPre 0x105b70 5) (callEffect (fun _ => 0x10fe50) 0x105b75)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105b70 0x10fe50 0x105b75).toInstrSpec (call_rel32_effect_step 0x105b70 0xa2db (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b6a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b6d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b70) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 53), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105b62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105b62 :=
  Rest.liftedBlock (rest_l105b62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105b62 x hx)

theorem rest_l105b75 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105b75 bytes_l105b75) (entryMap (live .l105b75))
      4 0x105b75 bytes_l105b75 b_l105b75 := by
  have f0 : InstrSpec 0x105b75 [0x4C, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105b75) (leaR64Effect 0x105b75 14 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x105b75 14 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x105b75 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105b7d [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x105b7d) (movR64R64Effect 0x105b7d 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105b7d 7 14).toInstrSpec (mov_r64_r64_effect_step 0x105b7d 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105b80 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x105b80) (movR64R64Effect 0x105b80 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105b80 6 3).toInstrSpec (mov_r64_r64_effect_step 0x105b80 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105b83 [0xE8, 0xC8, 0xA7, 0x01, 0x00] (PushPre 0x105b83 5) (callEffect (fun _ => 0x120350) 0x105b88)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105b83 0x120350 0x105b88).toInstrSpec (call_rel32_effect_step 0x105b83 0x1a7c8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b80) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b83) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120350) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105b75 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105b75 :=
  Rest.liftedBlock (rest_l105b75 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105b75 x hx)

theorem rest_l105b88 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105b88 bytes_l105b88) (entryMap (live .l105b88))
      15 0x105b88 bytes_l105b88 b_l105b88 := by
  have f0 : InstrSpec 0x105b88 [0xC6, 0x44, 0x24, 0x08, 0x01] (StorePre 0x105b88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b88 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105b88 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105b88 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x105b88 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105b8d [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x105b8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b8d + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105b8d (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105b8d (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x105b8d (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105b92 [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x105b92 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b92 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105b92 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105b92 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x105b92 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x105b97 [0xC6, 0x44, 0x24, 0x08, 0x00] (StorePre 0x105b97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b97 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105b97 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x105b97 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x105b97 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105b9c [0xC7, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00] (StorePre 0x105b9c 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x105b9c + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x105b9c 11 (.sib 4 none 0 (.d32 0x1c8)) 0x100)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x105b9c 11 (.sib 4 none 0 (.d32 0x1c8)) 0x100).toInstrSpec (mov_m32_imm32_effect_step 0x105b9c (.sib 4 none 0 (.d32 0x1c8)) (by decide) (by decide) (by decide) 0x100) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x105ba7 [0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105ba7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x105ba7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105ba7 (.sib 4 none 0 (.d32 0xd8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105ba7 (.sib 4 none 0 (.d32 0xd8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105ba7 0x48 (by decide) (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x105bb3 [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105bb3 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x105bb3 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105bb3 (.sib 4 none 0 (.d32 0xd0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105bb3 (.sib 4 none 0 (.d32 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105bb3 0x48 (by decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105bbf [0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105bbf 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x105bbf + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105bbf (.sib 4 none 0 (.d32 0xc8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105bbf (.sib 4 none 0 (.d32 0xc8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105bbf 0x48 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105bcb [0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105bcb 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105bcb + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105bcb (.sib 4 none 0 (.d32 0xc0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105bcb (.sib 4 none 0 (.d32 0xc0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105bcb 0x48 (by decide) (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x105bd7 [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105bd7) (movR32Imm32Effect 0x105bd7 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x105bd7 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x105bd7 0xbe (by decide) 0x20) pre_rip
  have f10 : InstrSpec 0x105bdc [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105bdc) (movR32Imm32Effect 0x105bdc 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x105bdc 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x105bdc 0xb9 (by decide) 0x4) pre_rip
  have f11 : InstrSpec 0x105be1 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x105be1) (movR64R64Effect 0x105be1 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105be1 7 14).toInstrSpec (mov_r64_r64_effect_step 0x105be1 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x105be4 [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x105be4) (movR64R64Effect 0x105be4 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105be4 2 5).toInstrSpec (mov_r64_r64_effect_step 0x105be4 0x48 0xea (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x105be7 [0x41, 0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105be7) (movR32Imm32Effect 0x105be7 6 8 0x100)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x105be7 6 8 0x100).toInstrSpec (mov_r32_imm32_rex_effect_step 0x105be7 0x41 0xb8 (by decide) (by decide) 0x100) pre_rip
  have f14 : InstrSpec 0x105bed [0xE8, 0x7E, 0x21, 0x02, 0x00] (PushPre 0x105bed 5) (callEffect (fun _ => 0x127d70) 0x105bf2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105bed 0x127d70 0x105bf2).toInstrSpec (call_rel32_effect_step 0x105bed 0x2217e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b8d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b92) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b97) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105b9c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ba7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bb3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bbf) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bcb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bd7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bdc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (3, 3), (4, 4), (5, 5), (6, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105be1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 64), (3, 3), (4, 4), (5, 5), (6, 62), (7, 66), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105be4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 64), (2, 68), (3, 3), (4, 4), (5, 5), (6, 62), (7, 66), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105be7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 64), (2, 68), (3, 3), (4, 4), (5, 5), (6, 62), (7, 66), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bed) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 64), (2, 68), (3, 3), (4, 72), (5, 5), (6, 62), (7, 66), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 74) (by decide) (by decide) rfl rfl

theorem block_l105b88 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105b88 :=
  Rest.liftedBlock (rest_l105b88 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105b88 x hx)

theorem rest_l105bf2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105bf2 bytes_l105bf2) (entryMap (live .l105bf2))
      2 0x105bf2 bytes_l105bf2 b_l105bf2 := by
  have f0 : InstrSpec 0x105bf2 [0x3C, 0xFF] (fun s => s.RIP = 0x105bf2) (cmpAlImm8Effect 0x105bf2 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x105bf2 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x105bf2 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105bf4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x105bf4 5 0x2f8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105bf2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105bf2 :=
  Rest.liftedBlock (rest_l105bf2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105bf2 x hx)

theorem rest_l105bfa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105bfa bytes_l105bfa) (entryMap (live .l105bfa))
      11 0x105bfa bytes_l105bfa b_l105bfa := by
  have f0 : InstrSpec 0x105bfa [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x105bfa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x105bfa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105bfa 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105bfa 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x105bfa 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105c02 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x105c02 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105c02 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c02 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c02 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x105c02 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105c07 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x105c07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x105c07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c07 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105c07 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x105c07 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105c0f [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x105c0f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105c0f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c0f 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c0f 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x105c0f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105c14 [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x105c14 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105c14 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c14 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105c14 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x105c14 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105c1c [0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x105c1c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x105c1c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c1c 1 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105c1c 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x105c1c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105c24 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x105c24 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105c24 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c24 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c24 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x105c24 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105c29 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x105c29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105c29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c29 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c29 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x105c29 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105c2e [0x48, 0x8D, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105c2e) (leaR64Effect 0x105c2e 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105c2e 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x105c2e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x105c36 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x105c36) (movR64R64Effect 0x105c36 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105c36 6 12).toInstrSpec (mov_r64_r64_effect_step 0x105c36 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x105c39 [0xE8, 0x42, 0x43, 0x00, 0x00] (PushPre 0x105c39 5) (callEffect (fun _ => 0x109f80) 0x105c3e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105c39 0x109f80 0x105c3e).toInstrSpec (call_rel32_effect_step 0x105c39 0x4342 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c07) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c0f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c14) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c1c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c24) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c29) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c2e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c36) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c39) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f80) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l105bfa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105bfa :=
  Rest.liftedBlock (rest_l105bfa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105bfa x hx)

theorem rest_l105c3e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105c3e bytes_l105c3e) (entryMap (live .l105c3e))
      20 0x105c3e bytes_l105c3e b_l105c3e := by
  have f0 : InstrSpec 0x105c3e [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x01, 0x00, 0x00] (LoadPre 0x105c3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x105c3e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c3e 0 (.sib 4 none 0 (.d32 0x1c0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105c3e 0 (.sib 4 none 0 (.d32 0x1c0))).toInstrSpec (mov_r64_m64_effect_step 0x105c3e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1c0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105c46 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x105c46 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x105c46 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105c46 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c46 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x105c46 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105c4e [0x48, 0x8B, 0x84, 0x24, 0xB8, 0x01, 0x00, 0x00] (LoadPre 0x105c4e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x105c4e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c4e 0 (.sib 4 none 0 (.d32 0x1b8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105c4e 0 (.sib 4 none 0 (.d32 0x1b8))).toInstrSpec (mov_r64_m64_effect_step 0x105c4e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1b8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105c56 [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x105c56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x105c56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105c56 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c56 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x105c56 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105c5e [0x48, 0x8B, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00] (LoadPre 0x105c5e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x105c5e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c5e 0 (.sib 4 none 0 (.d32 0x1a8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105c5e 0 (.sib 4 none 0 (.d32 0x1a8))).toInstrSpec (mov_r64_m64_effect_step 0x105c5e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1a8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105c66 [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x01, 0x00, 0x00] (LoadPre 0x105c66 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x105c66 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c66 1 (.sib 4 none 0 (.d32 0x1b0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105c66 1 (.sib 4 none 0 (.d32 0x1b0))).toInstrSpec (mov_r64_m64_effect_step 0x105c66 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1b0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105c6e [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x105c6e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x105c6e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105c6e 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c6e 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x105c6e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105c76 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x105c76 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x105c76 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105c76 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c76 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x105c76 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105c7e [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x105c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x105c7e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c7e 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105c7e 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x105c7e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x105c86 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x105c86 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105c86 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c86 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c86 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x105c86 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x105c8b [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x105c8b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105c8b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c8b 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105c8b 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x105c8b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x105c93 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x105c93 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105c93 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c93 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105c93 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x105c93 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105c98 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x105c98 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x105c98 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c98 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105c98 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x105c98 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x105ca0 [0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x105ca0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105ca0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105ca0 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105ca0 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x105ca0 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x105ca8 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x105ca8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105ca8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ca8 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105ca8 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x105ca8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x105cad [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x105cad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105cad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105cad 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105cad 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x105cad 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x105cb2 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x105cb2) (movR64R64Effect 0x105cb2 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105cb2 7 5).toInstrSpec (mov_r64_r64_effect_step 0x105cb2 0x48 0xef (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x105cb5 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x105cb5) (movR64R64Effect 0x105cb5 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105cb5 6 12).toInstrSpec (mov_r64_r64_effect_step 0x105cb5 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x105cb8 [0x48, 0x8B, 0x94, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x105cb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x105cb8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105cb8 2 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x105cb8 2 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_r64_m64_effect_step 0x105cb8 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x105cc0 [0xE8, 0xAB, 0x42, 0x00, 0x00] (PushPre 0x105cc0 5) (callEffect (fun _ => 0x109f70) 0x105cc5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105cc0 0x109f70 0x105cc5).toInstrSpec (call_rel32_effect_step 0x105cc0 0x42ab (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c46) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c4e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c56) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c5e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c66) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c6e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c76) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c7e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c86) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c8b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c93) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105c98) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ca0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ca8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cad) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cb2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (7, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cb5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (6, 79), (7, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cb8) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (2, 81), (3, 3), (4, 4), (5, 5), (6, 79), (7, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cc0) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (2, 81), (3, 3), (4, 83), (5, 5), (6, 79), (7, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f70) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l105c3e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105c3e :=
  Rest.liftedBlock (rest_l105c3e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105c3e x hx)

theorem rest_l105cc5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105cc5 bytes_l105cc5) (entryMap (live .l105cc5))
      5 0x105cc5 bytes_l105cc5 b_l105cc5 := by
  have f0 : InstrSpec 0x105cc5 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x105cc5) (movR64R64Effect 0x105cc5 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105cc5 7 12).toInstrSpec (mov_r64_r64_effect_step 0x105cc5 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105cc8 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x105cc8) (movR64R64Effect 0x105cc8 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105cc8 6 13).toInstrSpec (mov_r64_r64_effect_step 0x105cc8 0x4c 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105ccb [0x49, 0x89, 0xED] (fun s => s.RIP = 0x105ccb) (movR64R64Effect 0x105ccb 13 5)
      [.gpr 5] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x105ccb 13 5).toInstrSpec (mov_r64_r64_effect_step 0x105ccb 0x49 0xed (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105cce [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x105cce) (movR64R64Effect 0x105cce 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105cce 2 5).toInstrSpec (mov_r64_r64_effect_step 0x105cce 0x48 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x105cd1 [0xE8, 0x0A, 0x46, 0x00, 0x00] (PushPre 0x105cd1 5) (callEffect (fun _ => 0x10a2e0) 0x105cd6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105cd1 0x10a2e0 0x105cd6).toInstrSpec (call_rel32_effect_step 0x105cd1 0x460a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cc8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ccb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cce) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cd1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l105cc5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105cc5 :=
  Rest.liftedBlock (rest_l105cc5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105cc5 x hx)

theorem rest_l105cd6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105cd6 bytes_l105cd6) (entryMap (live .l105cd6))
      5 0x105cd6 bytes_l105cd6 b_l105cd6 := by
  have f0 : InstrSpec 0x105cd6 [0x4C, 0x89, 0xFB] (fun s => s.RIP = 0x105cd6) (movR64R64Effect 0x105cd6 3 15)
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x105cd6 3 15).toInstrSpec (mov_r64_r64_effect_step 0x105cd6 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105cd9 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x105cd9) (movR64R64Effect 0x105cd9 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105cd9 7 15).toInstrSpec (mov_r64_r64_effect_step 0x105cd9 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105cdc [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x105cdc) (movR64R64Effect 0x105cdc 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105cdc 6 14).toInstrSpec (mov_r64_r64_effect_step 0x105cdc 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105cdf [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x105cdf) (movR64R64Effect 0x105cdf 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105cdf 2 12).toInstrSpec (mov_r64_r64_effect_step 0x105cdf 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x105ce2 [0xE8, 0x79, 0x42, 0x00, 0x00] (PushPre 0x105ce2 5) (callEffect (fun _ => 0x109f60) 0x105ce7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105ce2 0x109f60 0x105ce7).toInstrSpec (call_rel32_effect_step 0x105ce2 0x4279 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cd9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cdc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cdf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ce2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f60) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l105cd6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105cd6 :=
  Rest.liftedBlock (rest_l105cd6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105cd6 x hx)

theorem rest_l105ce7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105ce7 bytes_l105ce7) (entryMap (live .l105ce7))
      12 0x105ce7 bytes_l105ce7 b_l105ce7 := by
  have f0 : InstrSpec 0x105ce7 [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x105ce7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x105ce7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105ce7 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105ce7 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x105ce7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105cef [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x105cef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x105cef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105cef 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105cef 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x105cef 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105cf7 [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x105cf7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105cf7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105cf7 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105cf7 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x105cf7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105cff [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x105cff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x105cff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105cff 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105cff 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x105cff 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105d07 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x105d07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x105d07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105d07 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105d07 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x105d07 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105d0f [0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x105d0f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105d0f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105d0f 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105d0f 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x105d0f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105d17 [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x105d17 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x105d17 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d17 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105d17 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x105d17 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x105d1f [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x105d1f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x105d1f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d1f 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105d1f 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x105d1f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105d27 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x105d27) (movR64R64Effect 0x105d27 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105d27 7 12).toInstrSpec (mov_r64_r64_effect_step 0x105d27 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x105d2a [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x105d2a) (movR64R64Effect 0x105d2a 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105d2a 6 14).toInstrSpec (mov_r64_r64_effect_step 0x105d2a 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x105d2d [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x105d2d) (movR64R64Effect 0x105d2d 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x105d2d 2 15).toInstrSpec (mov_r64_r64_effect_step 0x105d2d 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x105d30 [0xE8, 0x1B, 0xD7, 0xFF, 0xFF] (PushPre 0x105d30 5) (callEffect (fun _ => 0x103450) 0x105d35)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105d30 0x103450 0x105d35).toInstrSpec (call_rel32_effect_step 0x105d30 0xffffd71b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cef) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cf7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105cff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d07) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d0f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d17) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d1f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d27) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d2a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d2d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d30) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103450) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l105ce7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105ce7 :=
  Rest.liftedBlock (rest_l105ce7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105ce7 x hx)

theorem rest_l105d35 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105d35 bytes_l105d35) (entryMap (live .l105d35))
      4 0x105d35 bytes_l105d35 b_l105d35 := by
  have f0 : InstrSpec 0x105d35 [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x105d35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105d35 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d35 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x105d35 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x105d35 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105d3a [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x105d3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105d3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d3a 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105d3a 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x105d3a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x105d3f [0x80, 0x7C, 0x24, 0x08, 0x00] (LoadPre 0x105d3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105d3f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x105d3f 5 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x105d3f 5 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x105d3f (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d3a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d3f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d44) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x105d44 4 0x1c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105d35 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105d35 :=
  Rest.liftedBlock (rest_l105d35 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105d35 x hx)

theorem rest_l105d46 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105d46 bytes_l105d46) (entryMap (live .l105d46))
      2 0x105d46 bytes_l105d46 b_l105d46 := by
  have f0 : InstrSpec 0x105d46 [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x105d46) (testR64R64Effect 0x105d46 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x105d46 7 7).toInstrSpec (test_r64_r64_effect_step 0x105d46 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d49) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x105d49 4 0xfffffb21) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105d46 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105d46 :=
  Rest.liftedBlock (rest_l105d46 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105d46 x hx)

theorem rest_l105d4f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105d4f bytes_l105d4f) (entryMap (live .l105d4f))
      3 0x105d4f bytes_l105d4f b_l105d4f := by
  have f0 : InstrSpec 0x105d4f [0x48, 0x8B, 0x00] (LoadPre 0x105d4f (fun s => AddrMode.addr (.base 0 .none) s (0x105d4f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x105d4f 0 (.base 0 .none))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105d4f 0 (.base 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x105d4f 0x48 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105d52 [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x105d52) (testR64R64Effect 0x105d52 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x105d52 0 0).toInstrSpec (test_r64_r64_effect_step 0x105d52 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d52) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d55) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x105d55 4 0xfffffb15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l105d4f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105d4f :=
  Rest.liftedBlock (rest_l105d4f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105d4f x hx)

theorem rest_l105d5b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105d5b bytes_l105d5b) (entryMap (live .l105d5b))
      0 0x105d5b bytes_l105d5b b_l105d5b := by
  exact Rest.cut

theorem block_l105d5b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105d5b :=
  Rest.liftedBlock (rest_l105d5b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105d5b x hx)

theorem rest_l105d5d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105d5d bytes_l105d5d) (entryMap (live .l105d5d))
      1 0x105d5d bytes_l105d5d b_l105d5d := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x105d5d 0xfffffb0e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l105d5d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105d5d :=
  Rest.liftedBlock (rest_l105d5d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105d5d x hx)

theorem rest_l105d62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105d62 bytes_l105d62) (entryMap (live .l105d62))
      17 0x105d62 bytes_l105d62 b_l105d62 := by
  have f0 : InstrSpec 0x105d62 [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x105d62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105d62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d62 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105d62 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x105d62 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105d67 [0x48, 0x89, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x105d67 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105d67 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d67 1 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105d67 1 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x105d67 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105d6f [0x48, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x105d6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105d6f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d6f 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105d6f 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x105d6f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105d74 [0x48, 0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x105d74 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105d74 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d74 1 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105d74 1 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x105d74 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105d7c [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x105d7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105d7c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d7c 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105d7c 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x105d7c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105d81 [0x48, 0x89, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x105d81 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x105d81 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d81 1 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105d81 1 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x105d81 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x105d89 [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x105d89 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105d89 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d89 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105d89 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x105d89 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105d8e [0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x105d8e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105d8e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d8e 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105d8e 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x105d8e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105d96 [0x48, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x105d96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105d96 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d96 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105d96 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x105d96 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x105d9b [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x105d9b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105d9b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d9b 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x105d9b 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x105d9b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x105da0 [0x48, 0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x105da0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x105da0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105da0 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105da0 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x105da0 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x105da8 [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x105da8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x105da8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105da8 1 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105da8 1 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x105da8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105db0 [0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x105db0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105db0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105db0 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105db0 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x105db0 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x105db8 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x105db8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x105db8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105db8 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105db8 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x105db8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x105dc0 [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105dc0) (leaR64Effect 0x105dc0 7 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105dc0 7 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x105dc0 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x105dc8 [0x48, 0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105dc8) (leaR64Effect 0x105dc8 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105dc8 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x105dc8 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x105dd0 [0xE8, 0x5B, 0x40, 0x00, 0x00] (PushPre 0x105dd0 5) (callEffect (fun _ => 0x109e30) 0x105dd5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105dd0 0x109e30 0x105dd5).toInstrSpec (call_rel32_effect_step 0x105dd0 0x405b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d67) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d6f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d74) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d7c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d81) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d89) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d8e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d96) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105d9b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105da0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105da8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105db0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105db8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dc0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dc8) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (6, 75), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dd0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 65), (2, 67), (3, 3), (4, 77), (5, 5), (6, 75), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e30) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l105d62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105d62 :=
  Rest.liftedBlock (rest_l105d62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105d62 x hx)

theorem rest_l105dd5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105dd5 bytes_l105dd5) (entryMap (live .l105dd5))
      4 0x105dd5 bytes_l105dd5 b_l105dd5 := by
  have f0 : InstrSpec 0x105dd5 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x105dd5) (leaR64Effect 0x105dd5 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105dd5 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105dd5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105dda [0x48, 0x8D, 0x9C, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105dda) (leaR64Effect 0x105dda 3 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x105dda 3 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x105dda 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105de2 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x105de2) (movR64R64Effect 0x105de2 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x105de2 6 3).toInstrSpec (mov_r64_r64_effect_step 0x105de2 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105de5 [0xE8, 0x66, 0xA5, 0x01, 0x00] (PushPre 0x105de5 5) (callEffect (fun _ => 0x120350) 0x105dea)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105de5 0x120350 0x105dea).toInstrSpec (call_rel32_effect_step 0x105de5 0x1a566 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dda) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 55), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105de2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 55), (4, 4), (5, 5), (6, 57), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105de5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 55), (4, 59), (5, 5), (6, 57), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120350) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l105dd5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105dd5 :=
  Rest.liftedBlock (rest_l105dd5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105dd5 x hx)

theorem rest_l105dea [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105dea bytes_l105dea) (entryMap (live .l105dea))
      2 0x105dea bytes_l105dea b_l105dea := by
  have f0 : InstrSpec 0x105dea [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x105dea) (movR64R64Effect 0x105dea 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105dea 7 3).toInstrSpec (mov_r64_r64_effect_step 0x105dea 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105ded [0xE8, 0xBE, 0xA5, 0x01, 0x00] (PushPre 0x105ded 5) (callEffect (fun _ => 0x1203b0) 0x105df2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105ded 0x1203b0 0x105df2).toInstrSpec (call_rel32_effect_step 0x105ded 0x1a5be (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ded) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203b0) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l105dea [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105dea :=
  Rest.liftedBlock (rest_l105dea code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105dea x hx)

theorem rest_l105df2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105df2 bytes_l105df2) (entryMap (live .l105df2))
      2 0x105df2 bytes_l105df2 b_l105df2 := by
  have f0 : InstrSpec 0x105df2 [0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105df2) (leaR64Effect 0x105df2 7 (.sib 4 none 0 (.d32 0x1c8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105df2 7 (.sib 4 none 0 (.d32 0x1c8))).toInstrSpec (lea_r64_effect_step 0x105df2 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1c8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105dfa [0xE8, 0x71, 0x43, 0x00, 0x00] (PushPre 0x105dfa 5) (callEffect (fun _ => 0x10a170) 0x105dff)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105dfa 0x10a170 0x105dff).toInstrSpec (call_rel32_effect_step 0x105dfa 0x4371 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105dfa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 55), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a170) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l105df2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105df2 :=
  Rest.liftedBlock (rest_l105df2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105df2 x hx)

theorem rest_l105dff [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105dff bytes_l105dff) (entryMap (live .l105dff))
      3 0x105dff bytes_l105dff b_l105dff := by
  have f0 : InstrSpec 0x105dff [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x105dff) (leaR64Effect 0x105dff 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x105dff 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105dff 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105e04 [0x48, 0x8D, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105e04) (leaR64Effect 0x105e04 6 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105e04 6 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x105e04 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105e0c [0xE8, 0x7F, 0xEE, 0xFF, 0xFF] (PushPre 0x105e0c 5) (callEffect (fun _ => 0x104c90) 0x105e11)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105e0c 0x104c90 0x105e11).toInstrSpec (call_rel32_effect_step 0x105e0c 0xffffee7f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e04) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e0c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l105dff [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105dff :=
  Rest.liftedBlock (rest_l105dff code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105dff x hx)

theorem rest_l105e11_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x105e11 bytes_l105e11) [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]
      14 0x105e8d bytes_l105e11_1 b_l105e11_1 := by
  have f20 : InstrSpec 0x105e8d [0x48, 0x89, 0x70, 0x28] (StorePre 0x105e8d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x105e8d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e8d 6 (.base 0 (.d8 0x28)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e8d 6 (.base 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x105e8d 0x48 (by decide) 6 (.base 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x105e91 [0x48, 0x89, 0x78, 0x20] (StorePre 0x105e91 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x105e91 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e91 7 (.base 0 (.d8 0x20)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e91 7 (.base 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x105e91 0x48 (by decide) 7 (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x105e95 [0x4C, 0x89, 0x40, 0x18] (StorePre 0x105e95 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x105e95 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e95 8 (.base 0 (.d8 0x18)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e95 8 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x105e95 0x4c (by decide) 0 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x105e99 [0x4C, 0x89, 0x48, 0x08] (StorePre 0x105e99 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x105e99 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e99 9 (.base 0 (.d8 0x8)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e99 9 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x105e99 0x4c (by decide) 1 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x105e9d [0x4C, 0x89, 0x50, 0x10] (StorePre 0x105e9d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x105e9d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e9d 10 (.base 0 (.d8 0x10)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e9d 10 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x105e9d 0x4c (by decide) 2 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x105ea1 [0x48, 0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105ea1 7 (fun s => AddrMode.addr (.base 0 .none) s (0x105ea1 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x105ea1 (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105ea1 (.base 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105ea1 0x48 (by decide) (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x105ea8 [0x48, 0x81, 0xC4, 0xF8, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x105ea8) (addR64Imm32Effect 0x105ea8 4 0x2f8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x105ea8 4 0x2f8).toInstrSpec (add_r64_imm32_effect_step 0x105ea8 0x48 0xc4 0x2f8 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x105eaf [0x5B] (PopPre 0x105eaf) (popR64Effect 0x105eaf 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x105eaf 1 3).toInstrSpec (pop_r64_effect_step 0x105eaf 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f28 : InstrSpec 0x105eb0 [0x41, 0x5C] (PopPre 0x105eb0) (popR64Effect 0x105eb0 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x105eb0 2 12).toInstrSpec (pop_r64_rex_effect_step 0x105eb0 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f29 : InstrSpec 0x105eb2 [0x41, 0x5D] (PopPre 0x105eb2) (popR64Effect 0x105eb2 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x105eb2 2 13).toInstrSpec (pop_r64_rex_effect_step 0x105eb2 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f30 : InstrSpec 0x105eb4 [0x41, 0x5E] (PopPre 0x105eb4) (popR64Effect 0x105eb4 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x105eb4 2 14).toInstrSpec (pop_r64_rex_effect_step 0x105eb4 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f31 : InstrSpec 0x105eb6 [0x41, 0x5F] (PopPre 0x105eb6) (popR64Effect 0x105eb6 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x105eb6 2 15).toInstrSpec (pop_r64_rex_effect_step 0x105eb6 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f32 : InstrSpec 0x105eb8 [0x5D] (PopPre 0x105eb8) (popR64Effect 0x105eb8 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x105eb8 1 5).toInstrSpec (pop_r64_effect_step 0x105eb8 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f33 : InstrSpec 0x105eb9 [0xC3] (RetPre 0x105eb9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x105eb9).toInstrSpec (ret_effect_step 0x105eb9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e91) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e95) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e99) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e9d) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ea1) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105ea8) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 88), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eaf) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f27 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 91) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 92) (ρ' := [(0, 77), (1, 56), (2, 59), (3, 90), (4, 91), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb0) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f28 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 94) f28 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 95) (ρ' := [(0, 77), (1, 56), (2, 59), (3, 90), (4, 94), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (12, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb2) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f29 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 97) f29 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 98) (ρ' := [(0, 77), (1, 56), (2, 59), (3, 90), (4, 97), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (12, 93), (13, 96), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb4) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f30 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f30 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 77), (1, 56), (2, 59), (3, 90), (4, 100), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (12, 93), (13, 96), (14, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb6) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f31 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f31 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 77), (1, 56), (2, 59), (3, 90), (4, 103), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb8) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f32 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f32 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 107) (ρ' := [(0, 77), (1, 56), (2, 59), (3, 90), (4, 106), (5, 105), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105eb9) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f33 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 109) f33 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 110) (ρ' := [(0, 77), (1, 56), (2, 59), (3, 90), (4, 109), (5, 105), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) f33 (by decide) rfl rfl rfl (by decide)

theorem rest_l105e11 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105e11 bytes_l105e11) (entryMap (live .l105e11))
      34 0x105e11 bytes_l105e11 b_l105e11 := by
  have f0 : InstrSpec 0x105e11 [0x4C, 0x8B, 0x5C, 0x24, 0x40] (LoadPre 0x105e11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105e11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e11 11 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x105e11 11 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x105e11 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105e16 [0x4C, 0x89, 0x9C, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x105e16 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105e16 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e16 11 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e16 11 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x105e16 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105e1e [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x105e1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105e1e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e1e 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105e1e 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x105e1e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105e23 [0x48, 0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x105e23 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105e23 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e23 1 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e23 1 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x105e23 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105e2b [0x48, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x105e2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105e2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e2b 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x105e2b 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x105e2b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105e30 [0x48, 0x89, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x105e30 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x105e30 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e30 2 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e30 2 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x105e30 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x105e38 [0x48, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x105e38 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105e38 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e38 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x105e38 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x105e38 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105e3d [0x48, 0x89, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x105e3d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105e3d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e3d 6 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e3d 6 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x105e3d 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105e45 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x105e45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105e45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e45 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x105e45 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x105e45 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x105e4a [0x48, 0x89, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x105e4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x105e4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e4a 7 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e4a 7 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x105e4a 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x105e52 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x105e52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105e52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e52 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x105e52 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x105e52 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x105e57 [0x4C, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x105e57 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x105e57 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e57 8 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e57 8 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x105e57 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105e5f [0x4C, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x105e5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105e5f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e5f 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x105e5f 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x105e5f 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x105e64 [0x4C, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x105e64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105e64 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e64 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x105e64 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x105e64 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x105e69 [0x4C, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x105e69 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x105e69 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e69 10 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e69 10 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x105e69 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x105e71 [0x4C, 0x89, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x105e71 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105e71 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e71 9 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e71 9 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x105e71 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x105e79 [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x01, 0x00, 0x00] (LoadPre 0x105e79 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x105e79 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105e79 0 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x105e79 0 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_r64_m64_effect_step 0x105e79 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x105e81 [0x4C, 0x89, 0x58, 0x40] (StorePre 0x105e81 4 (fun s => AddrMode.addr (.base 0 (.d8 0x40)) s (0x105e81 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e81 11 (.base 0 (.d8 0x40)))
      [.gpr 11, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e81 11 (.base 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x105e81 0x4c (by decide) 3 (.base 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x105e85 [0x48, 0x89, 0x48, 0x38] (StorePre 0x105e85 4 (fun s => AddrMode.addr (.base 0 (.d8 0x38)) s (0x105e85 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e85 1 (.base 0 (.d8 0x38)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e85 1 (.base 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x105e85 0x48 (by decide) 1 (.base 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x105e89 [0x48, 0x89, 0x50, 0x30] (StorePre 0x105e89 4 (fun s => AddrMode.addr (.base 0 (.d8 0x30)) s (0x105e89 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e89 2 (.base 0 (.d8 0x30)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x105e89 2 (.base 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x105e89 0x48 (by decide) 2 (.base 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e16) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e1e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 56), (4, 4), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e23) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(1, 56), (4, 4), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e2b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 56), (2, 59), (4, 4), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e30) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(1, 56), (2, 59), (4, 4), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e38) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e3d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e45) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e4a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e52) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e57) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e5f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e64) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e69) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e71) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e79) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e81) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e85) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e89) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 77), (1, 56), (2, 59), (4, 4), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105e8d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l105e11_1 code

theorem block_l105e11 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105e11 :=
  Rest.liftedBlock (rest_l105e11 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105e11 x hx)

theorem rest_l105eba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105eba bytes_l105eba) (entryMap (live .l105eba))
      4 0x105eba bytes_l105eba b_l105eba := by
  have f0 : InstrSpec 0x105eba [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00] (StorePre 0x105eba 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105eba + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105eba (.sib 4 none 0 (.d8 0x8)) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105eba (.sib 4 none 0 (.d8 0x8)) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x105eba 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105ec3 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x105ec3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105ec3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105ec3 (.sib 4 none 0 (.d8 0x10)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105ec3 (.sib 4 none 0 (.d8 0x10)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x105ec3 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105ecc [0x48, 0x89, 0x6C, 0x24, 0x18] (StorePre 0x105ecc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105ecc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ecc 5 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105ecc 5 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x105ecc 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x105ec3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x105ecc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5)]) (p' := 0x105ed1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 56) (jmp_rel8_effect_step 0x105ed1 0x36 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l105eba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105eba :=
  Rest.liftedBlock (rest_l105eba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105eba x hx)

theorem rest_l105ed3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105ed3 bytes_l105ed3) (entryMap (live .l105ed3))
      6 0x105ed3 bytes_l105ed3 b_l105ed3 := by
  have f0 : InstrSpec 0x105ed3 [0x48, 0x8D, 0xB4, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105ed3) (leaR64Effect 0x105ed3 6 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105ed3 6 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x105ed3 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105edb [0x31, 0xFF] (fun s => s.RIP = 0x105edb) (xorR32R32Effect 0x105edb 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105edb 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x105edb 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x105edd [0x48, 0xC7, 0xC2, 0xE8, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x105edd) (movR64Imm32Effect 0x105edd 2 0x2022e8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x105edd 2 0x2022e8).toInstrSpec (mov_r64_imm32_effect_step 0x105edd 0x48 0xc2 (by decide) (by decide) (by decide) 0x2022e8) pre_rip
  have f3 : InstrSpec 0x105ee4 [0x31, 0xC9] (fun s => s.RIP = 0x105ee4) (xorR32R32Effect 0x105ee4 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105ee4 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x105ee4 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x105ee6 [0x49, 0xC7, 0xC1, 0xF0, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x105ee6) (movR64Imm32Effect 0x105ee6 9 0x2022f0)
      [] [] [.reg 9, .rip] :=
    (movR64Imm32Effect_footprint 0x105ee6 9 0x2022f0).toInstrSpec (mov_r64_imm32_effect_step 0x105ee6 0x49 0xc1 (by decide) (by decide) (by decide) 0x2022f0) pre_rip
  have f5 : InstrSpec 0x105eed [0xE8, 0x16, 0xF5, 0x00, 0x00] (PushPre 0x105eed 5) (callEffect (fun _ => 0x115408) 0x105ef2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105eed 0x115408 0x105ef2).toInstrSpec (call_rel32_effect_step 0x105eed 0xf516 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)]) (p' := 0x105edb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x105edd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x105ee4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8)]) (p' := 0x105ee6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 57), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)]) (p' := 0x105eed) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 59), (2, 57), (4, 63), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)]) (p' := 0x115408) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l105ed3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105ed3 :=
  Rest.liftedBlock (rest_l105ed3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105ed3 x hx)

theorem rest_l105ef2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105ef2 bytes_l105ef2) (entryMap (live .l105ef2))
      3 0x105ef2 bytes_l105ef2 b_l105ef2 := by
  have f0 : InstrSpec 0x105ef2 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00] (StorePre 0x105ef2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105ef2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105ef2 (.sib 4 none 0 (.d8 0x8)) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105ef2 (.sib 4 none 0 (.d8 0x8)) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x105ef2 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105efb [0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x105efb 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105efb + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105efb (.sib 4 none 0 (.d8 0x10)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105efb (.sib 4 none 0 (.d8 0x10)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x105efb 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x105f04 [0x4C, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x105f04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105f04 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f04 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105f04 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x105f04 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5), (15, 15)]) (p' := 0x105efb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (15, 15)]) (p' := 0x105f04) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (15, 15)]) (p' := 0x105f09) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l105ef2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105ef2 :=
  Rest.liftedBlock (rest_l105ef2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105ef2 x hx)

theorem rest_l105f09 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105f09 bytes_l105f09) (entryMap (live .l105f09))
      5 0x105f09 bytes_l105f09 b_l105f09 := by
  have f0 : InstrSpec 0x105f09 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x105f09 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105f09 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105f09 (.sib 4 none 0 (.d8 0x20)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105f09 (.sib 4 none 0 (.d8 0x20)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x105f09 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x105f12 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x105f12) (leaR64Effect 0x105f12 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x105f12 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x105f12 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x105f17 [0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00] (fun s => s.RIP = 0x105f17) (movR64Imm32Effect 0x105f17 7 0x20028f)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x105f17 7 0x20028f).toInstrSpec (mov_r64_imm32_effect_step 0x105f17 0x48 0xc7 (by decide) (by decide) (by decide) 0x20028f) pre_rip
  have f3 : InstrSpec 0x105f1e [0x48, 0xC7, 0xC2, 0x18, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x105f1e) (movR64Imm32Effect 0x105f1e 2 0x202518)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x105f1e 2 0x202518).toInstrSpec (mov_r64_imm32_effect_step 0x105f1e 0x48 0xc2 (by decide) (by decide) (by decide) 0x202518) pre_rip
  have f4 : InstrSpec 0x105f25 [0xE8, 0x46, 0x38, 0x02, 0x00] (PushPre 0x105f25 5) (callEffect (fun _ => 0x129770) 0x105f2a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105f25 0x129770 0x105f2a).toInstrSpec (call_rel32_effect_step 0x105f25 0x23846 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x105f12) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (6, 54)]) (p' := 0x105f17) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(4, 4), (5, 5), (6, 54), (7, 56)]) (p' := 0x105f1e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 58), (4, 4), (5, 5), (6, 54), (7, 56)]) (p' := 0x105f25) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 58), (4, 60), (5, 5), (6, 54), (7, 56)]) (p' := 0x129770) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l105f09 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105f09 :=
  Rest.liftedBlock (rest_l105f09 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105f09 x hx)

theorem rest_l105f2a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105f2a bytes_l105f2a) (entryMap (live .l105f2a))
      15 0x105f2a bytes_l105f2a b_l105f2a := by
  have f0 : InstrSpec 0x105f2a [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x105f2a) (fun _ => nopEffect 0x105f2a 6)
      [] [] [.rip] :=
    (nopEffect_footprint 0x105f2a 6).toInstrSpec (nop_m_effect_step 0x105f2a [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x105f30 [0x55] (PushPre 0x105f30 1) (pushR64Effect 0x105f30 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f30 1 5).toInstrSpec (push_r64_effect_step 0x105f30 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x105f31 [0x41, 0x57] (PushPre 0x105f31 2) (pushR64Effect 0x105f31 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f31 2 15).toInstrSpec (push_r64_rex_effect_step 0x105f31 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x105f33 [0x41, 0x56] (PushPre 0x105f33 2) (pushR64Effect 0x105f33 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f33 2 14).toInstrSpec (push_r64_rex_effect_step 0x105f33 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x105f35 [0x41, 0x55] (PushPre 0x105f35 2) (pushR64Effect 0x105f35 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f35 2 13).toInstrSpec (push_r64_rex_effect_step 0x105f35 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x105f37 [0x41, 0x54] (PushPre 0x105f37 2) (pushR64Effect 0x105f37 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f37 2 12).toInstrSpec (push_r64_rex_effect_step 0x105f37 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x105f39 [0x53] (PushPre 0x105f39 1) (pushR64Effect 0x105f39 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105f39 1 3).toInstrSpec (push_r64_effect_step 0x105f39 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x105f3a [0x48, 0x81, 0xEC, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x105f3a) (subR64Imm32Effect 0x105f3a 4 0x158)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x105f3a 4 0x158).toInstrSpec (sub_r64_imm32_effect_step 0x105f3a 0x48 0xec 0x158 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x105f41 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x105f41) (movR64R64Effect 0x105f41 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x105f41 14 6).toInstrSpec (mov_r64_r64_effect_step 0x105f41 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x105f44 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x105f44 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105f44 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f44 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105f44 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x105f44 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x105f49 [0x48, 0x8B, 0x2E] (LoadPre 0x105f49 (fun s => AddrMode.addr (.base 6 .none) s (0x105f49 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x105f49 5 (.base 6 .none))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x105f49 5 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x105f49 0x48 (by decide) 5 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x105f4c [0x4C, 0x8B, 0x6E, 0x08] (LoadPre 0x105f4c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x105f4c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105f4c 13 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x105f4c 13 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x105f4c 0x4c (by decide) 5 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x105f50 [0x4C, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105f50) (leaR64Effect 0x105f50 15 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x105f50 15 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x105f50 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x105f58 [0x4C, 0x8D, 0x64, 0x24, 0x68] (fun s => s.RIP = 0x105f58) (leaR64Effect 0x105f58 12 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x105f58 12 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x105f58 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f30) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f31) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f33) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f35) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f37) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f39) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 2), (3, 3), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f3a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f41) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f44) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f49) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f4c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 73), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f50) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 73), (14, 68), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f58) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 73), (14, 68), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105f5d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 79) (jmp_rel32_effect_step 0x105f5d 0xa7 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l105f2a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105f2a :=
  Rest.liftedBlock (rest_l105f2a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105f2a x hx)

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

theorem_by block_l104f20_eval :
    program.runBlock (dialect code) ⟨.l104f20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104fa4_eval :
    program.runBlock (dialect code) ⟨.l104fa4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104fb0_eval :
    program.runBlock (dialect code) ⟨.l104fb0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104fbc_eval :
    program.runBlock (dialect code) ⟨.l104fbc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105051_eval :
    program.runBlock (dialect code) ⟨.l105051, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10505d_eval :
    program.runBlock (dialect code) ⟨.l10505d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105069_eval :
    program.runBlock (dialect code) ⟨.l105069, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1050a9_eval :
    program.runBlock (dialect code) ⟨.l1050a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1050ad_eval :
    program.runBlock (dialect code) ⟨.l1050ad, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1050c1_eval :
    program.runBlock (dialect code) ⟨.l1050c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10513d_eval :
    program.runBlock (dialect code) ⟨.l10513d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105145_eval :
    program.runBlock (dialect code) ⟨.l105145, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10518b_eval :
    program.runBlock (dialect code) ⟨.l10518b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10519d_eval :
    program.runBlock (dialect code) ⟨.l10519d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1051b1_eval :
    program.runBlock (dialect code) ⟨.l1051b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105216_eval :
    program.runBlock (dialect code) ⟨.l105216, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105256_eval :
    program.runBlock (dialect code) ⟨.l105256, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10526c_eval :
    program.runBlock (dialect code) ⟨.l10526c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10527f_eval :
    program.runBlock (dialect code) ⟨.l10527f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105292_eval :
    program.runBlock (dialect code) ⟨.l105292, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105306_eval :
    program.runBlock (dialect code) ⟨.l105306, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10530e_eval :
    program.runBlock (dialect code) ⟨.l10530e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105357_eval :
    program.runBlock (dialect code) ⟨.l105357, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105367_eval :
    program.runBlock (dialect code) ⟨.l105367, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10536b_eval :
    program.runBlock (dialect code) ⟨.l10536b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10536f_eval :
    program.runBlock (dialect code) ⟨.l10536f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10537c_eval :
    program.runBlock (dialect code) ⟨.l10537c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10537f_eval :
    program.runBlock (dialect code) ⟨.l10537f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105393_eval :
    program.runBlock (dialect code) ⟨.l105393, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105398_eval :
    program.runBlock (dialect code) ⟨.l105398, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1053af_eval :
    program.runBlock (dialect code) ⟨.l1053af, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1053cb_eval :
    program.runBlock (dialect code) ⟨.l1053cb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1053d5_eval :
    program.runBlock (dialect code) ⟨.l1053d5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1053ef_eval :
    program.runBlock (dialect code) ⟨.l1053ef, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105415_eval :
    program.runBlock (dialect code) ⟨.l105415, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1054a6_eval :
    program.runBlock (dialect code) ⟨.l1054a6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1054c0_eval :
    program.runBlock (dialect code) ⟨.l1054c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1054d1_eval :
    program.runBlock (dialect code) ⟨.l1054d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1054e9_eval :
    program.runBlock (dialect code) ⟨.l1054e9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105509_eval :
    program.runBlock (dialect code) ⟨.l105509, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105512_eval :
    program.runBlock (dialect code) ⟨.l105512, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105524_eval :
    program.runBlock (dialect code) ⟨.l105524, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105546_eval :
    program.runBlock (dialect code) ⟨.l105546, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10555a_eval :
    program.runBlock (dialect code) ⟨.l10555a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105572_eval :
    program.runBlock (dialect code) ⟨.l105572, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105575_eval :
    program.runBlock (dialect code) ⟨.l105575, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1055a2_eval :
    program.runBlock (dialect code) ⟨.l1055a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1055af_eval :
    program.runBlock (dialect code) ⟨.l1055af, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1055b1_eval :
    program.runBlock (dialect code) ⟨.l1055b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1055bd_eval :
    program.runBlock (dialect code) ⟨.l1055bd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1055bf_eval :
    program.runBlock (dialect code) ⟨.l1055bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105612_eval :
    program.runBlock (dialect code) ⟨.l105612, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10561c_eval :
    program.runBlock (dialect code) ⟨.l10561c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105699_eval :
    program.runBlock (dialect code) ⟨.l105699, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1056d8_eval :
    program.runBlock (dialect code) ⟨.l1056d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105758_eval :
    program.runBlock (dialect code) ⟨.l105758, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10581a_eval :
    program.runBlock (dialect code) ⟨.l10581a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10584e_eval :
    program.runBlock (dialect code) ⟨.l10584e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105870_eval :
    program.runBlock (dialect code) ⟨.l105870, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105886_eval :
    program.runBlock (dialect code) ⟨.l105886, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1058d0_eval :
    program.runBlock (dialect code) ⟨.l1058d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10591b_eval :
    program.runBlock (dialect code) ⟨.l10591b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105961_eval :
    program.runBlock (dialect code) ⟨.l105961, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10599c_eval :
    program.runBlock (dialect code) ⟨.l10599c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1059a8_eval :
    program.runBlock (dialect code) ⟨.l1059a8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1059f3_eval :
    program.runBlock (dialect code) ⟨.l1059f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1059fb_eval :
    program.runBlock (dialect code) ⟨.l1059fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105aaa_eval :
    program.runBlock (dialect code) ⟨.l105aaa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105aba_eval :
    program.runBlock (dialect code) ⟨.l105aba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105afc_eval :
    program.runBlock (dialect code) ⟨.l105afc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105b0f_eval :
    program.runBlock (dialect code) ⟨.l105b0f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105b23_eval :
    program.runBlock (dialect code) ⟨.l105b23, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105b62_eval :
    program.runBlock (dialect code) ⟨.l105b62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105b75_eval :
    program.runBlock (dialect code) ⟨.l105b75, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105b88_eval :
    program.runBlock (dialect code) ⟨.l105b88, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105bf2_eval :
    program.runBlock (dialect code) ⟨.l105bf2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105bfa_eval :
    program.runBlock (dialect code) ⟨.l105bfa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105c3e_eval :
    program.runBlock (dialect code) ⟨.l105c3e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105cc5_eval :
    program.runBlock (dialect code) ⟨.l105cc5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105cd6_eval :
    program.runBlock (dialect code) ⟨.l105cd6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105ce7_eval :
    program.runBlock (dialect code) ⟨.l105ce7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105d35_eval :
    program.runBlock (dialect code) ⟨.l105d35, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105d46_eval :
    program.runBlock (dialect code) ⟨.l105d46, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105d4f_eval :
    program.runBlock (dialect code) ⟨.l105d4f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105d5b_eval :
    program.runBlock (dialect code) ⟨.l105d5b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105d5d_eval :
    program.runBlock (dialect code) ⟨.l105d5d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105d62_eval :
    program.runBlock (dialect code) ⟨.l105d62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105dd5_eval :
    program.runBlock (dialect code) ⟨.l105dd5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105dea_eval :
    program.runBlock (dialect code) ⟨.l105dea, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105df2_eval :
    program.runBlock (dialect code) ⟨.l105df2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105dff_eval :
    program.runBlock (dialect code) ⟨.l105dff, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105e11_eval :
    program.runBlock (dialect code) ⟨.l105e11, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105eba_eval :
    program.runBlock (dialect code) ⟨.l105eba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105ed3_eval :
    program.runBlock (dialect code) ⟨.l105ed3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105ef2_eval :
    program.runBlock (dialect code) ⟨.l105ef2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105f09_eval :
    program.runBlock (dialect code) ⟨.l105f09, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105f2a_eval :
    program.runBlock (dialect code) ⟨.l105f2a, args, mem⟩ = _ := by
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

end Steps

end K256.Proofs.Verify.LIR
