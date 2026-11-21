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

theorem rest_l105415 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105415 bytes_l105415) (entryMap (live .l105415))
      2 0x105415 bytes_l105415 b_l105415 := by
  have f0 : InstrSpec 0x105415 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105415) (fun _ => nopEffect 0x105415 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x105415 10).toInstrSpec (nop_m_effect_step 0x105415 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10541f [0x90] (fun s => s.RIP = 0x10541f) (fun _ => nopEffect 0x10541f 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10541f 1).toInstrSpec (nop_effect_step 0x10541f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10541f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105420) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l105415 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105415 :=
  Rest.liftedBlock (rest_l105415 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105415 x hx)

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

end Steps

end K256.Proofs.Signing.LIR
