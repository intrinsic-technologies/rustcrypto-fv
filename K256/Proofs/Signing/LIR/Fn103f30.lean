import K256.Proofs.Generate.LIR.CallPre
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

theorem rest_l103f30_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x103f30 bytes_l103f30) [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x103f99 bytes_l103f30_1 b_l103f30_1 := by
  have f20 : InstrSpec 0x103f99 [0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x103f99 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x103f99 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103f99 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103f99 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x103f99 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x103fa1 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x103fa1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x103fa1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103fa1 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103fa1 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x103fa1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x103fa9 [0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103fa9 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x103fa9 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103fa9 (.sib 4 none 0 (.d32 0xc0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103fa9 (.sib 4 none 0 (.d32 0xc0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103fa9 0x48 (by decide) (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x103fb5 [0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103fb5 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x103fb5 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103fb5 (.sib 4 none 0 (.d32 0xc8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103fb5 (.sib 4 none 0 (.d32 0xc8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103fb5 0x48 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x103fc1 [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103fc1 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x103fc1 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103fc1 (.sib 4 none 0 (.d32 0xd0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103fc1 (.sib 4 none 0 (.d32 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103fc1 0x48 (by decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x103fcd [0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103fcd 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x103fcd + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103fcd (.sib 4 none 0 (.d32 0xd8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103fcd (.sib 4 none 0 (.d32 0xd8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103fcd 0x48 (by decide) (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x103fd9 [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103fd9) (movR32Imm32Effect 0x103fd9 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x103fd9 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x103fd9 0xb8 (by decide) 0x3) pre_rip
  have f27 : InstrSpec 0x103fde [0x66, 0x90] (fun s => s.RIP = 0x103fde) (fun _ => nopEffect 0x103fde 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103fde 2).toInstrSpec (nop_66_effect_step 0x103fde) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fa1) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fa9) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fb5) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fc1) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fcd) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fd9) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fde) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 93), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fe0) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 96) (by decide) rfl

theorem rest_l103f30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f30 bytes_l103f30) (entryMap (live .l103f30))
      28 0x103f30 bytes_l103f30 b_l103f30 := by
  have f0 : InstrSpec 0x103f30 [0x55] (PushPre 0x103f30 1) (pushR64Effect 0x103f30 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103f30 1 5).toInstrSpec (push_r64_effect_step 0x103f30 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103f31 [0x41, 0x57] (PushPre 0x103f31 2) (pushR64Effect 0x103f31 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103f31 2 15).toInstrSpec (push_r64_rex_effect_step 0x103f31 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103f33 [0x41, 0x56] (PushPre 0x103f33 2) (pushR64Effect 0x103f33 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103f33 2 14).toInstrSpec (push_r64_rex_effect_step 0x103f33 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103f35 [0x41, 0x55] (PushPre 0x103f35 2) (pushR64Effect 0x103f35 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103f35 2 13).toInstrSpec (push_r64_rex_effect_step 0x103f35 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103f37 [0x41, 0x54] (PushPre 0x103f37 2) (pushR64Effect 0x103f37 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103f37 2 12).toInstrSpec (push_r64_rex_effect_step 0x103f37 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103f39 [0x53] (PushPre 0x103f39 1) (pushR64Effect 0x103f39 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103f39 1 3).toInstrSpec (push_r64_effect_step 0x103f39 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x103f3a [0x48, 0x81, 0xEC, 0x98, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x103f3a) (subR64Imm32Effect 0x103f3a 4 0x298)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x103f3a 4 0x298).toInstrSpec (sub_r64_imm32_effect_step 0x103f3a 0x48 0xec 0x298 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103f41 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x103f41) (movR64R64Effect 0x103f41 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x103f41 15 2).toInstrSpec (mov_r64_r64_effect_step 0x103f41 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103f44 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x103f44) (movR64R64Effect 0x103f44 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103f44 14 6).toInstrSpec (mov_r64_r64_effect_step 0x103f44 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103f47 [0x48, 0x89, 0xFD] (fun s => s.RIP = 0x103f47) (movR64R64Effect 0x103f47 5 7)
      [.gpr 7] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103f47 5 7).toInstrSpec (mov_r64_r64_effect_step 0x103f47 0x48 0xfd (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103f4a [0x48, 0xC7, 0x84, 0x24, 0x28, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103f4a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x103f4a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103f4a (.sib 4 none 0 (.d32 0x228)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103f4a (.sib 4 none 0 (.d32 0x228)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103f4a 0x48 (by decide) (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x103f56 [0x48, 0xC7, 0x84, 0x24, 0x20, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103f56 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x103f56 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103f56 (.sib 4 none 0 (.d32 0x220)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103f56 (.sib 4 none 0 (.d32 0x220)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103f56 0x48 (by decide) (.sib 4 none 0 (.d32 0x220)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103f62 [0x48, 0xC7, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103f62 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x103f62 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103f62 (.sib 4 none 0 (.d32 0x218)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103f62 (.sib 4 none 0 (.d32 0x218)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103f62 0x48 (by decide) (.sib 4 none 0 (.d32 0x218)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x103f6e [0x48, 0xC7, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103f6e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x103f6e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103f6e (.sib 4 none 0 (.d32 0x210)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103f6e (.sib 4 none 0 (.d32 0x210)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103f6e 0x48 (by decide) (.sib 4 none 0 (.d32 0x210)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x103f7a [0x48, 0x8B, 0x47, 0x18] (LoadPre 0x103f7a (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x103f7a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103f7a 0 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103f7a 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x103f7a 0x48 (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x103f7e [0x48, 0x8B, 0x4F, 0x10] (LoadPre 0x103f7e (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x103f7e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103f7e 1 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103f7e 1 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103f7e 0x48 (by decide) 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x103f82 [0x48, 0x8B, 0x17] (LoadPre 0x103f82 (fun s => AddrMode.addr (.base 7 .none) s (0x103f82 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x103f82 2 (.base 7 .none))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103f82 2 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103f82 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x103f85 [0x48, 0x8B, 0x77, 0x08] (LoadPre 0x103f85 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x103f85 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103f85 6 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103f85 6 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x103f85 0x48 (by decide) 6 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x103f89 [0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x103f89 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x103f89 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103f89 2 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103f89 2 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x103f89 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x103f91 [0x48, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x103f91 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x103f91 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103f91 6 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103f91 6 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x103f91 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f33) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f37) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f39) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f3a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f41) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f44) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f47) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f4a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f56) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f62) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f6e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f7a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (2, 2), (3, 3), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f7e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 79), (2, 2), (3, 3), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f82) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f85) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f89) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f91) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 77), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f99) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l103f30_1 code

theorem block_l103f30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f30 :=
  Rest.liftedBlock (rest_l103f30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f30 x hx)

theorem rest_l103fe0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103fe0 bytes_l103fe0) (entryMap (live .l103fe0))
      7 0x103fe0 bytes_l103fe0 b_l103fe0 := by
  have f0 : InstrSpec 0x103fe0 [0x80, 0xB4, 0x04, 0x9D, 0x00, 0x00, 0x00, 0x36] (StorePre 0x103fe0 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9d)) s (0x103fe0 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x103fe0 8 (.sib 4 (some 0) 0 (.d32 0x9d)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x103fe0 8 (.sib 4 (some 0) 0 (.d32 0x9d)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x103fe0 (.sib 4 (some 0) 0 (.d32 0x9d)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103fe8 [0x80, 0xB4, 0x04, 0x9E, 0x00, 0x00, 0x00, 0x36] (StorePre 0x103fe8 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9e)) s (0x103fe8 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x103fe8 8 (.sib 4 (some 0) 0 (.d32 0x9e)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x103fe8 8 (.sib 4 (some 0) 0 (.d32 0x9e)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x103fe8 (.sib 4 (some 0) 0 (.d32 0x9e)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103ff0 [0x80, 0xB4, 0x04, 0x9F, 0x00, 0x00, 0x00, 0x36] (StorePre 0x103ff0 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9f)) s (0x103ff0 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x103ff0 8 (.sib 4 (some 0) 0 (.d32 0x9f)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x103ff0 8 (.sib 4 (some 0) 0 (.d32 0x9f)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x103ff0 (.sib 4 (some 0) 0 (.d32 0x9f)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x103ff8 [0x80, 0xB4, 0x04, 0xA0, 0x00, 0x00, 0x00, 0x36] (StorePre 0x103ff8 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0xa0)) s (0x103ff8 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x103ff8 8 (.sib 4 (some 0) 0 (.d32 0xa0)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x103ff8 8 (.sib 4 (some 0) 0 (.d32 0xa0)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x103ff8 (.sib 4 (some 0) 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104000 [0x48, 0x83, 0xC0, 0x04] (fun s => s.RIP = 0x104000) (addR64Imm8Effect 0x104000 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104000 0 0x4).toInstrSpec (add_r64_imm8_effect_step 0x104000 0x48 0xc0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104004 [0x48, 0x83, 0xF8, 0x43] (fun s => s.RIP = 0x104004) (cmpR64Imm8Effect 0x104004 0 0x43)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x104004 0 0x43).toInstrSpec (cmp_r64_imm8_effect_step 0x104004 0x48 0xf8 0x43 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fe8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ff0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ff8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104000) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104004) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104008) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x104008 5 0xd6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103fe0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103fe0 :=
  Rest.liftedBlock (rest_l103fe0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103fe0 x hx)

theorem rest_l10400a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10400a bytes_l10400a) (entryMap (live .l10400a))
      14 0x10400a bytes_l10400a b_l10400a := by
  have f0 : InstrSpec 0x10400a [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10400a) (leaR64Effect 0x10400a 7 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10400a 7 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (lea_r64_effect_step 0x10400a 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104012 [0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B] (fun s => s.RIP = 0x104012) (movR64Imm64Effect 0x104012 0 0x5be0cd191f83d9ab)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104012 0 0x5be0cd191f83d9ab).toInstrSpec (mov_r64_imm64_effect_step 0x104012 0x48 0xb8 (by decide) (by decide) 0x5be0cd191f83d9ab) pre_rip
  have f2 : InstrSpec 0x10401c [0x48, 0x89, 0x84, 0x24, 0xA0, 0x01, 0x00, 0x00] (StorePre 0x10401c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10401c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10401c 0 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10401c 0 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_m64_r64_effect_step 0x10401c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104024 [0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B] (fun s => s.RIP = 0x104024) (movR64Imm64Effect 0x104024 0 0x9b05688c510e527f)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104024 0 0x9b05688c510e527f).toInstrSpec (mov_r64_imm64_effect_step 0x104024 0x48 0xb8 (by decide) (by decide) 0x9b05688c510e527f) pre_rip
  have f4 : InstrSpec 0x10402e [0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00] (StorePre 0x10402e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10402e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10402e 0 (.sib 4 none 0 (.d32 0x198)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10402e 0 (.sib 4 none 0 (.d32 0x198))).toInstrSpec (mov_m64_r64_effect_step 0x10402e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x104036 [0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5] (fun s => s.RIP = 0x104036) (movR64Imm64Effect 0x104036 0 0xa54ff53a3c6ef372)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104036 0 0xa54ff53a3c6ef372).toInstrSpec (mov_r64_imm64_effect_step 0x104036 0x48 0xb8 (by decide) (by decide) 0xa54ff53a3c6ef372) pre_rip
  have f6 : InstrSpec 0x104040 [0x48, 0x89, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00] (StorePre 0x104040 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x104040 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104040 0 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104040 0 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (mov_m64_r64_effect_step 0x104040 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x104048 [0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB] (fun s => s.RIP = 0x104048) (movR64Imm64Effect 0x104048 0 0xbb67ae856a09e667)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104048 0 0xbb67ae856a09e667).toInstrSpec (mov_r64_imm64_effect_step 0x104048 0x48 0xb8 (by decide) (by decide) 0xbb67ae856a09e667) pre_rip
  have f8 : InstrSpec 0x104052 [0x48, 0x89, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00] (StorePre 0x104052 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x104052 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104052 0 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104052 0 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_m64_r64_effect_step 0x104052 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10405a [0xC6, 0x84, 0x24, 0x87, 0x01, 0x00, 0x00, 0x00] (StorePre 0x10405a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x187)) s (0x10405a + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x10405a (.sib 4 none 0 (.d32 0x187)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10405a (.sib 4 none 0 (.d32 0x187)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10405a (.sib 4 none 0 (.d32 0x187)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x104062 [0x48, 0xC7, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x104062 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x104062 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104062 (.sib 4 none 0 (.d32 0x1a8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104062 (.sib 4 none 0 (.d32 0x1a8)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x104062 0x48 (by decide) (.sib 4 none 0 (.d32 0x1a8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10406e [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10406e) (leaR64Effect 0x10406e 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10406e 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x10406e 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104076 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104076) (movR32Imm32Effect 0x104076 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104076 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x104076 0xba (by decide) 0x1) pre_rip
  have f13 : InstrSpec 0x10407b [0xE8, 0x60, 0xD8, 0x01, 0x00] (PushPre 0x10407b 5) (callEffect (fun _ => 0x1218e0) 0x104080)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10407b 0x1218e0 0x104080).toInstrSpec (call_rel32_effect_step 0x10407b 0x1d860 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104012) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10401c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104024) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10402e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104036) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104040) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104048) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104052) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10405a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104062) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10406e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (6, 69), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104076) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 1), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10407b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 1), (2, 71), (3, 3), (4, 73), (5, 5), (6, 69), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l10400a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10400a :=
  Rest.liftedBlock (rest_l10400a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10400a x hx)

theorem rest_l104080 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104080 bytes_l104080) (entryMap (live .l104080))
      3 0x104080 bytes_l104080 b_l104080 := by
  have f0 : InstrSpec 0x104080 [0xC6, 0x84, 0x24, 0x87, 0x01, 0x00, 0x00, 0x00] (StorePre 0x104080 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x187)) s (0x104080 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104080 (.sib 4 none 0 (.d32 0x187)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x104080 (.sib 4 none 0 (.d32 0x187)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x104080 (.sib 4 none 0 (.d32 0x187)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104088 [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104088) (movR32Imm32Effect 0x104088 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x104088 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x104088 0xb8 (by decide) 0x3) pre_rip
  have f2 : InstrSpec 0x10408d [0x0F, 0x1F, 0x00] (fun s => s.RIP = 0x10408d) (fun _ => nopEffect 0x10408d 3)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10408d 3).toInstrSpec (nop_m_effect_step 0x10408d [] (by decide) (by decide) (.base 0 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104088) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10408d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104090) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l104080 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104080 :=
  Rest.liftedBlock (rest_l104080 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104080 x hx)

theorem rest_l104090 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104090 bytes_l104090) (entryMap (live .l104090))
      7 0x104090 bytes_l104090 b_l104090 := by
  have f0 : InstrSpec 0x104090 [0x80, 0xB4, 0x04, 0x9D, 0x00, 0x00, 0x00, 0x6A] (StorePre 0x104090 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9d)) s (0x104090 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x104090 8 (.sib 4 (some 0) 0 (.d32 0x9d)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104090 8 (.sib 4 (some 0) 0 (.d32 0x9d)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x104090 (.sib 4 (some 0) 0 (.d32 0x9d)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104098 [0x80, 0xB4, 0x04, 0x9E, 0x00, 0x00, 0x00, 0x6A] (StorePre 0x104098 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9e)) s (0x104098 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x104098 8 (.sib 4 (some 0) 0 (.d32 0x9e)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104098 8 (.sib 4 (some 0) 0 (.d32 0x9e)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x104098 (.sib 4 (some 0) 0 (.d32 0x9e)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1040a0 [0x80, 0xB4, 0x04, 0x9F, 0x00, 0x00, 0x00, 0x6A] (StorePre 0x1040a0 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9f)) s (0x1040a0 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x1040a0 8 (.sib 4 (some 0) 0 (.d32 0x9f)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1040a0 8 (.sib 4 (some 0) 0 (.d32 0x9f)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x1040a0 (.sib 4 (some 0) 0 (.d32 0x9f)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1040a8 [0x80, 0xB4, 0x04, 0xA0, 0x00, 0x00, 0x00, 0x6A] (StorePre 0x1040a8 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0xa0)) s (0x1040a8 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x1040a8 8 (.sib 4 (some 0) 0 (.d32 0xa0)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1040a8 8 (.sib 4 (some 0) 0 (.d32 0xa0)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x1040a8 (.sib 4 (some 0) 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1040b0 [0x48, 0x83, 0xC0, 0x04] (fun s => s.RIP = 0x1040b0) (addR64Imm8Effect 0x1040b0 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1040b0 0 0x4).toInstrSpec (add_r64_imm8_effect_step 0x1040b0 0x48 0xc0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1040b4 [0x48, 0x83, 0xF8, 0x43] (fun s => s.RIP = 0x1040b4) (cmpR64Imm8Effect 0x1040b4 0 0x43)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1040b4 0 0x43).toInstrSpec (cmp_r64_imm8_effect_step 0x1040b4 0x48 0xf8 0x43 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104098) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040a8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040b0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040b4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040b8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1040b8 5 0xd6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104090 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104090 :=
  Rest.liftedBlock (rest_l104090 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104090 x hx)

theorem rest_l1040ba_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x1040ba bytes_l1040ba) [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x104152 bytes_l1040ba_1 b_l1040ba_1 := by
  have f20 : InstrSpec 0x104152 [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104152) (leaR64Effect 0x104152 7 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104152 7 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x104152 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10415a [0x48, 0x8D, 0xB4, 0x24, 0xF0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10415a) (leaR64Effect 0x10415a 6 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10415a 6 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (lea_r64_effect_step 0x10415a 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x104162 [0xBA, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104162) (movR32Imm32Effect 0x104162 5 2 0xa8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104162 5 2 0xa8).toInstrSpec (mov_r32_imm32_effect_step 0x104162 0xba (by decide) 0xa8) pre_rip
  have f23 : InstrSpec 0x104167 [0xFF, 0x15, 0x63, 0xFC, 0x0F, 0x00] (GoesTo (CallMemPre 0x104167 (.rip 0xffc63)) (callEffect (callMemPtr 0x104167 (.rip 0xffc63)) (0x104167 + BitVec.ofNat 64 (callMemLen (.rip 0xffc63)))) 0x12a820) (callEffect (callMemPtr 0x104167 (.rip 0xffc63)) (0x104167 + BitVec.ofNat 64 (callMemLen (.rip 0xffc63))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x104167 (.rip 0xffc63)).toInstrSpec (call_m64_effect_step 0x104167 (.rip 0xffc63) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10415a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104162) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 78), (1, 80), (2, 88), (3, 3), (4, 4), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104167) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 78), (1, 80), (2, 88), (3, 3), (4, 90), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f23 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 92) (by decide) (by decide) rfl rfl

theorem rest_l1040ba [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1040ba bytes_l1040ba) (entryMap (live .l1040ba))
      24 0x1040ba bytes_l1040ba b_l1040ba := by
  have f0 : InstrSpec 0x1040ba [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x1040ba) (leaR64Effect 0x1040ba 7 (.sib 4 none 0 (.d32 0x230)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1040ba 7 (.sib 4 none 0 (.d32 0x230))).toInstrSpec (lea_r64_effect_step 0x1040ba 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x230)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1040c2 [0x48, 0x8D, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1040c2) (leaR64Effect 0x1040c2 6 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1040c2 6 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (lea_r64_effect_step 0x1040c2 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1040ca [0xB9, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1040ca) (movR32Imm32Effect 0x1040ca 5 1 0xd)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1040ca 5 1 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x1040ca 0xb9 (by decide) 0xd) pre_rip
  have f3 : InstrSpec 0x1040cf [0xF3, 0x48, 0xA5] (RepPre 0x1040cf (RepMovsqPre 0x1040cf)) (repMovsqEffect 0x1040cf)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1040cf).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1040cf 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x1040d2 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1040d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1040d2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1040d2 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1040d2 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1040d2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1040da [0x48, 0x89, 0x84, 0x24, 0x28, 0x02, 0x00, 0x00] (StorePre 0x1040da 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x1040da + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1040da 0 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1040da 0 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (mov_m64_r64_effect_step 0x1040da 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1040e2 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x1040e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1040e2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1040e2 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1040e2 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x1040e2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1040ea [0x48, 0x89, 0x84, 0x24, 0x20, 0x02, 0x00, 0x00] (StorePre 0x1040ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x1040ea + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1040ea 0 (.sib 4 none 0 (.d32 0x220)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1040ea 0 (.sib 4 none 0 (.d32 0x220))).toInstrSpec (mov_m64_r64_effect_step 0x1040ea 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x220)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1040f2 [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x1040f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1040f2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1040f2 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1040f2 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x1040f2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1040fa [0x48, 0x89, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00] (StorePre 0x1040fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x1040fa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1040fa 0 (.sib 4 none 0 (.d32 0x218)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1040fa 0 (.sib 4 none 0 (.d32 0x218))).toInstrSpec (mov_m64_r64_effect_step 0x1040fa 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x218)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x104102 [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x104102 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x104102 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104102 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104102 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x104102 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10410a [0x48, 0x89, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00] (StorePre 0x10410a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x10410a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10410a 0 (.sib 4 none 0 (.d32 0x210)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10410a 0 (.sib 4 none 0 (.d32 0x210))).toInstrSpec (mov_m64_r64_effect_step 0x10410a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x210)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x104112 [0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x104112 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x104112 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104112 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104112 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x104112 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10411a [0x48, 0x89, 0x84, 0x24, 0x08, 0x02, 0x00, 0x00] (StorePre 0x10411a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x208)) s (0x10411a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10411a 0 (.sib 4 none 0 (.d32 0x208)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10411a 0 (.sib 4 none 0 (.d32 0x208))).toInstrSpec (mov_m64_r64_effect_step 0x10411a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x208)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x104122 [0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x104122 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x104122 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104122 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104122 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x104122 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10412a [0x48, 0x89, 0x84, 0x24, 0x00, 0x02, 0x00, 0x00] (StorePre 0x10412a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x200)) s (0x10412a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10412a 0 (.sib 4 none 0 (.d32 0x200)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10412a 0 (.sib 4 none 0 (.d32 0x200))).toInstrSpec (mov_m64_r64_effect_step 0x10412a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x200)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x104132 [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x104132 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104132 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104132 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104132 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x104132 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10413a [0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x10413a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10413a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10413a 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10413a 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x10413a 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x104142 [0x48, 0x89, 0x8C, 0x24, 0xF8, 0x01, 0x00, 0x00] (StorePre 0x104142 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f8)) s (0x104142 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104142 1 (.sib 4 none 0 (.d32 0x1f8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104142 1 (.sib 4 none 0 (.d32 0x1f8))).toInstrSpec (mov_m64_r64_effect_step 0x104142 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1f8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x10414a [0x48, 0x89, 0x84, 0x24, 0xF0, 0x01, 0x00, 0x00] (StorePre 0x10414a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x10414a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10414a 0 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10414a 0 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (mov_m64_r64_effect_step 0x10414a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040d2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040da) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040e2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040ea) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040f2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040fa) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104102) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10410a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104112) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10411a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104122) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10412a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104132) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10413a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104142) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10414a) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104152) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1040ba_1 code

theorem block_l1040ba [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1040ba :=
  Rest.liftedBlock (rest_l1040ba hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1040ba x hx)

theorem rest_l10416d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10416d bytes_l10416d) (entryMap (live .l10416d))
      6 0x10416d bytes_l10416d b_l10416d := by
  have f0 : InstrSpec 0x10416d [0x48, 0x8D, 0x75, 0x20] (fun s => s.RIP = 0x10416d) (leaR64Effect 0x10416d 6 (.base 5 (.d8 0x20)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10416d 6 (.base 5 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x10416d 0x48 (by decide) 6 (.base 5 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104171 [0x4C, 0x8D, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104171) (leaR64Effect 0x104171 13 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x104171 13 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x104171 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104179 [0x0F, 0xB6, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00] (LoadPre 0x104179 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104179 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x104179 8 3 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x104179 8 3 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (movzx_r32_m8_effect_step 0x104179 3 (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x104181 [0x48, 0x83, 0xFB, 0x1F] (fun s => s.RIP = 0x104181) (cmpR64Imm8Effect 0x104181 3 0x1f)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x104181 3 0x1f).toInstrSpec (cmp_r64_imm8_effect_step 0x104181 0x48 0xfb 0x1f (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104185 [0x48, 0x89, 0x74, 0x24, 0x70] (StorePre 0x104185 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104185 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104185 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104185 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x104185 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104171) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104179) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 57), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104181) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(3, 57), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104185) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 57), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10418a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x10418a 7 0x454) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10416d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10416d :=
  Rest.liftedBlock (rest_l10416d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10416d x hx)

theorem rest_l104190 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104190 bytes_l104190) (entryMap (live .l104190))
      13 0x104190 bytes_l104190 b_l104190 := by
  have f0 : InstrSpec 0x104190 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x104190 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x104190 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104190 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104190 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104190 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104194 [0x49, 0x89, 0x44, 0x1D, 0x18] (StorePre 0x104194 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x18)) s (0x104194 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104194 0 (.sib 13 (some 3) 0 (.d8 0x18)))
      [.gpr 0, .gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104194 0 (.sib 13 (some 3) 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x104194 0x49 (by decide) 0 (.sib 13 (some 3) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x104199 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x104199 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x104199 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104199 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104199 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104199 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10419d [0x49, 0x89, 0x44, 0x1D, 0x10] (StorePre 0x10419d 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x10)) s (0x10419d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10419d 0 (.sib 13 (some 3) 0 (.d8 0x10)))
      [.gpr 0, .gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10419d 0 (.sib 13 (some 3) 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10419d 0x49 (by decide) 0 (.sib 13 (some 3) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1041a2 [0x48, 0x8B, 0x06] (LoadPre 0x1041a2 (fun s => AddrMode.addr (.base 6 .none) s (0x1041a2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1041a2 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1041a2 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1041a2 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1041a5 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x1041a5 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1041a5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1041a5 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1041a5 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1041a5 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1041a9 [0x49, 0x89, 0x4C, 0x1D, 0x08] (StorePre 0x1041a9 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x8)) s (0x1041a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1041a9 1 (.sib 13 (some 3) 0 (.d8 0x8)))
      [.gpr 1, .gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1041a9 1 (.sib 13 (some 3) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1041a9 0x49 (by decide) 1 (.sib 13 (some 3) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1041ae [0x49, 0x89, 0x44, 0x1D, 0x00] (StorePre 0x1041ae 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x0)) s (0x1041ae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1041ae 0 (.sib 13 (some 3) 0 (.d8 0x0)))
      [.gpr 0, .gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1041ae 0 (.sib 13 (some 3) 0 (.d8 0x0))).toInstrSpec (mov_m64_r64_effect_step 0x1041ae 0x49 (by decide) 0 (.sib 13 (some 3) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1041b3 [0x80, 0xCB, 0x20] (fun s => s.RIP = 0x1041b3) (orR8Imm8Effect 0x1041b3 3 3 0x20)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (orR8Imm8Effect_footprint 0x1041b3 3 3 0x20).toInstrSpec (or_r8_imm8_effect_step 0x1041b3 0xcb 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1041b6 [0x88, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00] (StorePre 0x1041b6 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x1041b6 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1041b6 7 3 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1041b6 7 3 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (mov_m8_r8_effect_step 0x1041b6 3 (by decide) (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1041bd [0x0F, 0xB6, 0xC3] (fun s => s.RIP = 0x1041bd) (movzxR32R8Effect 0x1041bd 3 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x1041bd 3 0 3).toInstrSpec (movzx_r32_r8_effect_step 0x1041bd 0xc3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1041c0 [0x3C, 0x3F] (fun s => s.RIP = 0x1041c0) (cmpAlImm8Effect 0x1041c0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1041c0 0x3f).toInstrSpec (cmp_al_imm8_effect_step 0x1041c0 0x3f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104194) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104199) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10419d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041a2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041a5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041a9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041ae) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041b3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 65), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041b6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (3, 65), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041bd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 61), (3, 65), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041c0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 61), (3, 65), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041c2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 72) (jcc_rel32_effect_step 0x1041c2 4 0x497) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104190 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104190 :=
  Rest.liftedBlock (rest_l104190 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104190 x hx)

theorem rest_l1041c8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1041c8 bytes_l1041c8) (entryMap (live .l1041c8))
      5 0x1041c8 bytes_l1041c8 b_l1041c8 := by
  have f0 : InstrSpec 0x1041c8 [0xC6, 0x84, 0x04, 0xE0, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1041c8 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0xe0)) s (0x1041c8 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x1041c8 (.sib 4 (some 0) 0 (.d32 0xe0)) 0x0)
      [.gpr 4, .gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1041c8 (.sib 4 (some 0) 0 (.d32 0xe0)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1041c8 (.sib 4 (some 0) 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1041d0 [0x8D, 0x58, 0x01] (fun s => s.RIP = 0x1041d0) (leaR32Effect 0x1041d0 3 3 (.base 0 (.d8 0x1)))
      [.gpr 0] [] [.reg 3, .rip] :=
    (leaR32Effect_footprint 0x1041d0 3 3 (.base 0 (.d8 0x1))).toInstrSpec (lea_r32_effect_step 0x1041d0 3 (.base 0 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1041d3 [0x88, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00] (StorePre 0x1041d3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x1041d3 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1041d3 7 3 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1041d3 7 3 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (mov_m8_r8_effect_step 0x1041d3 3 (by decide) (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1041da [0x4D, 0x85, 0xFF] (fun s => s.RIP = 0x1041da) (testR64R64Effect 0x1041da 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1041da 15 15).toInstrSpec (test_r64_r64_effect_step 0x1041da 0x4d 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041d0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041d3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041da) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041dd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x1041dd 4 0x4bf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1041c8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1041c8 :=
  Rest.liftedBlock (rest_l1041c8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1041c8 x hx)

theorem rest_l1041e3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1041e3 bytes_l1041e3) (entryMap (live .l1041e3))
      6 0x1041e3 bytes_l1041e3 b_l1041e3 := by
  have f0 : InstrSpec 0x1041e3 [0x48, 0x89, 0x6C, 0x24, 0x78] (StorePre 0x1041e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1041e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1041e3 5 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1041e3 5 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1041e3 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1041e8 [0x49, 0xC1, 0xE7, 0x04] (fun s => s.RIP = 0x1041e8) (shlR64Effect 0x1041e8 4 15 4)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64Effect_footprint 0x1041e8 4 15 4).toInstrSpec (shl_r64_imm8_effect_step 0x1041e8 0x49 0xe7 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1041ec [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x1041ec) (addR64R64Effect 0x1041ec 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1041ec 15 14).toInstrSpec (add_r64_r64_effect_step 0x1041ec 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1041ef [0x4C, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x1041ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1041ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1041ef 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1041ef 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1041ef 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1041f4 [0x4D, 0x89, 0xF7] (fun s => s.RIP = 0x1041f4) (movR64R64Effect 0x1041f4 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1041f4 15 14).toInstrSpec (mov_r64_r64_effect_step 0x1041f4 0x4d 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041e8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041ef) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041f4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041f7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x1041f7 0x32 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1041e3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1041e3 :=
  Rest.liftedBlock (rest_l1041e3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1041e3 x hx)

theorem rest_l104200 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104200 bytes_l104200) (entryMap (live .l104200))
      5 0x104200 bytes_l104200 b_l104200 := by
  have f0 : InstrSpec 0x104200 [0x89, 0xFD] (fun s => s.RIP = 0x104200) (movR32R32Effect 0x104200 2 5 7)
      [.gpr 7] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x104200 2 5 7).toInstrSpec (mov_r32_r32_effect_step 0x104200 0xfd (by decide)) pre_rip
  have f1 : InstrSpec 0x104202 [0x4C, 0x01, 0xEF] (fun s => s.RIP = 0x104202) (addR64R64Effect 0x104202 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x104202 7 13).toInstrSpec (add_r64_r64_effect_step 0x104202 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104205 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x104205) (movR64R64Effect 0x104205 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104205 6 3).toInstrSpec (mov_r64_r64_effect_step 0x104205 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104208 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x104208) (movR64R64Effect 0x104208 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104208 2 12).toInstrSpec (mov_r64_r64_effect_step 0x104208 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10420b [0xFF, 0x15, 0xBF, 0xFB, 0x0F, 0x00] (GoesTo (CallMemPre 0x10420b (.rip 0xffbbf)) (callEffect (callMemPtr 0x10420b (.rip 0xffbbf)) (0x10420b + BitVec.ofNat 64 (callMemLen (.rip 0xffbbf)))) 0x12a820) (callEffect (callMemPtr 0x10420b (.rip 0xffbbf)) (0x10420b + BitVec.ofNat 64 (callMemLen (.rip 0xffbbf))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10420b (.rip 0xffbbf)).toInstrSpec (call_m64_effect_step 0x10420b (.rip 0xffbbf) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104202) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104205) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104208) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10420b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 53), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l104200 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104200 :=
  Rest.liftedBlock (rest_l104200 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104200 x hx)

theorem rest_l104211 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104211 bytes_l104211) (entryMap (live .l104211))
      5 0x104211 bytes_l104211 b_l104211 := by
  have f0 : InstrSpec 0x104211 [0x41, 0x00, 0xEC] (fun s => s.RIP = 0x104211) (addR8R8Effect 0x104211 3 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (addR8R8Effect_footprint 0x104211 3 12 5).toInstrSpec (add_r8_r8_rex_effect_step 0x104211 0x41 0xec (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104214 [0x44, 0x88, 0xA4, 0x24, 0x1F, 0x01, 0x00, 0x00] (StorePre 0x104214 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104214 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x104214 8 12 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x104214 8 12 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x104214 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10421c [0x49, 0x83, 0xC7, 0x10] (fun s => s.RIP = 0x10421c) (addR64Imm8Effect 0x10421c 15 0x10)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10421c 15 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10421c 0x49 0xc7 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104220 [0x4C, 0x3B, 0x7C, 0x24, 0x08] (LoadPre 0x104220 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104220 + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x104220 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x104220 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (cmp_r64_m64_effect_step 0x104220 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104214) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10421c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104220) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 56), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104225) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x104225 4 0xe1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104211 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104211 :=
  Rest.liftedBlock (rest_l104211 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104211 x hx)

theorem rest_l10422b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10422b bytes_l10422b) (entryMap (live .l10422b))
      8 0x10422b bytes_l10422b b_l10422b := by
  have f0 : InstrSpec 0x10422b [0x49, 0x8B, 0x1F] (LoadPre 0x10422b (fun s => AddrMode.addr (.base 15 .none) s (0x10422b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10422b 3 (.base 15 .none))
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10422b 3 (.base 15 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10422b 0x49 (by decide) 3 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10422e [0x4D, 0x8B, 0x67, 0x08] (LoadPre 0x10422e (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x10422e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10422e 12 (.base 15 (.d8 0x8)))
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10422e 12 (.base 15 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10422e 0x4d (by decide) 4 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104232 [0x0F, 0xB6, 0xBC, 0x24, 0x1F, 0x01, 0x00, 0x00] (LoadPre 0x104232 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104232 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x104232 8 7 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x104232 8 7 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (movzx_r32_m8_effect_step 0x104232 7 (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10423a [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10423a) (movR32Imm32Effect 0x10423a 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10423a 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x10423a 0xba (by decide) 0x40) pre_rip
  have f4 : InstrSpec 0x10423f [0x48, 0x29, 0xFA] (fun s => s.RIP = 0x10423f) (subR64R64Effect 0x10423f 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10423f 2 7).toInstrSpec (sub_r64_r64_effect_step 0x10423f 0x48 0xfa (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104242 [0x4C, 0x89, 0xE5] (fun s => s.RIP = 0x104242) (movR64R64Effect 0x104242 5 12)
      [.gpr 12] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x104242 5 12).toInstrSpec (mov_r64_r64_effect_step 0x104242 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104245 [0x48, 0x29, 0xD5] (fun s => s.RIP = 0x104245) (subR64R64Effect 0x104245 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104245 5 2).toInstrSpec (sub_r64_r64_effect_step 0x104245 0x48 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 53), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10422e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 53), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104232) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 53), (4, 4), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10423a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (3, 53), (4, 4), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10423f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 61), (3, 53), (4, 4), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104242) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 61), (3, 53), (4, 4), (5, 63), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104245) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (2, 61), (3, 53), (4, 4), (5, 65), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104248) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x104248 2 0xb6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10422b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10422b :=
  Rest.liftedBlock (rest_l10422b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10422b x hx)

theorem rest_l10424a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10424a bytes_l10424a) (entryMap (live .l10424a))
      2 0x10424a bytes_l10424a b_l10424a := by
  have f0 : InstrSpec 0x10424a [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x10424a) (testR64R64Effect 0x10424a 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10424a 7 7).toInstrSpec (test_r64_r64_effect_step 0x10424a 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10424d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10424d 4 0xa1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10424a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10424a :=
  Rest.liftedBlock (rest_l10424a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10424a x hx)

theorem rest_l104253 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104253 bytes_l104253) (entryMap (live .l104253))
      4 0x104253 bytes_l104253 b_l104253 := by
  have f0 : InstrSpec 0x104253 [0x4C, 0x8D, 0x24, 0x13] (fun s => s.RIP = 0x104253) (leaR64Effect 0x104253 12 (.sib 3 (some 2) 0 .none))
      [.gpr 3, .gpr 2] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x104253 12 (.sib 3 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x104253 0x4c (by decide) 4 (.sib 3 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104257 [0x4C, 0x01, 0xEF] (fun s => s.RIP = 0x104257) (addR64R64Effect 0x104257 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x104257 7 13).toInstrSpec (add_r64_r64_effect_step 0x104257 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10425a [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x10425a) (movR64R64Effect 0x10425a 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10425a 6 3).toInstrSpec (mov_r64_r64_effect_step 0x10425a 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10425d [0xFF, 0x15, 0x6D, 0xFB, 0x0F, 0x00] (GoesTo (CallMemPre 0x10425d (.rip 0xffb6d)) (callEffect (callMemPtr 0x10425d (.rip 0xffb6d)) (0x10425d + BitVec.ofNat 64 (callMemLen (.rip 0xffb6d)))) 0x12a820) (callEffect (callMemPtr 0x10425d (.rip 0xffb6d)) (0x10425d + BitVec.ofNat 64 (callMemLen (.rip 0xffb6d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10425d (.rip 0xffb6d)).toInstrSpec (call_m64_effect_step 0x10425d (.rip 0xffb6d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104257) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10425a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10425d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l104253 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104253 :=
  Rest.liftedBlock (rest_l104253 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104253 x hx)

theorem rest_l104263 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104263 bytes_l104263) (entryMap (live .l104263))
      5 0x104263 bytes_l104263 b_l104263 := by
  have f0 : InstrSpec 0x104263 [0x48, 0xFF, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x104263 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104263 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104263 8 64 (.sib 4 none 0 (.d32 0x140)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x104263 8 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (inc_m64_effect_step 0x104263 0x48 (by decide) (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10426b [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10426b) (movR32Imm32Effect 0x10426b 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10426b 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10426b 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x104270 [0x48, 0x8D, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104270) (leaR64Effect 0x104270 7 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104270 7 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (lea_r64_effect_step 0x104270 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104278 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x104278) (movR64R64Effect 0x104278 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104278 6 13).toInstrSpec (mov_r64_r64_effect_step 0x104278 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10427b [0xE8, 0x60, 0xD6, 0x01, 0x00] (PushPre 0x10427b 5) (callEffect (fun _ => 0x1218e0) 0x104280)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10427b 0x1218e0 0x104280).toInstrSpec (call_rel32_effect_step 0x10427b 0x1d660 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10426b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104270) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104278) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10427b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l104263 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104263 :=
  Rest.liftedBlock (rest_l104263 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104263 x hx)

theorem rest_l104280 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104280 bytes_l104280) (entryMap (live .l104280))
      6 0x104280 bytes_l104280 b_l104280 := by
  have f0 : InstrSpec 0x104280 [0xC6, 0x84, 0x24, 0x1F, 0x01, 0x00, 0x00, 0x00] (StorePre 0x104280 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104280 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104280 (.sib 4 none 0 (.d32 0x11f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x104280 (.sib 4 none 0 (.d32 0x11f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x104280 (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104288 [0x4C, 0x89, 0xE3] (fun s => s.RIP = 0x104288) (movR64R64Effect 0x104288 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x104288 3 12).toInstrSpec (mov_r64_r64_effect_step 0x104288 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10428b [0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x10428b) (movR64Imm64Effect 0x10428b 1 0x7fffffffffffffc0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10428b 1 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x10428b 0x48 0xb9 (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f3 : InstrSpec 0x104295 [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x104295) (movR64R64Effect 0x104295 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104295 2 5).toInstrSpec (mov_r64_r64_effect_step 0x104295 0x48 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104298 [0x48, 0xC1, 0xEA, 0x06] (fun s => s.RIP = 0x104298) (shrR64Effect 0x104298 4 2 6)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x104298 4 2 6).toInstrSpec (shr_r64_imm8_effect_step 0x104298 0x48 0xea 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104288) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10428b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104295) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 56), (2, 58), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104298) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 61) f4 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x104298 4 2 6 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 56), (2, 60), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10429c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x10429c 4 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104280 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104280 :=
  Rest.liftedBlock (rest_l104280 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104280 x hx)

theorem rest_l10429e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10429e bytes_l10429e) (entryMap (live .l10429e))
      4 0x10429e bytes_l10429e b_l10429e := by
  have f0 : InstrSpec 0x10429e [0x48, 0x01, 0x94, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x10429e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10429e + BitVec.ofNat 64 8)) 8) (addMREffect 0x10429e 8 64 2 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 2, .gpr 4] [] [.flags, .rip] :=
    (addMREffect64_footprint 0x10429e 8 2 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (add_m64_r64_effect_step 0x10429e 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1042a6 [0x48, 0x8D, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1042a6) (leaR64Effect 0x1042a6 7 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1042a6 7 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (lea_r64_effect_step 0x1042a6 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1042ae [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1042ae) (movR64R64Effect 0x1042ae 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1042ae 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1042ae 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1042b1 [0xE8, 0x2A, 0xD6, 0x01, 0x00] (PushPre 0x1042b1 5) (callEffect (fun _ => 0x1218e0) 0x1042b6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1042b1 0x1218e0 0x1042b6).toInstrSpec (call_rel32_effect_step 0x1042b1 0x1d62a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042a6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042ae) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042b1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 60) (by decide) (by decide) rfl rfl

theorem block_l10429e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10429e :=
  Rest.liftedBlock (rest_l10429e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10429e x hx)

theorem rest_l1042b6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1042b6 bytes_l1042b6) (entryMap (live .l1042b6))
      1 0x1042b6 bytes_l1042b6 b_l1042b6 := by
  have f0 : InstrSpec 0x1042b6 [0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x1042b6) (movR64Imm64Effect 0x1042b6 1 0x7fffffffffffffc0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1042b6 1 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x1042b6 0x48 0xb9 (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042c0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1042b6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1042b6 :=
  Rest.liftedBlock (rest_l1042b6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1042b6 x hx)

theorem rest_l1042c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1042c0 bytes_l1042c0) (entryMap (live .l1042c0))
      9 0x1042c0 bytes_l1042c0 b_l1042c0 := by
  have f0 : InstrSpec 0x1042c0 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x1042c0) (movR64R64Effect 0x1042c0 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1042c0 0 5).toInstrSpec (mov_r64_r64_effect_step 0x1042c0 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1042c3 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x1042c3) (andR64R64Effect 0x1042c3 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1042c3 0 1).toInstrSpec (and_r64_r64_effect_step 0x1042c3 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1042c6 [0x83, 0xE5, 0x3F] (fun s => s.RIP = 0x1042c6) (andR32Imm8Effect 0x1042c6 3 5 0x3f)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1042c6 3 5 0x3f).toInstrSpec (and_r32_imm8_effect_step 0x1042c6 0xe5 0x3f (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1042c9 [0x48, 0x01, 0xC3] (fun s => s.RIP = 0x1042c9) (addR64R64Effect 0x1042c9 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1042c9 3 0).toInstrSpec (add_r64_r64_effect_step 0x1042c9 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1042cc [0x40, 0x88, 0xAC, 0x24, 0x1F, 0x01, 0x00, 0x00] (StorePre 0x1042cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x1042cc + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1042cc 8 5 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1042cc 8 5 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1042cc 0x40 (by decide) 5 (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1042d4 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x1042d4) (movR64R64Effect 0x1042d4 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1042d4 7 13).toInstrSpec (mov_r64_r64_effect_step 0x1042d4 0x4c 0xef (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1042d7 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1042d7) (movR64R64Effect 0x1042d7 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1042d7 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1042d7 0x48 0xde (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1042da [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x1042da) (movR64R64Effect 0x1042da 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1042da 2 5).toInstrSpec (mov_r64_r64_effect_step 0x1042da 0x48 0xea (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1042dd [0xFF, 0x15, 0xED, 0xFA, 0x0F, 0x00] (GoesTo (CallMemPre 0x1042dd (.rip 0xffaed)) (callEffect (callMemPtr 0x1042dd (.rip 0xffaed)) (0x1042dd + BitVec.ofNat 64 (callMemLen (.rip 0xffaed)))) 0x12a820) (callEffect (callMemPtr 0x1042dd (.rip 0xffaed)) (0x1042dd + BitVec.ofNat 64 (callMemLen (.rip 0xffaed))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1042dd (.rip 0xffaed)).toInstrSpec (call_m64_effect_step 0x1042dd (.rip 0xffaed) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042c6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (3, 59), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042cc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 1), (3, 59), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042d4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 1), (3, 59), (4, 4), (5, 57), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042d7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 1), (3, 59), (4, 4), (5, 57), (6, 64), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042da) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 1), (2, 66), (3, 59), (4, 4), (5, 57), (6, 64), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042dd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 1), (2, 66), (3, 59), (4, 68), (5, 57), (6, 64), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l1042c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1042c0 :=
  Rest.liftedBlock (rest_l1042c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1042c0 x hx)

theorem rest_l1042e3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1042e3 bytes_l1042e3) (entryMap (live .l1042e3))
      3 0x1042e3 bytes_l1042e3 b_l1042e3 := by
  have f0 : InstrSpec 0x1042e3 [0x49, 0x83, 0xC7, 0x10] (fun s => s.RIP = 0x1042e3) (addR64Imm8Effect 0x1042e3 15 0x10)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1042e3 15 0x10).toInstrSpec (add_r64_imm8_effect_step 0x1042e3 0x49 0xc7 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1042e7 [0x4C, 0x3B, 0x7C, 0x24, 0x08] (LoadPre 0x1042e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1042e7 + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x1042e7 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x1042e7 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (cmp_r64_m64_effect_step 0x1042e7 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042e7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1042ec 5 0xffffff39) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1042e3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1042e3 :=
  Rest.liftedBlock (rest_l1042e3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1042e3 x hx)

theorem rest_l1042f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1042f2 bytes_l1042f2) (entryMap (live .l1042f2))
      1 0x1042f2 bytes_l1042f2 b_l1042f2 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1042f2 0x18 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1042f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1042f2 :=
  Rest.liftedBlock (rest_l1042f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1042f2 x hx)

theorem rest_l1042f4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1042f4 bytes_l1042f4) (entryMap (live .l1042f4))
      5 0x1042f4 bytes_l1042f4 b_l1042f4 := by
  have f0 : InstrSpec 0x1042f4 [0x4C, 0x89, 0xE5] (fun s => s.RIP = 0x1042f4) (movR64R64Effect 0x1042f4 5 12)
      [.gpr 12] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1042f4 5 12).toInstrSpec (mov_r64_r64_effect_step 0x1042f4 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1042f7 [0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x1042f7) (movR64Imm64Effect 0x1042f7 1 0x7fffffffffffffc0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1042f7 1 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x1042f7 0x48 0xb9 (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f2 : InstrSpec 0x104301 [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x104301) (movR64R64Effect 0x104301 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104301 2 5).toInstrSpec (mov_r64_r64_effect_step 0x104301 0x48 0xea (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104304 [0x48, 0xC1, 0xEA, 0x06] (fun s => s.RIP = 0x104304) (shrR64Effect 0x104304 4 2 6)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x104304 4 2 6).toInstrSpec (shr_r64_imm8_effect_step 0x104304 0x48 0xea 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042f7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104301) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104304) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 60) f3 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x104304 4 2 6 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104308) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x104308 5 0x94) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1042f4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1042f4 :=
  Rest.liftedBlock (rest_l1042f4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1042f4 x hx)

theorem rest_l10430a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10430a bytes_l10430a) (entryMap (live .l10430a))
      1 0x10430a bytes_l10430a b_l10430a := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x10430a 0xb4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10430a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10430a :=
  Rest.liftedBlock (rest_l10430a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10430a x hx)

theorem rest_l10430c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10430c bytes_l10430c) (entryMap (live .l10430c))
      5 0x10430c bytes_l10430c b_l10430c := by
  have f0 : InstrSpec 0x10430c [0x48, 0x8D, 0x9C, 0x24, 0xF0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10430c) (leaR64Effect 0x10430c 3 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x10430c 3 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (lea_r64_effect_step 0x10430c 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104314 [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104314) (leaR64Effect 0x104314 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104314 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x104314 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10431c [0xBA, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10431c) (movR32Imm32Effect 0x10431c 5 2 0xa8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10431c 5 2 0xa8).toInstrSpec (mov_r32_imm32_effect_step 0x10431c 0xba (by decide) 0xa8) pre_rip
  have f3 : InstrSpec 0x104321 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x104321) (movR64R64Effect 0x104321 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104321 7 3).toInstrSpec (mov_r64_r64_effect_step 0x104321 0x48 0xdf (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104324 [0xFF, 0x15, 0xA6, 0xFA, 0x0F, 0x00] (GoesTo (CallMemPre 0x104324 (.rip 0xffaa6)) (callEffect (callMemPtr 0x104324 (.rip 0xffaa6)) (0x104324 + BitVec.ofNat 64 (callMemLen (.rip 0xffaa6)))) 0x12a820) (callEffect (callMemPtr 0x104324 (.rip 0xffaa6)) (0x104324 + BitVec.ofNat 64 (callMemLen (.rip 0xffaa6))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x104324 (.rip 0xffaa6)).toInstrSpec (call_m64_effect_step 0x104324 (.rip 0xffaa6) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104314) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10431c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 53), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104321) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 53), (4, 4), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104324) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 53), (4, 61), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10430c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10430c :=
  Rest.liftedBlock (rest_l10430c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10430c x hx)

theorem rest_l10432a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10432a bytes_l10432a) (entryMap (live .l10432a))
      7 0x10432a bytes_l10432a b_l10432a := by
  have f0 : InstrSpec 0x10432a [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10432a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10432a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10432a (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10432a (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10432a 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104333 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104333 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104333 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104333 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104333 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104333 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10433c [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10433c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10433c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10433c (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10433c (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10433c 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104345 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104345 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104345 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104345 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104345 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104345 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10434e [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x10434e) (leaR64Effect 0x10434e 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10434e 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x10434e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104353 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x104353) (movR64R64Effect 0x104353 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104353 7 3).toInstrSpec (mov_r64_r64_effect_step 0x104353 0x48 0xdf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104356 [0xE8, 0xF5, 0x36, 0x00, 0x00] (PushPre 0x104356 5) (callEffect (fun _ => 0x107a50) 0x10435b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104356 0x107a50 0x10435b).toInstrSpec (call_rel32_effect_step 0x104356 0x36f5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104333) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10433c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104345) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10434e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104353) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104356) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a50) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10432a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10432a :=
  Rest.liftedBlock (rest_l10432a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10432a x hx)

theorem rest_l10435b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10435b bytes_l10435b) (entryMap (live .l10435b))
      11 0x10435b bytes_l10435b b_l10435b := by
  have f0 : InstrSpec 0x10435b [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10435b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10435b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10435b 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10435b 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10435b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104360 [0x48, 0x8B, 0x5C, 0x24, 0x78] (LoadPre 0x104360 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x104360 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104360 3 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x104360 3 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x104360 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104365 [0x48, 0x89, 0x43, 0x18] (StorePre 0x104365 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x104365 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104365 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104365 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x104365 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104369 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x104369 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104369 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104369 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104369 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x104369 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10436e [0x48, 0x89, 0x43, 0x10] (StorePre 0x10436e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10436e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10436e 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10436e 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10436e 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x104372 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x104372 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104372 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104372 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104372 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104372 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x104377 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x104377 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104377 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104377 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104377 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104377 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10437c [0x48, 0x89, 0x4B, 0x08] (StorePre 0x10437c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10437c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10437c 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10437c 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10437c 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104380 [0x48, 0x89, 0x03] (StorePre 0x104380 3 (fun s => AddrMode.addr (.base 3 .none) s (0x104380 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x104380 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104380 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x104380 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x104383 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x104383) (movR64R64Effect 0x104383 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104383 7 3).toInstrSpec (mov_r64_r64_effect_step 0x104383 0x48 0xdf (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x104386 [0xE8, 0xE5, 0x05, 0x00, 0x00] (PushPre 0x104386 5) (callEffect (fun _ => 0x104970) 0x10438b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104386 0x104970 0x10438b).toInstrSpec (call_rel32_effect_step 0x104386 0x5e5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104360) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104365) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104369) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10436e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104372) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104377) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10437c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 63), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104380) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104383) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 63), (3, 55), (4, 4), (5, 5), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104386) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 63), (3, 55), (4, 69), (5, 5), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104970) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l10435b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10435b :=
  Rest.liftedBlock (rest_l10435b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10435b x hx)

theorem rest_l10438b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10438b bytes_l10438b) (entryMap (live .l10438b))
      18 0x10438b bytes_l10438b b_l10438b := by
  have f0 : InstrSpec 0x10438b [0x48, 0xC7, 0x84, 0x24, 0x28, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10438b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x10438b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10438b (.sib 4 none 0 (.d32 0x228)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10438b (.sib 4 none 0 (.d32 0x228)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10438b 0x48 (by decide) (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104397 [0x48, 0xC7, 0x84, 0x24, 0x20, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104397 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x104397 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104397 (.sib 4 none 0 (.d32 0x220)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104397 (.sib 4 none 0 (.d32 0x220)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104397 0x48 (by decide) (.sib 4 none 0 (.d32 0x220)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1043a3 [0x48, 0xC7, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1043a3 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x1043a3 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1043a3 (.sib 4 none 0 (.d32 0x218)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1043a3 (.sib 4 none 0 (.d32 0x218)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1043a3 0x48 (by decide) (.sib 4 none 0 (.d32 0x218)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1043af [0x48, 0xC7, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1043af 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x1043af + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1043af (.sib 4 none 0 (.d32 0x210)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1043af (.sib 4 none 0 (.d32 0x210)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1043af 0x48 (by decide) (.sib 4 none 0 (.d32 0x210)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1043bb [0x48, 0x8B, 0x43, 0x18] (LoadPre 0x1043bb (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1043bb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1043bb 0 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1043bb 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1043bb 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1043bf [0x48, 0x8B, 0x4B, 0x10] (LoadPre 0x1043bf (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1043bf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1043bf 1 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1043bf 1 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1043bf 0x48 (by decide) 1 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1043c3 [0x48, 0x8B, 0x13] (LoadPre 0x1043c3 (fun s => AddrMode.addr (.base 3 .none) s (0x1043c3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1043c3 2 (.base 3 .none))
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1043c3 2 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1043c3 0x48 (by decide) 2 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1043c6 [0x48, 0x8B, 0x73, 0x08] (LoadPre 0x1043c6 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1043c6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1043c6 6 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1043c6 6 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1043c6 0x48 (by decide) 6 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1043ca [0x48, 0x89, 0x54, 0x24, 0x30] (StorePre 0x1043ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1043ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1043ca 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1043ca 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1043ca 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1043cf [0x48, 0x89, 0x74, 0x24, 0x38] (StorePre 0x1043cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1043cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1043cf 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1043cf 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1043cf 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1043d4 [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x1043d4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1043d4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1043d4 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1043d4 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1043d4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1043d9 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x1043d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1043d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1043d9 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1043d9 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1043d9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1043de [0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1043de 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1043de + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1043de (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1043de (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1043de 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1043e7 [0x48, 0xC7, 0x44, 0x24, 0x58, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1043e7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1043e7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1043e7 (.sib 4 none 0 (.d8 0x58)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1043e7 (.sib 4 none 0 (.d8 0x58)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1043e7 0x48 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1043f0 [0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1043f0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1043f0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1043f0 (.sib 4 none 0 (.d8 0x60)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1043f0 (.sib 4 none 0 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1043f0 0x48 (by decide) (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1043f9 [0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1043f9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1043f9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1043f9 (.sib 4 none 0 (.d8 0x68)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1043f9 (.sib 4 none 0 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1043f9 0x48 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x104402 [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104402) (movR32Imm32Effect 0x104402 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x104402 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x104402 0xb8 (by decide) 0x3) pre_rip
  have f17 : InstrSpec 0x104407 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104407) (fun _ => nopEffect 0x104407 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x104407 9).toInstrSpec (nop_m_effect_step 0x104407 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104397) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043af) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043bb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043bf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043c3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043c6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043ca) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043cf) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043d4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043d9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043de) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043e7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043f0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043f9) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104402) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104407) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104410) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l10438b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10438b :=
  Rest.liftedBlock (rest_l10438b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10438b x hx)

theorem rest_l104410 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104410 bytes_l104410) (entryMap (live .l104410))
      7 0x104410 bytes_l104410 b_l104410 := by
  have f0 : InstrSpec 0x104410 [0x80, 0x74, 0x04, 0x2D, 0x36] (StorePre 0x104410 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2d)) s (0x104410 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104410 5 (.sib 4 (some 0) 0 (.d8 0x2d)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104410 5 (.sib 4 (some 0) 0 (.d8 0x2d)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x104410 (.sib 4 (some 0) 0 (.d8 0x2d)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104415 [0x80, 0x74, 0x04, 0x2E, 0x36] (StorePre 0x104415 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2e)) s (0x104415 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104415 5 (.sib 4 (some 0) 0 (.d8 0x2e)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104415 5 (.sib 4 (some 0) 0 (.d8 0x2e)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x104415 (.sib 4 (some 0) 0 (.d8 0x2e)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10441a [0x80, 0x74, 0x04, 0x2F, 0x36] (StorePre 0x10441a 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2f)) s (0x10441a + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x10441a 5 (.sib 4 (some 0) 0 (.d8 0x2f)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x10441a 5 (.sib 4 (some 0) 0 (.d8 0x2f)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x10441a (.sib 4 (some 0) 0 (.d8 0x2f)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10441f [0x80, 0x74, 0x04, 0x30, 0x36] (StorePre 0x10441f 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x30)) s (0x10441f + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x10441f 5 (.sib 4 (some 0) 0 (.d8 0x30)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x10441f 5 (.sib 4 (some 0) 0 (.d8 0x30)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x10441f (.sib 4 (some 0) 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104424 [0x48, 0x83, 0xC0, 0x04] (fun s => s.RIP = 0x104424) (addR64Imm8Effect 0x104424 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104424 0 0x4).toInstrSpec (add_r64_imm8_effect_step 0x104424 0x48 0xc0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104428 [0x48, 0x83, 0xF8, 0x43] (fun s => s.RIP = 0x104428) (cmpR64Imm8Effect 0x104428 0 0x43)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x104428 0 0x43).toInstrSpec (cmp_r64_imm8_effect_step 0x104428 0x48 0xf8 0x43 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104415) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10441a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10441f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104424) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104428) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10442c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x10442c 5 0xe2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104410 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104410 :=
  Rest.liftedBlock (rest_l104410 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104410 x hx)

theorem rest_l10442e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10442e bytes_l10442e) (entryMap (live .l10442e))
      15 0x10442e bytes_l10442e b_l10442e := by
  have f0 : InstrSpec 0x10442e [0x4C, 0x8D, 0xAC, 0x24, 0x88, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10442e) (leaR64Effect 0x10442e 13 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10442e 13 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (lea_r64_effect_step 0x10442e 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104436 [0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B] (fun s => s.RIP = 0x104436) (movR64Imm64Effect 0x104436 0 0x5be0cd191f83d9ab)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104436 0 0x5be0cd191f83d9ab).toInstrSpec (mov_r64_imm64_effect_step 0x104436 0x48 0xb8 (by decide) (by decide) 0x5be0cd191f83d9ab) pre_rip
  have f2 : InstrSpec 0x104440 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x01, 0x00, 0x00] (StorePre 0x104440 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x104440 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104440 0 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104440 0 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (mov_m64_r64_effect_step 0x104440 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104448 [0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B] (fun s => s.RIP = 0x104448) (movR64Imm64Effect 0x104448 0 0x9b05688c510e527f)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104448 0 0x9b05688c510e527f).toInstrSpec (mov_r64_imm64_effect_step 0x104448 0x48 0xb8 (by decide) (by decide) 0x9b05688c510e527f) pre_rip
  have f4 : InstrSpec 0x104452 [0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00] (StorePre 0x104452 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x104452 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104452 0 (.sib 4 none 0 (.d32 0x198)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104452 0 (.sib 4 none 0 (.d32 0x198))).toInstrSpec (mov_m64_r64_effect_step 0x104452 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10445a [0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5] (fun s => s.RIP = 0x10445a) (movR64Imm64Effect 0x10445a 0 0xa54ff53a3c6ef372)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10445a 0 0xa54ff53a3c6ef372).toInstrSpec (mov_r64_imm64_effect_step 0x10445a 0x48 0xb8 (by decide) (by decide) 0xa54ff53a3c6ef372) pre_rip
  have f6 : InstrSpec 0x104464 [0x48, 0x89, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00] (StorePre 0x104464 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x104464 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104464 0 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104464 0 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (mov_m64_r64_effect_step 0x104464 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10446c [0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB] (fun s => s.RIP = 0x10446c) (movR64Imm64Effect 0x10446c 0 0xbb67ae856a09e667)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10446c 0 0xbb67ae856a09e667).toInstrSpec (mov_r64_imm64_effect_step 0x10446c 0x48 0xb8 (by decide) (by decide) 0xbb67ae856a09e667) pre_rip
  have f8 : InstrSpec 0x104476 [0x48, 0x89, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00] (StorePre 0x104476 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x104476 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104476 0 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104476 0 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_m64_r64_effect_step 0x104476 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10447e [0xC6, 0x84, 0x24, 0x87, 0x01, 0x00, 0x00, 0x00] (StorePre 0x10447e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x187)) s (0x10447e + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x10447e (.sib 4 none 0 (.d32 0x187)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10447e (.sib 4 none 0 (.d32 0x187)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10447e (.sib 4 none 0 (.d32 0x187)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x104486 [0x48, 0xC7, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x104486 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x104486 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104486 (.sib 4 none 0 (.d32 0x1a8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104486 (.sib 4 none 0 (.d32 0x1a8)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x104486 0x48 (by decide) (.sib 4 none 0 (.d32 0x1a8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x104492 [0x48, 0x8D, 0x74, 0x24, 0x30] (fun s => s.RIP = 0x104492) (leaR64Effect 0x104492 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104492 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x104492 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104497 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104497) (movR32Imm32Effect 0x104497 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104497 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x104497 0xba (by decide) 0x1) pre_rip
  have f13 : InstrSpec 0x10449c [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x10449c) (movR64R64Effect 0x10449c 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10449c 7 13).toInstrSpec (mov_r64_r64_effect_step 0x10449c 0x4c 0xef (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10449f [0xE8, 0x3C, 0xD4, 0x01, 0x00] (PushPre 0x10449f 5) (callEffect (fun _ => 0x1218e0) 0x1044a4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10449f 0x1218e0 0x1044a4).toInstrSpec (call_rel32_effect_step 0x10449f 0x1d43c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104436) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104440) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104448) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104452) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10445a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104464) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10446c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104476) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10447e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104486) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104492) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (6, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104497) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 1), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10449c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 1), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10449f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 64), (1, 1), (2, 71), (3, 3), (4, 75), (5, 5), (6, 69), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l10442e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10442e :=
  Rest.liftedBlock (rest_l10442e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10442e x hx)

theorem rest_l1044a4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1044a4 bytes_l1044a4) (entryMap (live .l1044a4))
      3 0x1044a4 bytes_l1044a4 b_l1044a4 := by
  have f0 : InstrSpec 0x1044a4 [0xC6, 0x84, 0x24, 0x87, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1044a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x187)) s (0x1044a4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x1044a4 (.sib 4 none 0 (.d32 0x187)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1044a4 (.sib 4 none 0 (.d32 0x187)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1044a4 (.sib 4 none 0 (.d32 0x187)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1044ac [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1044ac) (movR32Imm32Effect 0x1044ac 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1044ac 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x1044ac 0xb8 (by decide) 0x3) pre_rip
  have f2 : InstrSpec 0x1044b1 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1044b1) (fun _ => nopEffect 0x1044b1 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1044b1 15).toInstrSpec (nop_m_effect_step 0x1044b1 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044b1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044c0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l1044a4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1044a4 :=
  Rest.liftedBlock (rest_l1044a4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1044a4 x hx)

theorem rest_l1044c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1044c0 bytes_l1044c0) (entryMap (live .l1044c0))
      7 0x1044c0 bytes_l1044c0 b_l1044c0 := by
  have f0 : InstrSpec 0x1044c0 [0x80, 0x74, 0x04, 0x2D, 0x6A] (StorePre 0x1044c0 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2d)) s (0x1044c0 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1044c0 5 (.sib 4 (some 0) 0 (.d8 0x2d)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1044c0 5 (.sib 4 (some 0) 0 (.d8 0x2d)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x1044c0 (.sib 4 (some 0) 0 (.d8 0x2d)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1044c5 [0x80, 0x74, 0x04, 0x2E, 0x6A] (StorePre 0x1044c5 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2e)) s (0x1044c5 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1044c5 5 (.sib 4 (some 0) 0 (.d8 0x2e)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1044c5 5 (.sib 4 (some 0) 0 (.d8 0x2e)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x1044c5 (.sib 4 (some 0) 0 (.d8 0x2e)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1044ca [0x80, 0x74, 0x04, 0x2F, 0x6A] (StorePre 0x1044ca 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2f)) s (0x1044ca + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1044ca 5 (.sib 4 (some 0) 0 (.d8 0x2f)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1044ca 5 (.sib 4 (some 0) 0 (.d8 0x2f)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x1044ca (.sib 4 (some 0) 0 (.d8 0x2f)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1044cf [0x80, 0x74, 0x04, 0x30, 0x6A] (StorePre 0x1044cf 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x30)) s (0x1044cf + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1044cf 5 (.sib 4 (some 0) 0 (.d8 0x30)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1044cf 5 (.sib 4 (some 0) 0 (.d8 0x30)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x1044cf (.sib 4 (some 0) 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1044d4 [0x48, 0x83, 0xC0, 0x04] (fun s => s.RIP = 0x1044d4) (addR64Imm8Effect 0x1044d4 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1044d4 0 0x4).toInstrSpec (add_r64_imm8_effect_step 0x1044d4 0x48 0xc0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1044d8 [0x48, 0x83, 0xF8, 0x43] (fun s => s.RIP = 0x1044d8) (cmpR64Imm8Effect 0x1044d8 0 0x43)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1044d8 0 0x43).toInstrSpec (cmp_r64_imm8_effect_step 0x1044d8 0x48 0xf8 0x43 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044c5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044d4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044d8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044dc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1044dc 5 0xe2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1044c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1044c0 :=
  Rest.liftedBlock (rest_l1044c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1044c0 x hx)

theorem rest_l1044de_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x1044de bytes_l1044de) [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x10455e bytes_l1044de_1 b_l1044de_1 := by
  have f20 : InstrSpec 0x10455e [0x48, 0x8D, 0xBC, 0x24, 0x48, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10455e) (leaR64Effect 0x10455e 7 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10455e 7 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (lea_r64_effect_step 0x10455e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x104566 [0x48, 0x8D, 0xB4, 0x24, 0xF0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104566) (leaR64Effect 0x104566 6 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104566 6 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (lea_r64_effect_step 0x104566 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10456e [0xBA, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10456e) (movR32Imm32Effect 0x10456e 5 2 0xa8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10456e 5 2 0xa8).toInstrSpec (mov_r32_imm32_effect_step 0x10456e 0xba (by decide) 0xa8) pre_rip
  have f23 : InstrSpec 0x104573 [0xFF, 0x15, 0x57, 0xF8, 0x0F, 0x00] (GoesTo (CallMemPre 0x104573 (.rip 0xff857)) (callEffect (callMemPtr 0x104573 (.rip 0xff857)) (0x104573 + BitVec.ofNat 64 (callMemLen (.rip 0xff857)))) 0x12a820) (callEffect (callMemPtr 0x104573 (.rip 0xff857)) (0x104573 + BitVec.ofNat 64 (callMemLen (.rip 0xff857))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x104573 (.rip 0xff857)).toInstrSpec (call_m64_effect_step 0x104573 (.rip 0xff857) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104566) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10456e) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 78), (1, 80), (2, 88), (3, 3), (4, 4), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104573) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 78), (1, 80), (2, 88), (3, 3), (4, 90), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f23 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 92) (by decide) (by decide) rfl rfl

theorem rest_l1044de [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1044de bytes_l1044de) (entryMap (live .l1044de))
      24 0x1044de bytes_l1044de b_l1044de := by
  have f0 : InstrSpec 0x1044de [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x1044de) (leaR64Effect 0x1044de 7 (.sib 4 none 0 (.d32 0x230)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1044de 7 (.sib 4 none 0 (.d32 0x230))).toInstrSpec (lea_r64_effect_step 0x1044de 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x230)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1044e6 [0x48, 0x8D, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1044e6) (leaR64Effect 0x1044e6 6 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1044e6 6 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (lea_r64_effect_step 0x1044e6 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1044ee [0xB9, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1044ee) (movR32Imm32Effect 0x1044ee 5 1 0xd)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1044ee 5 1 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x1044ee 0xb9 (by decide) 0xd) pre_rip
  have f3 : InstrSpec 0x1044f3 [0xF3, 0x48, 0xA5] (RepPre 0x1044f3 (RepMovsqPre 0x1044f3)) (repMovsqEffect 0x1044f3)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1044f3).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1044f3 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x1044f6 [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x1044f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1044f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1044f6 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1044f6 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1044f6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1044fb [0x48, 0x89, 0x84, 0x24, 0x28, 0x02, 0x00, 0x00] (StorePre 0x1044fb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x1044fb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1044fb 0 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1044fb 0 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (mov_m64_r64_effect_step 0x1044fb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x104503 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x104503 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x104503 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104503 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104503 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x104503 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x104508 [0x48, 0x89, 0x84, 0x24, 0x20, 0x02, 0x00, 0x00] (StorePre 0x104508 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x104508 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104508 0 (.sib 4 none 0 (.d32 0x220)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104508 0 (.sib 4 none 0 (.d32 0x220))).toInstrSpec (mov_m64_r64_effect_step 0x104508 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x220)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104510 [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x104510 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x104510 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104510 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104510 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x104510 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x104515 [0x48, 0x89, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00] (StorePre 0x104515 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x104515 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104515 0 (.sib 4 none 0 (.d32 0x218)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104515 0 (.sib 4 none 0 (.d32 0x218))).toInstrSpec (mov_m64_r64_effect_step 0x104515 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x218)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10451d [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x10451d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10451d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10451d 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10451d 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10451d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x104522 [0x48, 0x89, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00] (StorePre 0x104522 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x104522 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104522 0 (.sib 4 none 0 (.d32 0x210)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104522 0 (.sib 4 none 0 (.d32 0x210))).toInstrSpec (mov_m64_r64_effect_step 0x104522 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x210)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10452a [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x10452a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10452a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10452a 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10452a 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10452a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10452f [0x48, 0x89, 0x84, 0x24, 0x08, 0x02, 0x00, 0x00] (StorePre 0x10452f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x208)) s (0x10452f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10452f 0 (.sib 4 none 0 (.d32 0x208)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10452f 0 (.sib 4 none 0 (.d32 0x208))).toInstrSpec (mov_m64_r64_effect_step 0x10452f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x208)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x104537 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x104537 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x104537 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104537 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104537 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x104537 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10453c [0x48, 0x89, 0x84, 0x24, 0x00, 0x02, 0x00, 0x00] (StorePre 0x10453c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x200)) s (0x10453c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10453c 0 (.sib 4 none 0 (.d32 0x200)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10453c 0 (.sib 4 none 0 (.d32 0x200))).toInstrSpec (mov_m64_r64_effect_step 0x10453c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x200)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x104544 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x104544 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x104544 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104544 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104544 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x104544 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x104549 [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x104549 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x104549 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104549 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104549 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x104549 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10454e [0x48, 0x89, 0x8C, 0x24, 0xF8, 0x01, 0x00, 0x00] (StorePre 0x10454e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f8)) s (0x10454e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10454e 1 (.sib 4 none 0 (.d32 0x1f8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10454e 1 (.sib 4 none 0 (.d32 0x1f8))).toInstrSpec (mov_m64_r64_effect_step 0x10454e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1f8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x104556 [0x48, 0x89, 0x84, 0x24, 0xF0, 0x01, 0x00, 0x00] (StorePre 0x104556 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x104556 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104556 0 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104556 0 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (mov_m64_r64_effect_step 0x104556 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044e6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044ee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044f3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044f6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044fb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104503) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104508) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104510) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104515) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10451d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104522) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10452a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10452f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104537) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10453c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104544) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104549) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10454e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104556) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10455e) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1044de_1 code

theorem block_l1044de [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1044de :=
  Rest.liftedBlock (rest_l1044de hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1044de x hx)

theorem rest_l104579 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104579 bytes_l104579) (entryMap (live .l104579))
      4 0x104579 bytes_l104579 b_l104579 := by
  have f0 : InstrSpec 0x104579 [0x48, 0x8D, 0xAC, 0x24, 0xC8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104579) (leaR64Effect 0x104579 5 (.sib 4 none 0 (.d32 0x1c8)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x104579 5 (.sib 4 none 0 (.d32 0x1c8))).toInstrSpec (lea_r64_effect_step 0x104579 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x1c8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104581 [0x0F, 0xB6, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00] (LoadPre 0x104581 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x104581 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x104581 8 3 (.sib 4 none 0 (.d32 0x1c7)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x104581 8 3 (.sib 4 none 0 (.d32 0x1c7))).toInstrSpec (movzx_r32_m8_effect_step 0x104581 3 (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104589 [0x48, 0x83, 0xFB, 0x1F] (fun s => s.RIP = 0x104589) (cmpR64Imm8Effect 0x104589 3 0x1f)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x104589 3 0x1f).toInstrSpec (cmp_r64_imm8_effect_step 0x104589 0x48 0xfb 0x1f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104581) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 55), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104589) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(3, 55), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10458d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x10458d 7 0x18a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104579 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104579 :=
  Rest.liftedBlock (rest_l104579 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104579 x hx)

theorem rest_l104593 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104593 bytes_l104593) (entryMap (live .l104593))
      15 0x104593 bytes_l104593 b_l104593 := by
  have f0 : InstrSpec 0x104593 [0x48, 0x8B, 0x4C, 0x24, 0x70] (LoadPre 0x104593 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104593 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104593 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104593 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x104593 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104598 [0x48, 0x8B, 0x41, 0x18] (LoadPre 0x104598 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x104598 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104598 0 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104598 0 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104598 0x48 (by decide) 0 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10459c [0x49, 0x89, 0x44, 0x1D, 0x18] (StorePre 0x10459c 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x18)) s (0x10459c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10459c 0 (.sib 13 (some 3) 0 (.d8 0x18)))
      [.gpr 0, .gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10459c 0 (.sib 13 (some 3) 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10459c 0x49 (by decide) 0 (.sib 13 (some 3) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1045a1 [0x48, 0x8B, 0x41, 0x10] (LoadPre 0x1045a1 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x1045a1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1045a1 0 (.base 1 (.d8 0x10)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1045a1 0 (.base 1 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1045a1 0x48 (by decide) 0 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1045a5 [0x49, 0x89, 0x44, 0x1D, 0x10] (StorePre 0x1045a5 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x10)) s (0x1045a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1045a5 0 (.sib 13 (some 3) 0 (.d8 0x10)))
      [.gpr 0, .gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1045a5 0 (.sib 13 (some 3) 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1045a5 0x49 (by decide) 0 (.sib 13 (some 3) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1045aa [0x48, 0x8B, 0x01] (LoadPre 0x1045aa (fun s => AddrMode.addr (.base 1 .none) s (0x1045aa + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1045aa 0 (.base 1 .none))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1045aa 0 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1045aa 0x48 (by decide) 0 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1045ad [0x48, 0x8B, 0x49, 0x08] (LoadPre 0x1045ad (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x1045ad + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1045ad 1 (.base 1 (.d8 0x8)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1045ad 1 (.base 1 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1045ad 0x48 (by decide) 1 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1045b1 [0x49, 0x89, 0x4C, 0x1D, 0x08] (StorePre 0x1045b1 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x8)) s (0x1045b1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1045b1 1 (.sib 13 (some 3) 0 (.d8 0x8)))
      [.gpr 1, .gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1045b1 1 (.sib 13 (some 3) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1045b1 0x49 (by decide) 1 (.sib 13 (some 3) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1045b6 [0x49, 0x89, 0x44, 0x1D, 0x00] (StorePre 0x1045b6 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x0)) s (0x1045b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1045b6 0 (.sib 13 (some 3) 0 (.d8 0x0)))
      [.gpr 0, .gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1045b6 0 (.sib 13 (some 3) 0 (.d8 0x0))).toInstrSpec (mov_m64_r64_effect_step 0x1045b6 0x49 (by decide) 0 (.sib 13 (some 3) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1045bb [0x80, 0xCB, 0x20] (fun s => s.RIP = 0x1045bb) (orR8Imm8Effect 0x1045bb 3 3 0x20)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (orR8Imm8Effect_footprint 0x1045bb 3 3 0x20).toInstrSpec (or_r8_imm8_effect_step 0x1045bb 0xcb 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1045be [0x88, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00] (StorePre 0x1045be 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x1045be + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1045be 7 3 (.sib 4 none 0 (.d32 0x1c7)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1045be 7 3 (.sib 4 none 0 (.d32 0x1c7))).toInstrSpec (mov_m8_r8_effect_step 0x1045be 3 (by decide) (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1045c5 [0x4C, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x1045c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1045c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1045c5 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1045c5 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1045c5 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1045ca [0x0F, 0xB6, 0xC3] (fun s => s.RIP = 0x1045ca) (movzxR32R8Effect 0x1045ca 3 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x1045ca 3 0 3).toInstrSpec (movzx_r32_r8_effect_step 0x1045ca 0xc3 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1045cd [0x3C, 0x3F] (fun s => s.RIP = 0x1045cd) (cmpAlImm8Effect 0x1045cd 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1045cd 0x3f).toInstrSpec (cmp_al_imm8_effect_step 0x1045cd 0x3f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104598) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10459c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045a5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045aa) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045ad) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045b1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045b6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045bb) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 63), (3, 67), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045be) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 61), (1, 63), (3, 67), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045c5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 63), (3, 67), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045ca) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 63), (3, 67), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045cd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 63), (3, 67), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 70), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045cf) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x1045cf 4 0x1be) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104593 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104593 :=
  Rest.liftedBlock (rest_l104593 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104593 x hx)

theorem rest_l1045d5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1045d5 bytes_l1045d5) (entryMap (live .l1045d5))
      3 0x1045d5 bytes_l1045d5 b_l1045d5 := by
  have f0 : InstrSpec 0x1045d5 [0xC6, 0x84, 0x04, 0x88, 0x01, 0x00, 0x00, 0x01] (StorePre 0x1045d5 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x188)) s (0x1045d5 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x1045d5 (.sib 4 (some 0) 0 (.d32 0x188)) 0x1)
      [.gpr 4, .gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1045d5 (.sib 4 (some 0) 0 (.d32 0x188)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1045d5 (.sib 4 (some 0) 0 (.d32 0x188)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1045dd [0xFF, 0xC0] (fun s => s.RIP = 0x1045dd) (incR32Effect 0x1045dd 2 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR32Effect_footprint 0x1045dd 2 0).toInstrSpec (inc_r32_effect_step 0x1045dd 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 56) (jmp_rel32_effect_step 0x1045df 0x1e0 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1045d5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1045d5 :=
  Rest.liftedBlock (rest_l1045d5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1045d5 x hx)

theorem rest_l1045e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1045e4 bytes_l1045e4) (entryMap (live .l1045e4))
      8 0x1045e4 bytes_l1045e4 b_l1045e4 := by
  have f0 : InstrSpec 0x1045e4 [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1045e4) (movR32Imm32Effect 0x1045e4 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1045e4 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x1045e4 0xba (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x1045e9 [0x48, 0x29, 0xDA] (fun s => s.RIP = 0x1045e9) (subR64R64Effect 0x1045e9 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1045e9 2 3).toInstrSpec (sub_r64_r64_effect_step 0x1045e9 0x48 0xda (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1045ec [0x4C, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x1045ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1045ec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1045ec 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1045ec 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1045ec 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1045f1 [0x4C, 0x8D, 0x3C, 0x16] (fun s => s.RIP = 0x1045f1) (leaR64Effect 0x1045f1 15 (.sib 6 (some 2) 0 .none))
      [.gpr 6, .gpr 2] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1045f1 15 (.sib 6 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1045f1 0x4c (by decide) 7 (.sib 6 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1045f5 [0x4A, 0x8D, 0x3C, 0x2B] (fun s => s.RIP = 0x1045f5) (leaR64Effect 0x1045f5 7 (.sib 3 (some 13) 0 .none))
      [.gpr 3, .gpr 13] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1045f5 7 (.sib 3 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1045f5 0x4a (by decide) 7 (.sib 3 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1045f9 [0x48, 0x83, 0xC3, 0xE0] (fun s => s.RIP = 0x1045f9) (addR64Imm8Effect 0x1045f9 3 0xe0)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1045f9 3 0xe0).toInstrSpec (add_r64_imm8_effect_step 0x1045f9 0x48 0xc3 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1045fd [0x4C, 0x8D, 0x25, 0x1C, 0x62, 0x02, 0x00] (fun s => s.RIP = 0x1045fd) (leaR64Effect 0x1045fd 12 (.rip 0x2621c))
      [] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x1045fd 12 (.rip 0x2621c)).toInstrSpec (lea_r64_effect_step 0x1045fd 0x4c (by decide) 4 (.rip 0x2621c) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104604 [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x104604 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104607) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104607)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x104604 12 0x104607).toInstrSpec (call_r64_rex_effect_step 0x104604 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045e9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045f1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045f5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 60), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045f9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 55), (3, 62), (4, 4), (5, 5), (6, 6), (7, 60), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045fd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 55), (3, 62), (4, 4), (5, 5), (6, 6), (7, 60), (9, 9), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104604) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 55), (3, 62), (4, 66), (5, 5), (6, 6), (7, 60), (9, 9), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f7 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l1045e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1045e4 :=
  Rest.liftedBlock (rest_l1045e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1045e4 x hx)

theorem rest_l104607 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104607 bytes_l104607) (entryMap (live .l104607))
      5 0x104607 bytes_l104607 b_l104607 := by
  have f0 : InstrSpec 0x104607 [0x48, 0xFF, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x104607 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104607 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104607 8 64 (.sib 4 none 0 (.d32 0x140)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x104607 8 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (inc_m64_effect_step 0x104607 0x48 (by decide) (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10460f [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10460f) (movR32Imm32Effect 0x10460f 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10460f 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10460f 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x104614 [0x48, 0x8D, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104614) (leaR64Effect 0x104614 7 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104614 7 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (lea_r64_effect_step 0x104614 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10461c [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10461c) (movR64R64Effect 0x10461c 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10461c 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10461c 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10461f [0xE8, 0xBC, 0xD2, 0x01, 0x00] (PushPre 0x10461f 5) (callEffect (fun _ => 0x1218e0) 0x104624)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10461f 0x1218e0 0x104624).toInstrSpec (call_rel32_effect_step 0x10461f 0x1d2bc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10460f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104614) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10461c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10461f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l104607 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104607 :=
  Rest.liftedBlock (rest_l104607 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104607 x hx)

theorem rest_l104624 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104624 bytes_l104624) (entryMap (live .l104624))
      9 0x104624 bytes_l104624 b_l104624 := by
  have f0 : InstrSpec 0x104624 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x104624) (movR64R64Effect 0x104624 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104624 6 3).toInstrSpec (mov_r64_r64_effect_step 0x104624 0x48 0xde (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104627 [0x48, 0xB8, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x104627) (movR64Imm64Effect 0x104627 0 0x7fffffffffffffc0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104627 0 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x104627 0x48 0xb8 (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f2 : InstrSpec 0x104631 [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x104631) (andR64R64Effect 0x104631 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x104631 6 0).toInstrSpec (and_r64_r64_effect_step 0x104631 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104634 [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x104634) (addR64R64Effect 0x104634 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x104634 6 15).toInstrSpec (add_r64_r64_effect_step 0x104634 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104637 [0x4C, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x104637 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104637 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104637 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x104637 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104637 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10463c [0x88, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00] (StorePre 0x10463c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x10463c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10463c 7 3 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10463c 7 3 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (mov_m8_r8_effect_step 0x10463c 3 (by decide) (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x104643 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x104643) (movR64R64Effect 0x104643 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104643 7 13).toInstrSpec (mov_r64_r64_effect_step 0x104643 0x4c 0xef (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104646 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x104646) (movR64R64Effect 0x104646 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104646 2 3).toInstrSpec (mov_r64_r64_effect_step 0x104646 0x48 0xda (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104649 [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x104649 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10464c) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10464c)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x104649 12 0x10464c).toInstrSpec (call_r64_rex_effect_step 0x104649 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104627) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104631) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104634) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104637) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10463c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104643) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104646) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (2, 66), (3, 3), (4, 4), (5, 5), (6, 59), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104649) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (2, 66), (3, 3), (4, 68), (5, 5), (6, 59), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l104624 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104624 :=
  Rest.liftedBlock (rest_l104624 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104624 x hx)

theorem rest_l10464c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10464c bytes_l10464c) (entryMap (live .l10464c))
      4 0x10464c bytes_l10464c b_l10464c := by
  have f0 : InstrSpec 0x10464c [0x0F, 0xB6, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00] (LoadPre 0x10464c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x10464c + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10464c 8 3 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x10464c 8 3 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (movzx_r32_m8_effect_step 0x10464c 3 (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104654 [0x0F, 0xB6, 0xC3] (fun s => s.RIP = 0x104654) (movzxR32R8Effect 0x104654 3 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x104654 3 0 3).toInstrSpec (movzx_r32_r8_effect_step 0x104654 0xc3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104657 [0x3C, 0x3F] (fun s => s.RIP = 0x104657) (cmpAlImm8Effect 0x104657 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x104657 0x3f).toInstrSpec (cmp_al_imm8_effect_step 0x104657 0x3f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104654) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104657) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104659) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x104659 5 0xfffffb69) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10464c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10464c :=
  Rest.liftedBlock (rest_l10464c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10464c x hx)

theorem rest_l10465f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10465f bytes_l10465f) (entryMap (live .l10465f))
      6 0x10465f bytes_l10465f b_l10465f := by
  have f0 : InstrSpec 0x10465f [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10465f) (movR32Imm32Effect 0x10465f 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10465f 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x10465f 0xba (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x104664 [0x48, 0x29, 0xC2] (fun s => s.RIP = 0x104664) (subR64R64Effect 0x104664 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104664 2 0).toInstrSpec (sub_r64_r64_effect_step 0x104664 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104667 [0x4A, 0x8D, 0x3C, 0x28] (fun s => s.RIP = 0x104667) (leaR64Effect 0x104667 7 (.sib 0 (some 13) 0 .none))
      [.gpr 0, .gpr 13] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104667 7 (.sib 0 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x104667 0x4a (by decide) 7 (.sib 0 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10466b [0x31, 0xDB] (fun s => s.RIP = 0x10466b) (xorR32R32Effect 0x10466b 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10466b 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x10466b 0xdb (by decide)) pre_rip
  have f4 : InstrSpec 0x10466d [0x31, 0xF6] (fun s => s.RIP = 0x10466d) (xorR32R32Effect 0x10466d 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10466d 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10466d 0xf6 (by decide)) pre_rip
  have f5 : InstrSpec 0x10466f [0xFF, 0x15, 0x9B, 0xF7, 0x0F, 0x00] (GoesTo (CallMemPre 0x10466f (.rip 0xff79b)) (callEffect (callMemPtr 0x10466f (.rip 0xff79b)) (0x10466f + BitVec.ofNat 64 (callMemLen (.rip 0xff79b)))) 0x12a700) (callEffect (callMemPtr 0x10466f (.rip 0xff79b)) (0x10466f + BitVec.ofNat 64 (callMemLen (.rip 0xff79b))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10466f (.rip 0xff79b)).toInstrSpec (call_m64_effect_step 0x10466f (.rip 0xff79b) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104664) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104667) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10466b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 55), (3, 59), (4, 4), (5, 5), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10466d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 55), (3, 59), (4, 4), (5, 5), (6, 61), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10466f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 55), (3, 59), (4, 63), (5, 5), (6, 61), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l10465f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10465f :=
  Rest.liftedBlock (rest_l10465f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10465f x hx)

theorem rest_l104675 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104675 bytes_l104675) (entryMap (live .l104675))
      5 0x104675 bytes_l104675 b_l104675 := by
  have f0 : InstrSpec 0x104675 [0x48, 0xFF, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x104675 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104675 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104675 8 64 (.sib 4 none 0 (.d32 0x140)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x104675 8 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (inc_m64_effect_step 0x104675 0x48 (by decide) (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10467d [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10467d) (movR32Imm32Effect 0x10467d 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10467d 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10467d 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x104682 [0x48, 0x8D, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104682) (leaR64Effect 0x104682 7 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104682 7 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (lea_r64_effect_step 0x104682 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10468a [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10468a) (movR64R64Effect 0x10468a 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10468a 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10468a 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10468d [0xE8, 0x4E, 0xD2, 0x01, 0x00] (PushPre 0x10468d 5) (callEffect (fun _ => 0x1218e0) 0x104692)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10468d 0x1218e0 0x104692).toInstrSpec (call_rel32_effect_step 0x10468d 0x1d24e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10467d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104682) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10468a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10468d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l104675 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104675 :=
  Rest.liftedBlock (rest_l104675 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104675 x hx)

theorem rest_l104692 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104692 bytes_l104692) (entryMap (live .l104692))
      3 0x104692 bytes_l104692 b_l104692 := by
  have f0 : InstrSpec 0x104692 [0x88, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00] (StorePre 0x104692 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104692 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x104692 7 3 (.sib 4 none 0 (.d32 0x11f)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x104692 7 3 (.sib 4 none 0 (.d32 0x11f))).toInstrSpec (mov_m8_r8_effect_step 0x104692 3 (by decide) (.sib 4 none 0 (.d32 0x11f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104699 [0x4D, 0x85, 0xFF] (fun s => s.RIP = 0x104699) (testR64R64Effect 0x104699 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x104699 15 15).toInstrSpec (test_r64_r64_effect_step 0x104699 0x4d 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104699) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10469c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x10469c 5 0xfffffb41) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104692 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104692 :=
  Rest.liftedBlock (rest_l104692 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104692 x hx)

theorem rest_l1046a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1046a2 bytes_l1046a2) (entryMap (live .l1046a2))
      5 0x1046a2 bytes_l1046a2 b_l1046a2 := by
  have f0 : InstrSpec 0x1046a2 [0x48, 0x8D, 0x9C, 0x24, 0xF0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1046a2) (leaR64Effect 0x1046a2 3 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1046a2 3 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (lea_r64_effect_step 0x1046a2 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1046aa [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1046aa) (leaR64Effect 0x1046aa 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1046aa 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x1046aa 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1046b2 [0xBA, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1046b2) (movR32Imm32Effect 0x1046b2 5 2 0xa8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1046b2 5 2 0xa8).toInstrSpec (mov_r32_imm32_effect_step 0x1046b2 0xba (by decide) 0xa8) pre_rip
  have f3 : InstrSpec 0x1046b7 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1046b7) (movR64R64Effect 0x1046b7 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1046b7 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1046b7 0x48 0xdf (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1046ba [0xFF, 0x15, 0x10, 0xF7, 0x0F, 0x00] (GoesTo (CallMemPre 0x1046ba (.rip 0xff710)) (callEffect (callMemPtr 0x1046ba (.rip 0xff710)) (0x1046ba + BitVec.ofNat 64 (callMemLen (.rip 0xff710)))) 0x12a820) (callEffect (callMemPtr 0x1046ba (.rip 0xff710)) (0x1046ba + BitVec.ofNat 64 (callMemLen (.rip 0xff710))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1046ba (.rip 0xff710)).toInstrSpec (call_m64_effect_step 0x1046ba (.rip 0xff710) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046aa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 53), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046b7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 53), (4, 4), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046ba) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 53), (4, 61), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1046a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1046a2 :=
  Rest.liftedBlock (rest_l1046a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1046a2 x hx)

theorem rest_l1046c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1046c0 bytes_l1046c0) (entryMap (live .l1046c0))
      7 0x1046c0 bytes_l1046c0 b_l1046c0 := by
  have f0 : InstrSpec 0x1046c0 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1046c0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1046c0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1046c0 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1046c0 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1046c0 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1046c9 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1046c9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1046c9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1046c9 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1046c9 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1046c9 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1046d2 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1046d2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1046d2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1046d2 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1046d2 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1046d2 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1046db [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1046db 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1046db + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1046db (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1046db (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1046db 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1046e4 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x1046e4) (leaR64Effect 0x1046e4 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1046e4 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1046e4 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1046e9 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1046e9) (movR64R64Effect 0x1046e9 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1046e9 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1046e9 0x48 0xdf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1046ec [0xE8, 0x5F, 0x33, 0x00, 0x00] (PushPre 0x1046ec 5) (callEffect (fun _ => 0x107a50) 0x1046f1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1046ec 0x107a50 0x1046f1).toInstrSpec (call_rel32_effect_step 0x1046ec 0x335f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046d2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046db) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046e4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046ec) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a50) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1046c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1046c0 :=
  Rest.liftedBlock (rest_l1046c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1046c0 x hx)

theorem rest_l1046f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1046f1 bytes_l1046f1) (entryMap (live .l1046f1))
      10 0x1046f1 bytes_l1046f1 b_l1046f1 := by
  have f0 : InstrSpec 0x1046f1 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1046f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1046f1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1046f1 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1046f1 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1046f1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1046f6 [0x48, 0x89, 0x45, 0x18] (StorePre 0x1046f6 4 (fun s => AddrMode.addr (.base 5 (.d8 0x18)) s (0x1046f6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1046f6 0 (.base 5 (.d8 0x18)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1046f6 0 (.base 5 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1046f6 0x48 (by decide) 0 (.base 5 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1046fa [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1046fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1046fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1046fa 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1046fa 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1046fa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1046ff [0x48, 0x89, 0x45, 0x10] (StorePre 0x1046ff 4 (fun s => AddrMode.addr (.base 5 (.d8 0x10)) s (0x1046ff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1046ff 0 (.base 5 (.d8 0x10)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1046ff 0 (.base 5 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1046ff 0x48 (by decide) 0 (.base 5 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104703 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x104703 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104703 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104703 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104703 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104703 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x104708 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x104708 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104708 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104708 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104708 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104708 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10470d [0x48, 0x89, 0x4D, 0x08] (StorePre 0x10470d 4 (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x10470d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10470d 1 (.base 5 (.d8 0x8)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x10470d 1 (.base 5 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10470d 0x48 (by decide) 1 (.base 5 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x104711 [0x48, 0x89, 0x45, 0x00] (StorePre 0x104711 4 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x104711 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104711 0 (.base 5 (.d8 0x0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x104711 0 (.base 5 (.d8 0x0))).toInstrSpec (mov_m64_r64_effect_step 0x104711 0x48 (by decide) 0 (.base 5 (.d8 0x0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104715 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x104715) (movR64R64Effect 0x104715 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104715 7 5).toInstrSpec (mov_r64_r64_effect_step 0x104715 0x48 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046f6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046ff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104703) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104708) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10470d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104711) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104715) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104718) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 67) (jmp_rel32_effect_step 0x104718 0x22f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1046f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1046f1 :=
  Rest.liftedBlock (rest_l1046f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1046f1 x hx)

theorem rest_l10471d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10471d bytes_l10471d) (entryMap (live .l10471d))
      8 0x10471d bytes_l10471d b_l10471d := by
  have f0 : InstrSpec 0x10471d [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10471d) (movR32Imm32Effect 0x10471d 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10471d 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x10471d 0xba (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x104722 [0x48, 0x29, 0xDA] (fun s => s.RIP = 0x104722) (subR64R64Effect 0x104722 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104722 2 3).toInstrSpec (sub_r64_r64_effect_step 0x104722 0x48 0xda (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104725 [0x48, 0x8B, 0x74, 0x24, 0x70] (LoadPre 0x104725 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104725 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104725 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x104725 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x104725 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10472a [0x4C, 0x8D, 0x3C, 0x16] (fun s => s.RIP = 0x10472a) (leaR64Effect 0x10472a 15 (.sib 6 (some 2) 0 .none))
      [.gpr 6, .gpr 2] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10472a 15 (.sib 6 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10472a 0x4c (by decide) 7 (.sib 6 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10472e [0x4A, 0x8D, 0x3C, 0x2B] (fun s => s.RIP = 0x10472e) (leaR64Effect 0x10472e 7 (.sib 3 (some 13) 0 .none))
      [.gpr 3, .gpr 13] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10472e 7 (.sib 3 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10472e 0x4a (by decide) 7 (.sib 3 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104732 [0x48, 0x83, 0xC3, 0xE0] (fun s => s.RIP = 0x104732) (addR64Imm8Effect 0x104732 3 0xe0)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104732 3 0xe0).toInstrSpec (add_r64_imm8_effect_step 0x104732 0x48 0xc3 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104736 [0x4C, 0x8D, 0x25, 0xE3, 0x60, 0x02, 0x00] (fun s => s.RIP = 0x104736) (leaR64Effect 0x104736 12 (.rip 0x260e3))
      [] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x104736 12 (.rip 0x260e3)).toInstrSpec (lea_r64_effect_step 0x104736 0x4c (by decide) 4 (.rip 0x260e3) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10473d [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x10473d 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104740) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104740)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10473d 12 0x104740).toInstrSpec (call_r64_rex_effect_step 0x10473d 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104722) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104725) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10472a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10472e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 61), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104732) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 55), (3, 63), (4, 4), (5, 5), (6, 57), (7, 61), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104736) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 55), (3, 63), (4, 4), (5, 5), (6, 57), (7, 61), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10473d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 55), (3, 63), (4, 67), (5, 5), (6, 57), (7, 61), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f7 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l10471d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10471d :=
  Rest.liftedBlock (rest_l10471d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10471d x hx)

theorem rest_l104740 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104740 bytes_l104740) (entryMap (live .l104740))
      5 0x104740 bytes_l104740 b_l104740 := by
  have f0 : InstrSpec 0x104740 [0x48, 0xFF, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x104740 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x104740 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104740 8 64 (.sib 4 none 0 (.d32 0x1e8)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x104740 8 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (inc_m64_effect_step 0x104740 0x48 (by decide) (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104748 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104748) (movR32Imm32Effect 0x104748 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104748 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x104748 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x10474d [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x10474d) (movR64R64Effect 0x10474d 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10474d 7 5).toInstrSpec (mov_r64_r64_effect_step 0x10474d 0x48 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104750 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x104750) (movR64R64Effect 0x104750 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104750 6 13).toInstrSpec (mov_r64_r64_effect_step 0x104750 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104753 [0xE8, 0x88, 0xD1, 0x01, 0x00] (PushPre 0x104753 5) (callEffect (fun _ => 0x1218e0) 0x104758)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104753 0x1218e0 0x104758).toInstrSpec (call_rel32_effect_step 0x104753 0x1d188 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104748) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10474d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104750) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104753) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l104740 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104740 :=
  Rest.liftedBlock (rest_l104740 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104740 x hx)

theorem rest_l104758 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104758 bytes_l104758) (entryMap (live .l104758))
      8 0x104758 bytes_l104758 b_l104758 := by
  have f0 : InstrSpec 0x104758 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x104758) (movR64R64Effect 0x104758 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104758 6 3).toInstrSpec (mov_r64_r64_effect_step 0x104758 0x48 0xde (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10475b [0x48, 0xB8, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x10475b) (movR64Imm64Effect 0x10475b 0 0x7fffffffffffffc0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10475b 0 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x10475b 0x48 0xb8 (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f2 : InstrSpec 0x104765 [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x104765) (andR64R64Effect 0x104765 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x104765 6 0).toInstrSpec (and_r64_r64_effect_step 0x104765 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104768 [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x104768) (addR64R64Effect 0x104768 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x104768 6 15).toInstrSpec (add_r64_r64_effect_step 0x104768 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10476b [0x88, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00] (StorePre 0x10476b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x10476b + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10476b 7 3 (.sib 4 none 0 (.d32 0x1c7)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10476b 7 3 (.sib 4 none 0 (.d32 0x1c7))).toInstrSpec (mov_m8_r8_effect_step 0x10476b 3 (by decide) (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x104772 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x104772) (movR64R64Effect 0x104772 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104772 7 13).toInstrSpec (mov_r64_r64_effect_step 0x104772 0x4c 0xef (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104775 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x104775) (movR64R64Effect 0x104775 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104775 2 3).toInstrSpec (mov_r64_r64_effect_step 0x104775 0x48 0xda (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104778 [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x104778 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10477b) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10477b)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x104778 12 0x10477b).toInstrSpec (call_r64_rex_effect_step 0x104778 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10475b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104765) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104768) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10476b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104772) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104775) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (2, 64), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104778) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (2, 64), (3, 3), (4, 66), (5, 5), (6, 59), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f7 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l104758 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104758 :=
  Rest.liftedBlock (rest_l104758 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104758 x hx)

theorem rest_l10477b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10477b bytes_l10477b) (entryMap (live .l10477b))
      5 0x10477b bytes_l10477b b_l10477b := by
  have f0 : InstrSpec 0x10477b [0x0F, 0xB6, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00] (LoadPre 0x10477b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x10477b + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10477b 8 3 (.sib 4 none 0 (.d32 0x1c7)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x10477b 8 3 (.sib 4 none 0 (.d32 0x1c7))).toInstrSpec (movzx_r32_m8_effect_step 0x10477b 3 (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104783 [0x4C, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x104783 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104783 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104783 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x104783 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104783 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104788 [0x0F, 0xB6, 0xC3] (fun s => s.RIP = 0x104788) (movzxR32R8Effect 0x104788 3 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x104788 3 0 3).toInstrSpec (movzx_r32_r8_effect_step 0x104788 0xc3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10478b [0x3C, 0x3F] (fun s => s.RIP = 0x10478b) (cmpAlImm8Effect 0x10478b 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x10478b 0x3f).toInstrSpec (cmp_al_imm8_effect_step 0x10478b 0x3f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104783) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104788) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10478b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10478d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x10478d 5 0xfffffe42) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10477b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10477b :=
  Rest.liftedBlock (rest_l10477b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10477b x hx)

theorem rest_l104793 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104793 bytes_l104793) (entryMap (live .l104793))
      5 0x104793 bytes_l104793 b_l104793 := by
  have f0 : InstrSpec 0x104793 [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104793) (movR32Imm32Effect 0x104793 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104793 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x104793 0xba (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x104798 [0x48, 0x29, 0xC2] (fun s => s.RIP = 0x104798) (subR64R64Effect 0x104798 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104798 2 0).toInstrSpec (sub_r64_r64_effect_step 0x104798 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10479b [0x4A, 0x8D, 0x3C, 0x28] (fun s => s.RIP = 0x10479b) (leaR64Effect 0x10479b 7 (.sib 0 (some 13) 0 .none))
      [.gpr 0, .gpr 13] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10479b 7 (.sib 0 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10479b 0x4a (by decide) 7 (.sib 0 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10479f [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10479f) (movR32Imm32Effect 0x10479f 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10479f 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10479f 0xbe (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x1047a4 [0xFF, 0x15, 0x66, 0xF6, 0x0F, 0x00] (GoesTo (CallMemPre 0x1047a4 (.rip 0xff666)) (callEffect (callMemPtr 0x1047a4 (.rip 0xff666)) (0x1047a4 + BitVec.ofNat 64 (callMemLen (.rip 0xff666)))) 0x12a700) (callEffect (callMemPtr 0x1047a4 (.rip 0xff666)) (0x1047a4 + BitVec.ofNat 64 (callMemLen (.rip 0xff666))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1047a4 (.rip 0xff666)).toInstrSpec (call_m64_effect_step 0x1047a4 (.rip 0xff666) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104798) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10479b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10479f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047a4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l104793 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104793 :=
  Rest.liftedBlock (rest_l104793 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104793 x hx)

theorem rest_l1047aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1047aa bytes_l1047aa) (entryMap (live .l1047aa))
      5 0x1047aa bytes_l1047aa b_l1047aa := by
  have f0 : InstrSpec 0x1047aa [0x48, 0xFF, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x1047aa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x1047aa + BitVec.ofNat 64 8)) 8) (incMEffect 0x1047aa 8 64 (.sib 4 none 0 (.d32 0x1e8)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x1047aa 8 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (inc_m64_effect_step 0x1047aa 0x48 (by decide) (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1047b2 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1047b2) (movR32Imm32Effect 0x1047b2 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1047b2 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1047b2 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x1047b7 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x1047b7) (movR64R64Effect 0x1047b7 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1047b7 7 5).toInstrSpec (mov_r64_r64_effect_step 0x1047b7 0x48 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1047ba [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x1047ba) (movR64R64Effect 0x1047ba 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1047ba 6 13).toInstrSpec (mov_r64_r64_effect_step 0x1047ba 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1047bd [0xE8, 0x1E, 0xD1, 0x01, 0x00] (PushPre 0x1047bd 5) (callEffect (fun _ => 0x1218e0) 0x1047c2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1047bd 0x1218e0 0x1047c2).toInstrSpec (call_rel32_effect_step 0x1047bd 0x1d11e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047b2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047b7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047bd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l1047aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1047aa :=
  Rest.liftedBlock (rest_l1047aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1047aa x hx)

theorem rest_l1047c2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1047c2 bytes_l1047c2) (entryMap (live .l1047c2))
      1 0x1047c2 bytes_l1047c2 b_l1047c2 := by
  have f0 : InstrSpec 0x1047c2 [0x31, 0xC0] (fun s => s.RIP = 0x1047c2) (xorR32R32Effect 0x1047c2 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047c2 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1047c2 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1047c2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1047c2 :=
  Rest.liftedBlock (rest_l1047c2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1047c2 x hx)

theorem rest_l1047c4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1047c4 bytes_l1047c4) (entryMap (live .l1047c4))
      2 0x1047c4 bytes_l1047c4 b_l1047c4 := by
  have f0 : InstrSpec 0x1047c4 [0x88, 0x84, 0x24, 0xC7, 0x01, 0x00, 0x00] (StorePre 0x1047c4 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x1047c4 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1047c4 7 0 (.sib 4 none 0 (.d32 0x1c7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1047c4 7 0 (.sib 4 none 0 (.d32 0x1c7))).toInstrSpec (mov_m8_r8_effect_step 0x1047c4 0 (by decide) (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047cb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel8_effect_step 0x1047cb 0x2e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1047c4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1047c4 :=
  Rest.liftedBlock (rest_l1047c4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1047c4 x hx)

theorem rest_l1047d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1047d0 bytes_l1047d0) (entryMap (live .l1047d0))
      4 0x1047d0 bytes_l1047d0 b_l1047d0 := by
  have f0 : InstrSpec 0x1047d0 [0x41, 0x89, 0xFF] (fun s => s.RIP = 0x1047d0) (movR32R32Effect 0x1047d0 3 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x1047d0 3 15 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x1047d0 0x41 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1047d3 [0x4C, 0x01, 0xEF] (fun s => s.RIP = 0x1047d3) (addR64R64Effect 0x1047d3 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1047d3 7 13).toInstrSpec (add_r64_r64_effect_step 0x1047d3 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1047d6 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x1047d6) (movR64R64Effect 0x1047d6 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1047d6 2 3).toInstrSpec (mov_r64_r64_effect_step 0x1047d6 0x48 0xda (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1047d9 [0xFF, 0x15, 0xF1, 0xF5, 0x0F, 0x00] (GoesTo (CallMemPre 0x1047d9 (.rip 0xff5f1)) (callEffect (callMemPtr 0x1047d9 (.rip 0xff5f1)) (0x1047d9 + BitVec.ofNat 64 (callMemLen (.rip 0xff5f1)))) 0x12a820) (callEffect (callMemPtr 0x1047d9 (.rip 0xff5f1)) (0x1047d9 + BitVec.ofNat 64 (callMemLen (.rip 0xff5f1))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1047d9 (.rip 0xff5f1)).toInstrSpec (call_m64_effect_step 0x1047d9 (.rip 0xff5f1) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047d6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047d9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1047d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1047d0 :=
  Rest.liftedBlock (rest_l1047d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1047d0 x hx)

theorem rest_l1047df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1047df bytes_l1047df) (entryMap (live .l1047df))
      6 0x1047df bytes_l1047df b_l1047df := by
  have f0 : InstrSpec 0x1047df [0x44, 0x00, 0xFB] (fun s => s.RIP = 0x1047df) (addR8R8Effect 0x1047df 3 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (addR8R8Effect_footprint 0x1047df 3 3 15).toInstrSpec (add_r8_r8_rex_effect_step 0x1047df 0x44 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1047e2 [0x4C, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x1047e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1047e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1047e2 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1047e2 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1047e2 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1047e7 [0x88, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00] (StorePre 0x1047e7 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x1047e7 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1047e7 7 3 (.sib 4 none 0 (.d32 0x1c7)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1047e7 7 3 (.sib 4 none 0 (.d32 0x1c7))).toInstrSpec (mov_m8_r8_effect_step 0x1047e7 3 (by decide) (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1047ee [0x49, 0x83, 0xC6, 0x10] (fun s => s.RIP = 0x1047ee) (addR64Imm8Effect 0x1047ee 14 0x10)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1047ee 14 0x10).toInstrSpec (add_r64_imm8_effect_step 0x1047ee 0x49 0xc6 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1047f2 [0x4D, 0x39, 0xFE] (fun s => s.RIP = 0x1047f2) (cmpR64R64Effect 0x1047f2 14 15)
      [.gpr 14, .gpr 15] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1047f2 14 15).toInstrSpec (cmp_r64_r64_effect_step 0x1047f2 0x4d 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047e2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047e7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047f2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 55), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047f5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel32_effect_step 0x1047f5 4 0xbf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1047df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1047df :=
  Rest.liftedBlock (rest_l1047df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1047df x hx)

theorem rest_l1047fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1047fb bytes_l1047fb) (entryMap (live .l1047fb))
      8 0x1047fb bytes_l1047fb b_l1047fb := by
  have f0 : InstrSpec 0x1047fb [0x49, 0x8B, 0x36] (LoadPre 0x1047fb (fun s => AddrMode.addr (.base 14 .none) s (0x1047fb + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1047fb 6 (.base 14 .none))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1047fb 6 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1047fb 0x49 (by decide) 6 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1047fe [0x49, 0x8B, 0x5E, 0x08] (LoadPre 0x1047fe (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1047fe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1047fe 3 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1047fe 3 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1047fe 0x49 (by decide) 3 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104802 [0x0F, 0xB6, 0xBC, 0x24, 0xC7, 0x01, 0x00, 0x00] (LoadPre 0x104802 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x104802 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x104802 8 7 (.sib 4 none 0 (.d32 0x1c7)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x104802 8 7 (.sib 4 none 0 (.d32 0x1c7))).toInstrSpec (movzx_r32_m8_effect_step 0x104802 7 (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10480a [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10480a) (movR32Imm32Effect 0x10480a 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10480a 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x10480a 0xba (by decide) 0x40) pre_rip
  have f4 : InstrSpec 0x10480f [0x48, 0x29, 0xFA] (fun s => s.RIP = 0x10480f) (subR64R64Effect 0x10480f 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10480f 2 7).toInstrSpec (sub_r64_r64_effect_step 0x10480f 0x48 0xfa (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104812 [0x49, 0x89, 0xDC] (fun s => s.RIP = 0x104812) (movR64R64Effect 0x104812 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x104812 12 3).toInstrSpec (mov_r64_r64_effect_step 0x104812 0x49 0xdc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104815 [0x49, 0x29, 0xD4] (fun s => s.RIP = 0x104815) (subR64R64Effect 0x104815 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104815 12 2).toInstrSpec (sub_r64_r64_effect_step 0x104815 0x49 0xd4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 55), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104802) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 55), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10480a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 55), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10480f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 55), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104812) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 55), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104815) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 55), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104818) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x104818 2 0xb6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1047fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1047fb :=
  Rest.liftedBlock (rest_l1047fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1047fb x hx)

theorem rest_l10481a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10481a bytes_l10481a) (entryMap (live .l10481a))
      2 0x10481a bytes_l10481a b_l10481a := by
  have f0 : InstrSpec 0x10481a [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x10481a) (testR64R64Effect 0x10481a 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10481a 7 7).toInstrSpec (test_r64_r64_effect_step 0x10481a 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10481d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10481d 4 0x89) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10481a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10481a :=
  Rest.liftedBlock (rest_l10481a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10481a x hx)

theorem rest_l104823 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104823 bytes_l104823) (entryMap (live .l104823))
      3 0x104823 bytes_l104823 b_l104823 := by
  have f0 : InstrSpec 0x104823 [0x48, 0x8D, 0x1C, 0x16] (fun s => s.RIP = 0x104823) (leaR64Effect 0x104823 3 (.sib 6 (some 2) 0 .none))
      [.gpr 6, .gpr 2] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x104823 3 (.sib 6 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x104823 0x48 (by decide) 3 (.sib 6 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104827 [0x4C, 0x01, 0xEF] (fun s => s.RIP = 0x104827) (addR64R64Effect 0x104827 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x104827 7 13).toInstrSpec (add_r64_r64_effect_step 0x104827 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10482a [0xFF, 0x15, 0xA0, 0xF5, 0x0F, 0x00] (GoesTo (CallMemPre 0x10482a (.rip 0xff5a0)) (callEffect (callMemPtr 0x10482a (.rip 0xff5a0)) (0x10482a + BitVec.ofNat 64 (callMemLen (.rip 0xff5a0)))) 0x12a820) (callEffect (callMemPtr 0x10482a (.rip 0xff5a0)) (0x10482a + BitVec.ofNat 64 (callMemLen (.rip 0xff5a0))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10482a (.rip 0xff5a0)).toInstrSpec (call_m64_effect_step 0x10482a (.rip 0xff5a0) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104827) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10482a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 53), (4, 57), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f2 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l104823 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104823 :=
  Rest.liftedBlock (rest_l104823 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104823 x hx)

theorem rest_l104830 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104830 bytes_l104830) (entryMap (live .l104830))
      5 0x104830 bytes_l104830 b_l104830 := by
  have f0 : InstrSpec 0x104830 [0x48, 0xFF, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x104830 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x104830 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104830 8 64 (.sib 4 none 0 (.d32 0x1e8)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x104830 8 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (inc_m64_effect_step 0x104830 0x48 (by decide) (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104838 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104838) (movR32Imm32Effect 0x104838 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104838 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x104838 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x10483d [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x10483d) (movR64R64Effect 0x10483d 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10483d 7 5).toInstrSpec (mov_r64_r64_effect_step 0x10483d 0x48 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104840 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x104840) (movR64R64Effect 0x104840 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104840 6 13).toInstrSpec (mov_r64_r64_effect_step 0x104840 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104843 [0xE8, 0x98, 0xD0, 0x01, 0x00] (PushPre 0x104843 5) (callEffect (fun _ => 0x1218e0) 0x104848)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104843 0x1218e0 0x104848).toInstrSpec (call_rel32_effect_step 0x104843 0x1d098 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104838) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10483d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104840) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104843) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l104830 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104830 :=
  Rest.liftedBlock (rest_l104830 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104830 x hx)

theorem rest_l104848 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104848 bytes_l104848) (entryMap (live .l104848))
      5 0x104848 bytes_l104848 b_l104848 := by
  have f0 : InstrSpec 0x104848 [0xC6, 0x84, 0x24, 0xC7, 0x01, 0x00, 0x00, 0x00] (StorePre 0x104848 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x104848 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104848 (.sib 4 none 0 (.d32 0x1c7)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x104848 (.sib 4 none 0 (.d32 0x1c7)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x104848 (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104850 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x104850) (movR64R64Effect 0x104850 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104850 6 3).toInstrSpec (mov_r64_r64_effect_step 0x104850 0x48 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104853 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x104853) (movR64R64Effect 0x104853 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104853 2 12).toInstrSpec (mov_r64_r64_effect_step 0x104853 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104856 [0x48, 0xC1, 0xEA, 0x06] (fun s => s.RIP = 0x104856) (shrR64Effect 0x104856 4 2 6)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x104856 4 2 6).toInstrSpec (shr_r64_imm8_effect_step 0x104856 0x48 0xea 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104850) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104853) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104856) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 59) f3 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x104856 4 2 6 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10485a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x10485a 4 0x16) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104848 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104848 :=
  Rest.liftedBlock (rest_l104848 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104848 x hx)

theorem rest_l10485c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10485c bytes_l10485c) (entryMap (live .l10485c))
      4 0x10485c bytes_l10485c b_l10485c := by
  have f0 : InstrSpec 0x10485c [0x48, 0x01, 0x94, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x10485c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x10485c + BitVec.ofNat 64 8)) 8) (addMREffect 0x10485c 8 64 2 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 2, .gpr 4] [] [.flags, .rip] :=
    (addMREffect64_footprint 0x10485c 8 2 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (add_m64_r64_effect_step 0x10485c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104864 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x104864) (movR64R64Effect 0x104864 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104864 7 5).toInstrSpec (mov_r64_r64_effect_step 0x104864 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104867 [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x104867) (movR64R64Effect 0x104867 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x104867 3 6).toInstrSpec (mov_r64_r64_effect_step 0x104867 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10486a [0xE8, 0x71, 0xD0, 0x01, 0x00] (PushPre 0x10486a 5) (callEffect (fun _ => 0x1218e0) 0x10486f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10486a 0x1218e0 0x10486f).toInstrSpec (call_rel32_effect_step 0x10486a 0x1d071 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104864) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104867) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10486a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 58), (5, 5), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 60) (by decide) (by decide) rfl rfl

theorem block_l10485c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10485c :=
  Rest.liftedBlock (rest_l10485c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10485c x hx)

theorem rest_l10486f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10486f bytes_l10486f) (entryMap (live .l10486f))
      1 0x10486f bytes_l10486f b_l10486f := by
  have f0 : InstrSpec 0x10486f [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x10486f) (movR64R64Effect 0x10486f 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10486f 6 3).toInstrSpec (mov_r64_r64_effect_step 0x10486f 0x48 0xde (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104872) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l10486f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10486f :=
  Rest.liftedBlock (rest_l10486f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10486f x hx)

theorem rest_l104872 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104872 bytes_l104872) (entryMap (live .l104872))
      9 0x104872 bytes_l104872 b_l104872 := by
  have f0 : InstrSpec 0x104872 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x104872) (movR64R64Effect 0x104872 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x104872 0 12).toInstrSpec (mov_r64_r64_effect_step 0x104872 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104875 [0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x104875) (movR64Imm64Effect 0x104875 1 0x7fffffffffffffc0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x104875 1 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x104875 0x48 0xb9 (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f2 : InstrSpec 0x10487f [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10487f) (andR64R64Effect 0x10487f 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10487f 0 1).toInstrSpec (and_r64_r64_effect_step 0x10487f 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104882 [0x41, 0x83, 0xE4, 0x3F] (fun s => s.RIP = 0x104882) (andR32Imm8Effect 0x104882 4 12 0x3f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x104882 4 12 0x3f).toInstrSpec (and_r32_imm8_rex_effect_step 0x104882 0x41 0xe4 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104886 [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x104886) (addR64R64Effect 0x104886 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x104886 6 0).toInstrSpec (add_r64_r64_effect_step 0x104886 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104889 [0x44, 0x88, 0xA4, 0x24, 0xC7, 0x01, 0x00, 0x00] (StorePre 0x104889 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x104889 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x104889 8 12 (.sib 4 none 0 (.d32 0x1c7)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x104889 8 12 (.sib 4 none 0 (.d32 0x1c7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x104889 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x1c7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x104891 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x104891) (movR64R64Effect 0x104891 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104891 7 13).toInstrSpec (mov_r64_r64_effect_step 0x104891 0x4c 0xef (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104894 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x104894) (movR64R64Effect 0x104894 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104894 2 12).toInstrSpec (mov_r64_r64_effect_step 0x104894 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104897 [0xFF, 0x15, 0x33, 0xF5, 0x0F, 0x00] (GoesTo (CallMemPre 0x104897 (.rip 0xff533)) (callEffect (callMemPtr 0x104897 (.rip 0xff533)) (0x104897 + BitVec.ofNat 64 (callMemLen (.rip 0xff533)))) 0x12a820) (callEffect (callMemPtr 0x104897 (.rip 0xff533)) (0x104897 + BitVec.ofNat 64 (callMemLen (.rip 0xff533))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x104897 (.rip 0xff533)).toInstrSpec (call_m64_effect_step 0x104897 (.rip 0xff533) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104875) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10487f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104882) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104886) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 61), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104889) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 61), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104891) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 61), (7, 64), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104894) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 55), (2, 66), (3, 3), (4, 4), (5, 5), (6, 61), (7, 64), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104897) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 55), (2, 66), (3, 3), (4, 68), (5, 5), (6, 61), (7, 64), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l104872 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104872 :=
  Rest.liftedBlock (rest_l104872 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104872 x hx)

theorem rest_l10489d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10489d bytes_l10489d) (entryMap (live .l10489d))
      3 0x10489d bytes_l10489d b_l10489d := by
  have f0 : InstrSpec 0x10489d [0x49, 0x83, 0xC6, 0x10] (fun s => s.RIP = 0x10489d) (addR64Imm8Effect 0x10489d 14 0x10)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10489d 14 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10489d 0x49 0xc6 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1048a1 [0x4D, 0x39, 0xFE] (fun s => s.RIP = 0x1048a1) (cmpR64R64Effect 0x1048a1 14 15)
      [.gpr 14, .gpr 15] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1048a1 14 15).toInstrSpec (cmp_r64_r64_effect_step 0x1048a1 0x4d 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1048a4 5 0xffffff51) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10489d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10489d :=
  Rest.liftedBlock (rest_l10489d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10489d x hx)

theorem rest_l1048aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1048aa bytes_l1048aa) (entryMap (live .l1048aa))
      1 0x1048aa bytes_l1048aa b_l1048aa := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1048aa 0xe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1048aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1048aa :=
  Rest.liftedBlock (rest_l1048aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1048aa x hx)

theorem rest_l1048ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1048ac bytes_l1048ac) (entryMap (live .l1048ac))
      4 0x1048ac bytes_l1048ac b_l1048ac := by
  have f0 : InstrSpec 0x1048ac [0x49, 0x89, 0xDC] (fun s => s.RIP = 0x1048ac) (movR64R64Effect 0x1048ac 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1048ac 12 3).toInstrSpec (mov_r64_r64_effect_step 0x1048ac 0x49 0xdc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1048af [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x1048af) (movR64R64Effect 0x1048af 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1048af 2 12).toInstrSpec (mov_r64_r64_effect_step 0x1048af 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1048b2 [0x48, 0xC1, 0xEA, 0x06] (fun s => s.RIP = 0x1048b2) (shrR64Effect 0x1048b2 4 2 6)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x1048b2 4 2 6).toInstrSpec (shr_r64_imm8_effect_step 0x1048b2 0x48 0xea 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048af) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 58) f2 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x1048b2 4 2 6 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048b6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x1048b6 5 0xa4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1048ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1048ac :=
  Rest.liftedBlock (rest_l1048ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1048ac x hx)

theorem rest_l1048b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1048b8 bytes_l1048b8) (entryMap (live .l1048b8))
      1 0x1048b8 bytes_l1048b8 b_l1048b8 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1048b8 0xb8 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1048b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1048b8 :=
  Rest.liftedBlock (rest_l1048b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1048b8 x hx)

theorem rest_l1048ba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1048ba bytes_l1048ba) (entryMap (live .l1048ba))
      5 0x1048ba bytes_l1048ba b_l1048ba := by
  have f0 : InstrSpec 0x1048ba [0x48, 0x8D, 0x9C, 0x24, 0xF0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1048ba) (leaR64Effect 0x1048ba 3 (.sib 4 none 0 (.d32 0x1f0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1048ba 3 (.sib 4 none 0 (.d32 0x1f0))).toInstrSpec (lea_r64_effect_step 0x1048ba 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x1f0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1048c2 [0x48, 0x8D, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1048c2) (leaR64Effect 0x1048c2 6 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1048c2 6 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (lea_r64_effect_step 0x1048c2 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1048ca [0xBA, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1048ca) (movR32Imm32Effect 0x1048ca 5 2 0xa8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1048ca 5 2 0xa8).toInstrSpec (mov_r32_imm32_effect_step 0x1048ca 0xba (by decide) 0xa8) pre_rip
  have f3 : InstrSpec 0x1048cf [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1048cf) (movR64R64Effect 0x1048cf 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1048cf 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1048cf 0x48 0xdf (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1048d2 [0xFF, 0x15, 0xF8, 0xF4, 0x0F, 0x00] (GoesTo (CallMemPre 0x1048d2 (.rip 0xff4f8)) (callEffect (callMemPtr 0x1048d2 (.rip 0xff4f8)) (0x1048d2 + BitVec.ofNat 64 (callMemLen (.rip 0xff4f8)))) 0x12a820) (callEffect (callMemPtr 0x1048d2 (.rip 0xff4f8)) (0x1048d2 + BitVec.ofNat 64 (callMemLen (.rip 0xff4f8))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1048d2 (.rip 0xff4f8)).toInstrSpec (call_m64_effect_step 0x1048d2 (.rip 0xff4f8) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 53), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 53), (4, 4), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048d2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 53), (4, 61), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1048ba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1048ba :=
  Rest.liftedBlock (rest_l1048ba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1048ba x hx)

theorem rest_l1048d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1048d8 bytes_l1048d8) (entryMap (live .l1048d8))
      7 0x1048d8 bytes_l1048d8 b_l1048d8 := by
  have f0 : InstrSpec 0x1048d8 [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1048d8 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1048d8 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1048d8 (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1048d8 (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1048d8 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1048e4 [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1048e4 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1048e4 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1048e4 (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1048e4 (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1048e4 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1048f0 [0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1048f0 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1048f0 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1048f0 (.sib 4 none 0 (.d32 0x90)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1048f0 (.sib 4 none 0 (.d32 0x90)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1048f0 0x48 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1048fc [0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1048fc 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1048fc + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1048fc (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1048fc (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1048fc 0x48 (by decide) (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104908 [0x48, 0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104908) (leaR64Effect 0x104908 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104908 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x104908 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104910 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x104910) (movR64R64Effect 0x104910 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104910 7 3).toInstrSpec (mov_r64_r64_effect_step 0x104910 0x48 0xdf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104913 [0xE8, 0x38, 0x31, 0x00, 0x00] (PushPre 0x104913 5) (callEffect (fun _ => 0x107a50) 0x104918)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104913 0x107a50 0x104918).toInstrSpec (call_rel32_effect_step 0x104913 0x3138 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048e4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048f0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048fc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104908) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104910) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104913) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a50) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l1048d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1048d8 :=
  Rest.liftedBlock (rest_l1048d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1048d8 x hx)

theorem rest_l104918 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104918 bytes_l104918) (entryMap (live .l104918))
      9 0x104918 bytes_l104918 b_l104918 := by
  have f0 : InstrSpec 0x104918 [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x104918 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x104918 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104918 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104918 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x104918 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104920 [0x48, 0x8B, 0x7C, 0x24, 0x78] (LoadPre 0x104920 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x104920 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104920 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x104920 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x104920 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104925 [0x48, 0x89, 0x47, 0x18] (StorePre 0x104925 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x104925 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104925 0 (.base 7 (.d8 0x18)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x104925 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x104925 0x48 (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104929 [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x104929 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x104929 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104929 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104929 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x104929 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x104931 [0x48, 0x89, 0x47, 0x10] (StorePre 0x104931 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x104931 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104931 0 (.base 7 (.d8 0x10)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x104931 0 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x104931 0x48 (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x104935 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x104935 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x104935 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104935 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104935 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x104935 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10493d [0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10493d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10493d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10493d 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10493d 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x10493d 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x104945 [0x48, 0x89, 0x4F, 0x08] (StorePre 0x104945 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x104945 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104945 1 (.base 7 (.d8 0x8)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x104945 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x104945 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104949 [0x48, 0x89, 0x07] (StorePre 0x104949 3 (fun s => AddrMode.addr (.base 7 .none) s (0x104949 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x104949 0 (.base 7 .none))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x104949 0 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x104949 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104920) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104925) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104929) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104931) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104935) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10493d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104945) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104949) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10494c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 67) (by decide) rfl

theorem block_l104918 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104918 :=
  Rest.liftedBlock (rest_l104918 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104918 x hx)

theorem rest_l10494c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10494c bytes_l10494c) (entryMap (live .l10494c))
      1 0x10494c bytes_l10494c b_l10494c := by
  have f0 : InstrSpec 0x10494c [0xE8, 0x1F, 0x00, 0x00, 0x00] (PushPre 0x10494c 5) (callEffect (fun _ => 0x104970) 0x104951)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10494c 0x104970 0x104951).toInstrSpec (call_rel32_effect_step 0x10494c 0x1f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104970) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 55) (by decide) (by decide) rfl rfl

theorem block_l10494c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10494c :=
  Rest.liftedBlock (rest_l10494c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10494c x hx)

theorem rest_l104951 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104951 bytes_l104951) (entryMap (live .l104951))
      8 0x104951 bytes_l104951 b_l104951 := by
  have f0 : InstrSpec 0x104951 [0x48, 0x81, 0xC4, 0x98, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x104951) (addR64Imm32Effect 0x104951 4 0x298)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x104951 4 0x298).toInstrSpec (add_r64_imm32_effect_step 0x104951 0x48 0xc4 0x298 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104958 [0x5B] (PopPre 0x104958) (popR64Effect 0x104958 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104958 1 3).toInstrSpec (pop_r64_effect_step 0x104958 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x104959 [0x41, 0x5C] (PopPre 0x104959) (popR64Effect 0x104959 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104959 2 12).toInstrSpec (pop_r64_rex_effect_step 0x104959 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10495b [0x41, 0x5D] (PopPre 0x10495b) (popR64Effect 0x10495b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10495b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10495b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10495d [0x41, 0x5E] (PopPre 0x10495d) (popR64Effect 0x10495d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10495d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10495d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10495f [0x41, 0x5F] (PopPre 0x10495f) (popR64Effect 0x10495f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10495f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10495f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x104961 [0x5D] (PopPre 0x104961) (popR64Effect 0x104961 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104961 1 5).toInstrSpec (pop_r64_effect_step 0x104961 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x104962 [0xC3] (RetPre 0x104962) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x104962).toInstrSpec (ret_effect_step 0x104962) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104958) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104959) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10495b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10495d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10495f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104961) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104962) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l104951 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104951 :=
  Rest.liftedBlock (rest_l104951 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104951 x hx)

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

theorem_by block_l103f30_eval :
    program.runBlock (dialect code) ⟨.l103f30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103fe0_eval :
    program.runBlock (dialect code) ⟨.l103fe0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10400a_eval :
    program.runBlock (dialect code) ⟨.l10400a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104080_eval :
    program.runBlock (dialect code) ⟨.l104080, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104090_eval :
    program.runBlock (dialect code) ⟨.l104090, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1040ba_eval :
    program.runBlock (dialect code) ⟨.l1040ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10416d_eval :
    program.runBlock (dialect code) ⟨.l10416d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104190_eval :
    program.runBlock (dialect code) ⟨.l104190, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1041c8_eval :
    program.runBlock (dialect code) ⟨.l1041c8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1041e3_eval :
    program.runBlock (dialect code) ⟨.l1041e3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104200_eval :
    program.runBlock (dialect code) ⟨.l104200, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104211_eval :
    program.runBlock (dialect code) ⟨.l104211, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10422b_eval :
    program.runBlock (dialect code) ⟨.l10422b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10424a_eval :
    program.runBlock (dialect code) ⟨.l10424a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104253_eval :
    program.runBlock (dialect code) ⟨.l104253, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104263_eval :
    program.runBlock (dialect code) ⟨.l104263, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104280_eval :
    program.runBlock (dialect code) ⟨.l104280, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10429e_eval :
    program.runBlock (dialect code) ⟨.l10429e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1042b6_eval :
    program.runBlock (dialect code) ⟨.l1042b6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1042c0_eval :
    program.runBlock (dialect code) ⟨.l1042c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1042e3_eval :
    program.runBlock (dialect code) ⟨.l1042e3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1042f2_eval :
    program.runBlock (dialect code) ⟨.l1042f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1042f4_eval :
    program.runBlock (dialect code) ⟨.l1042f4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10430a_eval :
    program.runBlock (dialect code) ⟨.l10430a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10430c_eval :
    program.runBlock (dialect code) ⟨.l10430c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10432a_eval :
    program.runBlock (dialect code) ⟨.l10432a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10435b_eval :
    program.runBlock (dialect code) ⟨.l10435b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10438b_eval :
    program.runBlock (dialect code) ⟨.l10438b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104410_eval :
    program.runBlock (dialect code) ⟨.l104410, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10442e_eval :
    program.runBlock (dialect code) ⟨.l10442e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1044a4_eval :
    program.runBlock (dialect code) ⟨.l1044a4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1044c0_eval :
    program.runBlock (dialect code) ⟨.l1044c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1044de_eval :
    program.runBlock (dialect code) ⟨.l1044de, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104579_eval :
    program.runBlock (dialect code) ⟨.l104579, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104593_eval :
    program.runBlock (dialect code) ⟨.l104593, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1045d5_eval :
    program.runBlock (dialect code) ⟨.l1045d5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1045e4_eval :
    program.runBlock (dialect code) ⟨.l1045e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104607_eval :
    program.runBlock (dialect code) ⟨.l104607, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104624_eval :
    program.runBlock (dialect code) ⟨.l104624, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10464c_eval :
    program.runBlock (dialect code) ⟨.l10464c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10465f_eval :
    program.runBlock (dialect code) ⟨.l10465f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104675_eval :
    program.runBlock (dialect code) ⟨.l104675, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104692_eval :
    program.runBlock (dialect code) ⟨.l104692, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1046a2_eval :
    program.runBlock (dialect code) ⟨.l1046a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1046c0_eval :
    program.runBlock (dialect code) ⟨.l1046c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1046f1_eval :
    program.runBlock (dialect code) ⟨.l1046f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10471d_eval :
    program.runBlock (dialect code) ⟨.l10471d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104740_eval :
    program.runBlock (dialect code) ⟨.l104740, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104758_eval :
    program.runBlock (dialect code) ⟨.l104758, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10477b_eval :
    program.runBlock (dialect code) ⟨.l10477b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104793_eval :
    program.runBlock (dialect code) ⟨.l104793, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1047aa_eval :
    program.runBlock (dialect code) ⟨.l1047aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1047c2_eval :
    program.runBlock (dialect code) ⟨.l1047c2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1047c4_eval :
    program.runBlock (dialect code) ⟨.l1047c4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1047d0_eval :
    program.runBlock (dialect code) ⟨.l1047d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1047df_eval :
    program.runBlock (dialect code) ⟨.l1047df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1047fb_eval :
    program.runBlock (dialect code) ⟨.l1047fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10481a_eval :
    program.runBlock (dialect code) ⟨.l10481a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104823_eval :
    program.runBlock (dialect code) ⟨.l104823, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104830_eval :
    program.runBlock (dialect code) ⟨.l104830, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104848_eval :
    program.runBlock (dialect code) ⟨.l104848, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10485c_eval :
    program.runBlock (dialect code) ⟨.l10485c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10486f_eval :
    program.runBlock (dialect code) ⟨.l10486f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104872_eval :
    program.runBlock (dialect code) ⟨.l104872, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10489d_eval :
    program.runBlock (dialect code) ⟨.l10489d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1048aa_eval :
    program.runBlock (dialect code) ⟨.l1048aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1048ac_eval :
    program.runBlock (dialect code) ⟨.l1048ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1048b8_eval :
    program.runBlock (dialect code) ⟨.l1048b8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1048ba_eval :
    program.runBlock (dialect code) ⟨.l1048ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1048d8_eval :
    program.runBlock (dialect code) ⟨.l1048d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104918_eval :
    program.runBlock (dialect code) ⟨.l104918, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10494c_eval :
    program.runBlock (dialect code) ⟨.l10494c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104951_eval :
    program.runBlock (dialect code) ⟨.l104951, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
