import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Inverse.Wrapper.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Inverse.Wrapper.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118910 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112e30 bytes_l118910) (entryMap (live .l118910))
      8 0x112e30 bytes_l118910 b_l118910 := by
  have f0 : InstrSpec 0x112e30 [0x53] (PushPre 0x112e30 1) (pushR64Effect 0x112e30 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x112e30 1 3).toInstrSpec (push_r64_effect_step 0x112e30 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x112e31 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x112e31) (subR64Imm8Effect 0x112e31 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x112e31 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x112e31 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112e35 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x112e35) (movR64R64Effect 0x112e35 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x112e35 3 7).toInstrSpec (mov_r64_r64_effect_step 0x112e35 0x48 0xfb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112e38 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x112e38) (leaR64Effect 0x112e38 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x112e38 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x112e38 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112e3d [0x48, 0xB9, 0xB1, 0x43, 0xFF, 0x11, 0x55, 0x37, 0x2E, 0x33] (fun s => s.RIP = 0x112e3d) (movR64Imm64Effect 0x112e3d 1 0x332e375511ff43b1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x112e3d 1 0x332e375511ff43b1).toInstrSpec (mov_r64_imm64_effect_step 0x112e3d 0x48 0xb9 (by decide) (by decide) 0x332e375511ff43b1) pre_rip
  have f5 : InstrSpec 0x112e47 [0x48, 0xc7, 0xc2, 0xe0, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x112e47) (movR64Imm32Effect 0x112e47 2 0x2025e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x112e47 2 0x2025e0).toInstrSpec (mov_r64_imm32_effect_step 0x112e47 0x48 0xc2 (by decide) (by decide) (by decide) 0x2025e0) pre_rip
  have f6 : InstrSpec 0x112e4e [0x49, 0xc7, 0xc0, 0xc0, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x112e4e) (movR64Imm32Effect 0x112e4e 8 0x2025c0)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x112e4e 8 0x2025c0).toInstrSpec (mov_r64_imm32_effect_step 0x112e4e 0x49 0xc0 (by decide) (by decide) (by decide) 0x2025c0) pre_rip
  have f7 : InstrSpec 0x112e55 [0xE8, 0x16, 0xED, 0xFF, 0xFF] (PushPre 0x112e55 5) (callEffect (fun _ => 0x111b70) 0x112e5a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x112e55 0x111b70 0x112e5a).toInstrSpec (call_rel32_effect_step 0x112e55 0xffffed16 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e35) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e38) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e3d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e47) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 63), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e4e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 63), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e55) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 63), (3, 57), (4, 67), (5, 5), (6, 6), (7, 59), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b70) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l118910 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118910 :=
  Rest.liftedBlock (rest_l118910 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118910 x hx)

theorem rest_l11893a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112e5a bytes_l11893a) (entryMap (live .l11893a))
      10 0x112e5a bytes_l11893a b_l11893a := by
  have f0 : InstrSpec 0x112e5a [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x112e5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112e5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112e5a 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112e5a 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x112e5a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x112e5f [0x48, 0x89, 0x43, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e5f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x112e5f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e5f 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x112e5f 0 (.base 3 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112e5f 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f2 : InstrSpec 0x112e63 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x112e63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112e63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112e63 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112e63 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x112e63 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x112e68 [0x48, 0x89, 0x43, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e68 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x112e68 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e68 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x112e68 0 (.base 3 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112e68 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f4 : InstrSpec 0x112e6c [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x112e6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112e6c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112e6c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112e6c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x112e6c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x112e71 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x112e71 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112e71 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112e71 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x112e71 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x112e71 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x112e76 [0x48, 0x89, 0x4B, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e76 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x112e76 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e76 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x112e76 1 (.base 3 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112e76 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x112e7a [0x48, 0x89, 0x03] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e7a 3 (fun s => AddrMode.addr (.base 3 .none) s (0x112e7a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x112e7a 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x112e7a 0 (.base 3 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112e7a 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f8 : InstrSpec 0x112e7d [0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x112e7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112e7d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x112e7d 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x112e7d 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x112e7d 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x112e81 [0xe8, 0xea, 0x61, 0x00, 0x00] (PushPre 0x112e81 5) (callEffect (fun _ => 0x119070) 0x112e86)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x112e81 0x119070 0x112e86).toInstrSpec (call_rel32_effect_step 0x112e81 0x61ea (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e5f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e63) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e68) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e6c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e71) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e76) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e7a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e7d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e81) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 67), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x119070) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l11893a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11893a :=
  Rest.liftedBlock (rest_l11893a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11893a x hx)

theorem rest_l118966 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112e86 bytes_l118966) (entryMap (live .l118966))
      5 0x112e86 bytes_l118966 b_l118966 := by
  have f0 : InstrSpec 0x112e86 [0x88, 0x43, 0x20] (StorePre 0x112e86 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x112e86 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x112e86 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x112e86 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x112e86 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112e89 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x112e89) (movR64R64Effect 0x112e89 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112e89 0 3).toInstrSpec (mov_r64_r64_effect_step 0x112e89 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112e8c [0x48, 0x83, 0xC4, 0x30] (fun s => s.RIP = 0x112e8c) (addR64Imm8Effect 0x112e8c 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x112e8c 4 0x30).toInstrSpec (add_r64_imm8_effect_step 0x112e8c 0x48 0xc4 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112e90 [0x5B] (PopPre 0x112e90) (popR64Effect 0x112e90 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112e90 1 3).toInstrSpec (pop_r64_effect_step 0x112e90 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x112e91 [0xC3] (RetPre 0x112e91) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x112e91).toInstrSpec (ret_effect_step 0x112e91) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e89) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e8c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 56), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e90) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (2, 2), (3, 58), (4, 59), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e91) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 54), (2, 2), (3, 58), (4, 62), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l118966 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118966 :=
  Rest.liftedBlock (rest_l118966 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118966 x hx)

theorem rest_l117650 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111b70 bytes_l117650) (entryMap (live .l117650))
      0 0x111b70 bytes_l117650 b_l117650 := by
  exact Rest.cut

theorem block_l117650 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117650 :=
  Rest.liftedBlock (rest_l117650 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117650 x hx)

theorem rest_l126f60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x119070 bytes_l126f60) (entryMap (live .l126f60))
      5 0x119070 bytes_l126f60 b_l126f60 := by
  have f0 : InstrSpec 0x119070 [0x48, 0x83, 0xEC, 0x01] (fun s => s.RIP = 0x119070) (subR64Imm8Effect 0x119070 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x119070 4 0x1).toInstrSpec (sub_r64_imm8_effect_step 0x119070 0x48 0xec 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x119074 [0x40, 0x88, 0x3C, 0x24] (StorePre 0x119074 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119074 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x119074 4 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x119074 4 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x119074 0x40 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x119078 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x119078 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119078 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x119078 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x119078 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x119078 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11907c [0x48, 0x83, 0xC4, 0x01] (fun s => s.RIP = 0x11907c) (addR64Imm8Effect 0x11907c 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11907c 4 0x1).toInstrSpec (add_r64_imm8_effect_step 0x11907c 0x48 0xc4 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x119080 [0xC3] (RetPre 0x119080) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x119080).toInstrSpec (ret_effect_step 0x119080) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x119074) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x119078) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 53), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11907c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 58), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x119080) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 62) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 61), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l126f60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f60 :=
  Rest.liftedBlock (rest_l126f60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f60 x hx)

end P256.Proofs.Scalar.Inverse.Wrapper.Machine
