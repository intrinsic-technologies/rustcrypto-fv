import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l115020 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112fd0 bytes_l115020) (entryMap (live .l115020))
      8 0x112fd0 bytes_l115020 b_l115020 := by
  have f0 : InstrSpec 0x112fd0 [0x53] (PushPre 0x112fd0 1) (pushR64Effect 0x112fd0 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x112fd0 1 3).toInstrSpec (push_r64_effect_step 0x112fd0 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x112fd1 [0x48, 0x83, 0xec, 0x30] (fun s => s.RIP = 0x112fd1) (subR64Imm8Effect 0x112fd1 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x112fd1 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x112fd1 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112fd5 [0x48, 0x89, 0xfb] (fun s => s.RIP = 0x112fd5) (movR64R64Effect 0x112fd5 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x112fd5 3 7).toInstrSpec (mov_r64_r64_effect_step 0x112fd5 0x48 0xfb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112fd8 [0x48, 0x8d, 0x7c, 0x24, 0x8] (fun s => s.RIP = 0x112fd8) (leaR64Effect 0x112fd8 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x112fd8 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x112fd8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112fdd [0x48, 0xb9, 0xb1, 0x43, 0xff, 0x11, 0x55, 0x37, 0x2e, 0x33] (fun s => s.RIP = 0x112fdd) (movR64Imm64Effect 0x112fdd 1 0x332e375511ff43b1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x112fdd 1 0x332e375511ff43b1).toInstrSpec (mov_r64_imm64_effect_step 0x112fdd 0x48 0xb9 (by decide) (by decide) 0x332e375511ff43b1) pre_rip
  have f5 : InstrSpec 0x112fe7 [0x48, 0xc7, 0xc2, 0xe0, 0x25, 0x20, 0x0] (fun s => s.RIP = 0x112fe7) (movR64Imm32Effect 0x112fe7 2 0x2025e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x112fe7 2 0x2025e0).toInstrSpec (mov_r64_imm32_effect_step 0x112fe7 0x48 0xc2 (by decide) (by decide) (by decide) 0x2025e0) pre_rip
  have f6 : InstrSpec 0x112fee [0x49, 0xc7, 0xc0, 0xc0, 0x25, 0x20, 0x0] (fun s => s.RIP = 0x112fee) (movR64Imm32Effect 0x112fee 8 0x2025c0)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x112fee 8 0x2025c0).toInstrSpec (mov_r64_imm32_effect_step 0x112fee 0x49 0xc0 (by decide) (by decide) (by decide) 0x2025c0) pre_rip
  have f7 : InstrSpec 0x112ff5 [0xe8, 0x96, 0xf1, 0xff, 0xff] (PushPre 0x112ff5 5) (callEffect (fun _ => 0x112190) 0x112ffa)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x112ff5 0x112190 0x112ffa).toInstrSpec (call_rel32_effect_step 0x112ff5 0xfffff196 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112fd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112fd5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112fd8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112fdd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112fe7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 63), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112fee) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 63), (3, 57), (4, 55), (5, 5), (6, 6), (7, 59), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ff5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 63), (3, 57), (4, 67), (5, 5), (6, 6), (7, 59), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112190) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l115020 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l115020 :=
  Rest.liftedBlock (rest_l115020 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l115020 x hx)

theorem rest_l11504a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112ffa bytes_l11504a) (entryMap (live .l11504a))
      10 0x112ffa bytes_l11504a b_l11504a := by
  have f0 : InstrSpec 0x112ffa [0x48, 0x8b, 0x44, 0x24, 0x20] (LoadPre 0x112ffa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112ffa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112ffa 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112ffa 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x112ffa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x112fff [0x48, 0x89, 0x43, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112fff 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x112fff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112fff 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x112fff 0 (.base 3 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112fff 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f2 : InstrSpec 0x113003 [0x48, 0x8b, 0x44, 0x24, 0x18] (LoadPre 0x113003 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x113003 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x113003 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x113003 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x113003 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x113008 [0x48, 0x89, 0x43, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x113008 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x113008 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x113008 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x113008 0 (.base 3 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x113008 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11300c [0x48, 0x8b, 0x44, 0x24, 0x8] (LoadPre 0x11300c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11300c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11300c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11300c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11300c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x113011 [0x48, 0x8b, 0x4c, 0x24, 0x10] (LoadPre 0x113011 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x113011 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x113011 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x113011 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x113011 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x113016 [0x48, 0x89, 0x4b, 0x8] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x113016 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x113016 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x113016 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x113016 1 (.base 3 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x113016 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x11301a [0x48, 0x89, 0x3] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11301a 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11301a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11301a 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11301a 0 (.base 3 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11301a 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11301d [0x8b, 0x7c, 0x24, 0x28] (LoadPre 0x11301d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11301d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11301d 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x11301d 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x11301d 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x113021 [0xe8, 0x4a, 0x60, 0x0, 0x0] (PushPre 0x113021 5) (callEffect (fun _ => 0x119070) 0x113026)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x113021 0x119070 0x113026).toInstrSpec (call_rel32_effect_step 0x113021 0x604a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112fff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x113003) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x113008) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11300c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x113011) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x113016) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11301a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11301d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x113021) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 67), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x119070) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l11504a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11504a :=
  Rest.liftedBlock (rest_l11504a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11504a x hx)

theorem rest_l115076 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x113026 bytes_l115076) (entryMap (live .l115076))
      5 0x113026 bytes_l115076 b_l115076 := by
  have f0 : InstrSpec 0x113026 [0x88, 0x43, 0x20] (StorePre 0x113026 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x113026 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x113026 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x113026 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x113026 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x113029 [0x48, 0x89, 0xd8] (fun s => s.RIP = 0x113029) (movR64R64Effect 0x113029 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x113029 0 3).toInstrSpec (mov_r64_r64_effect_step 0x113029 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11302c [0x48, 0x83, 0xc4, 0x30] (fun s => s.RIP = 0x11302c) (addR64Imm8Effect 0x11302c 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11302c 4 0x30).toInstrSpec (add_r64_imm8_effect_step 0x11302c 0x48 0xc4 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x113030 [0x5b] (PopPre 0x113030) (popR64Effect 0x113030 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x113030 1 3).toInstrSpec (pop_r64_effect_step 0x113030 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x113031 [0xc3] (RetPre 0x113031) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x113031).toInstrSpec (ret_effect_step 0x113031) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x113029) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11302c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 56), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x113030) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (2, 2), (3, 58), (4, 59), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x113031) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 54), (2, 2), (3, 58), (4, 62), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l115076 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l115076 :=
  Rest.liftedBlock (rest_l115076 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l115076 x hx)

theorem rest_l1141e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112190 bytes_l1141e0) (entryMap (live .l1141e0))
      0 0x112190 bytes_l1141e0 b_l1141e0 := by
  exact Rest.cut

theorem block_l1141e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1141e0 :=
  Rest.liftedBlock (rest_l1141e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1141e0 x hx)

theorem rest_l1234c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x119070 bytes_l1234c0) (entryMap (live .l1234c0))
      5 0x119070 bytes_l1234c0 b_l1234c0 := by
  have f0 : InstrSpec 0x119070 [0x48, 0x83, 0xec, 0x1] (fun s => s.RIP = 0x119070) (subR64Imm8Effect 0x119070 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x119070 4 0x1).toInstrSpec (sub_r64_imm8_effect_step 0x119070 0x48 0xec 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x119074 [0x40, 0x88, 0x3c, 0x24] (StorePre 0x119074 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119074 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x119074 4 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x119074 4 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x119074 0x40 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x119078 [0xf, 0xb6, 0x4, 0x24] (LoadPre 0x119078 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119078 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x119078 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x119078 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x119078 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11907c [0x48, 0x83, 0xc4, 0x1] (fun s => s.RIP = 0x11907c) (addR64Imm8Effect 0x11907c 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11907c 4 0x1).toInstrSpec (add_r64_imm8_effect_step 0x11907c 0x48 0xc4 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x119080 [0xc3] (RetPre 0x119080) (retEffect)
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

theorem block_l1234c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1234c0 :=
  Rest.liftedBlock (rest_l1234c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1234c0 x hx)

end P256.Proofs.Verifying.Core.Inverse.Machine
