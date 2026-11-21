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

theorem rest_l1218e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1218e0 bytes_l1218e0) (entryMap (live .l1218e0))
      2 0x1218e0 bytes_l1218e0 b_l1218e0 := by
  have f0 : InstrSpec 0x1218e0 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x1218e0) (testR64R64Effect 0x1218e0 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1218e0 2 2).toInstrSpec (test_r64_r64_effect_step 0x1218e0 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1218e3 4 0x280f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1218e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1218e0 :=
  Rest.liftedBlock (rest_l1218e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1218e0 x hx)

theorem rest_l1218e9_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x1218e9 bytes_l1218e9) [(0, 78), (1, 89), (2, 86), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (8, 82), (9, 80), (10, 84), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x12192f bytes_l1218e9_1 b_l1218e9_1 := by
  have f20 : InstrSpec 0x12192f [0x90] (fun s => s.RIP = 0x12192f) (fun _ => nopEffect 0x12192f 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12192f 1).toInstrSpec (nop_effect_step 0x12192f) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 78), (1, 89), (2, 86), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (8, 82), (9, 80), (10, 84), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121930) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 92) (by decide) rfl

theorem rest_l1218e9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1218e9 bytes_l1218e9) (entryMap (live .l1218e9))
      21 0x1218e9 bytes_l1218e9 b_l1218e9 := by
  have f0 : InstrSpec 0x1218e9 [0x55] (PushPre 0x1218e9 1) (pushR64Effect 0x1218e9 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1218e9 1 5).toInstrSpec (push_r64_effect_step 0x1218e9 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1218ea [0x41, 0x57] (PushPre 0x1218ea 2) (pushR64Effect 0x1218ea 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1218ea 2 15).toInstrSpec (push_r64_rex_effect_step 0x1218ea 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1218ec [0x41, 0x56] (PushPre 0x1218ec 2) (pushR64Effect 0x1218ec 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1218ec 2 14).toInstrSpec (push_r64_rex_effect_step 0x1218ec 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1218ee [0x41, 0x55] (PushPre 0x1218ee 2) (pushR64Effect 0x1218ee 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1218ee 2 13).toInstrSpec (push_r64_rex_effect_step 0x1218ee 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1218f0 [0x41, 0x54] (PushPre 0x1218f0 2) (pushR64Effect 0x1218f0 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1218f0 2 12).toInstrSpec (push_r64_rex_effect_step 0x1218f0 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1218f2 [0x53] (PushPre 0x1218f2 1) (pushR64Effect 0x1218f2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1218f2 1 3).toInstrSpec (push_r64_effect_step 0x1218f2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1218f3 [0x48, 0x81, 0xEC, 0x20, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1218f3) (subR64Imm32Effect 0x1218f3 4 0x120)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1218f3 4 0x120).toInstrSpec (sub_r64_imm32_effect_step 0x1218f3 0x48 0xec 0x120 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1218fa [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x1218fa) (movR64R64Effect 0x1218fa 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1218fa 0 2).toInstrSpec (mov_r64_r64_effect_step 0x1218fa 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1218fd [0x48, 0xC1, 0xE0, 0x06] (fun s => s.RIP = 0x1218fd) (shlR64Effect 0x1218fd 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x1218fd 4 0 6).toInstrSpec (shl_r64_imm8_effect_step 0x1218fd 0x48 0xe0 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x121901 [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x121901) (addR64R64Effect 0x121901 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x121901 0 6).toInstrSpec (add_r64_r64_effect_step 0x121901 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x121904 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x121904 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x121904 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121904 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121904 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x121904 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x12190c [0x8B, 0x1F] (LoadPre 0x12190c (fun s => AddrMode.addr (.base 7 .none) s (0x12190c + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x12190c 3 (.base 7 .none))
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x12190c 3 (.base 7 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x12190c 3 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12190e [0x44, 0x8B, 0x77, 0x04] (LoadPre 0x12190e (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x12190e + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12190e 14 (.base 7 (.d8 0x4)))
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x12190e 14 (.base 7 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x12190e 0x44 (by decide) 6 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x121912 [0x8B, 0x47, 0x08] (LoadPre 0x121912 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x121912 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121912 0 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x121912 0 (.base 7 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x121912 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x121915 [0x44, 0x8B, 0x4F, 0x0C] (LoadPre 0x121915 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x121915 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121915 9 (.base 7 (.d8 0xc)))
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x121915 9 (.base 7 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x121915 0x44 (by decide) 1 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x121919 [0x44, 0x8B, 0x47, 0x10] (LoadPre 0x121919 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x121919 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121919 8 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x121919 8 (.base 7 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x121919 0x44 (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x12191d [0x44, 0x8B, 0x57, 0x14] (LoadPre 0x12191d (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x12191d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12191d 10 (.base 7 (.d8 0x14)))
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x12191d 10 (.base 7 (.d8 0x14))).toInstrSpec (mov_r32_m32_effect_step 0x12191d 0x44 (by decide) 2 (.base 7 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x121921 [0x8B, 0x57, 0x18] (LoadPre 0x121921 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x121921 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121921 2 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x121921 2 (.base 7 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x121921 2 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x121924 [0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x121924 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x121924 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121924 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121924 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x121924 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x12192c [0x8B, 0x4F, 0x1C] (LoadPre 0x12192c (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x12192c + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12192c 1 (.base 7 (.d8 0x1c)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12192c 1 (.base 7 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x12192c 1 (.base 7 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218f0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218f2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218f3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218fa) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218fd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121901) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121904) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12190c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 71), (2, 2), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12190e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 71), (2, 2), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121912) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (2, 2), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121915) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (2, 2), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (9, 80), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121919) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 78), (2, 2), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (8, 82), (9, 80), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12191d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 78), (2, 2), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (8, 82), (9, 80), (10, 84), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121921) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (2, 86), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (8, 82), (9, 80), (10, 84), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121924) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 78), (2, 86), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (8, 82), (9, 80), (10, 84), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12192c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 78), (1, 89), (2, 86), (3, 74), (4, 65), (5, 5), (6, 6), (7, 7), (8, 82), (9, 80), (10, 84), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12192f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1218e9_1 code

theorem block_l1218e9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1218e9 :=
  Rest.liftedBlock (rest_l1218e9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1218e9 x hx)

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

theorem_by block_l1218e0_eval :
    program.runBlock (dialect code) ⟨.l1218e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1218e9_eval :
    program.runBlock (dialect code) ⟨.l1218e9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
