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

theorem rest_l126d20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126d20 bytes_l126d20) (entryMap (live .l126d20))
      13 0x126d20 bytes_l126d20 b_l126d20 := by
  have f0 : InstrSpec 0x126d20 [0x55] (PushPre 0x126d20 1) (pushR64Effect 0x126d20 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126d20 1 5).toInstrSpec (push_r64_effect_step 0x126d20 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x126d21 [0x41, 0x57] (PushPre 0x126d21 2) (pushR64Effect 0x126d21 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126d21 2 15).toInstrSpec (push_r64_rex_effect_step 0x126d21 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x126d23 [0x41, 0x56] (PushPre 0x126d23 2) (pushR64Effect 0x126d23 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126d23 2 14).toInstrSpec (push_r64_rex_effect_step 0x126d23 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x126d25 [0x41, 0x55] (PushPre 0x126d25 2) (pushR64Effect 0x126d25 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126d25 2 13).toInstrSpec (push_r64_rex_effect_step 0x126d25 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x126d27 [0x41, 0x54] (PushPre 0x126d27 2) (pushR64Effect 0x126d27 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126d27 2 12).toInstrSpec (push_r64_rex_effect_step 0x126d27 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x126d29 [0x53] (PushPre 0x126d29 1) (pushR64Effect 0x126d29 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x126d29 1 3).toInstrSpec (push_r64_effect_step 0x126d29 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x126d2a [0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126d2a) (subR64Imm32Effect 0x126d2a 4 0xa8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x126d2a 4 0xa8).toInstrSpec (sub_r64_imm32_effect_step 0x126d2a 0x48 0xec 0xa8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x126d31 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x126d31) (movR64R64Effect 0x126d31 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x126d31 3 7).toInstrSpec (mov_r64_r64_effect_step 0x126d31 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x126d34 [0x8B, 0x6A, 0x08] (LoadPre 0x126d34 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x126d34 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x126d34 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x126d34 5 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x126d34 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126d37 [0x44, 0x8B, 0x7E, 0x1C] (LoadPre 0x126d37 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x126d37 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126d37 15 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x126d37 15 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x126d37 0x44 (by decide) 7 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x126d3b [0x45, 0x89, 0xFD] (fun s => s.RIP = 0x126d3b) (movR32R32Effect 0x126d3b 3 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x126d3b 3 13 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x126d3b 0x45 0xfd (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x126d3e [0x41, 0x01, 0xED] (fun s => s.RIP = 0x126d3e) (addR32R32Effect 0x126d3e 3 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x126d3e 3 13 5).toInstrSpec (add_r32_r32_rex_effect_step 0x126d3e 0x41 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d21) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d23) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d25) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d27) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d29) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d2a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d31) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d34) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d37) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d3b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 73), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d3e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d41) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 78) (jcc_rel32_effect_step 0x126d41 2 0x3df) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126d20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126d20 :=
  Rest.liftedBlock (rest_l126d20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126d20 x hx)

theorem rest_l126d47 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126d47 bytes_l126d47) (entryMap (live .l126d47))
      8 0x126d47 bytes_l126d47 b_l126d47 := by
  have f0 : InstrSpec 0x126d47 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x126d47) (movR64R64Effect 0x126d47 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x126d47 14 6).toInstrSpec (mov_r64_r64_effect_step 0x126d47 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126d4a [0x48, 0x8B, 0x36] (LoadPre 0x126d4a (fun s => AddrMode.addr (.base 6 .none) s (0x126d4a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x126d4a 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126d4a 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x126d4a 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126d4d [0x49, 0x8B, 0x56, 0x08] (LoadPre 0x126d4d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126d4d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126d4d 2 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126d4d 2 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x126d4d 0x49 (by decide) 2 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126d51 [0x48, 0x8D, 0x7C, 0x24, 0x18] (fun s => s.RIP = 0x126d51) (leaR64Effect 0x126d51 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x126d51 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x126d51 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x126d56 [0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x126d56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126d56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126d56 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126d56 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x126d56 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x126d5e [0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x126d5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126d5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126d5e 2 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126d5e 2 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x126d5e 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126d66 [0x44, 0x89, 0xE9] (fun s => s.RIP = 0x126d66) (movR32R32Effect 0x126d66 3 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x126d66 3 1 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x126d66 0x44 0xe9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x126d69 [0xE8, 0xE2, 0x0E, 0x00, 0x00] (PushPre 0x126d69 5) (callEffect (fun _ => 0x127c50) 0x126d6e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x126d69 0x127c50 0x126d6e).toInstrSpec (call_rel32_effect_step 0x126d69 0xee2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d4a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d4d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d51) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d56) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d5e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d66) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 63), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d69) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 63), (2, 57), (3, 3), (4, 65), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l126d47 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126d47 :=
  Rest.liftedBlock (rest_l126d47 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126d47 x hx)

theorem rest_l126d6e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126d6e bytes_l126d6e) (entryMap (live .l126d6e))
      3 0x126d6e bytes_l126d6e b_l126d6e := by
  have f0 : InstrSpec 0x126d6e [0x44, 0x8B, 0x64, 0x24, 0x18] (LoadPre 0x126d6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126d6e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126d6e 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x126d6e 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x126d6e 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126d73 [0x41, 0x83, 0xFC, 0x02] (fun s => s.RIP = 0x126d73) (cmpR32Imm8Effect 0x126d73 4 12 0x2)
      [.gpr 12] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126d73 4 12 0x2).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x126d73 0x41 0xfc 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d73) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d77) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x126d77 5 0x30) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126d6e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126d6e :=
  Rest.liftedBlock (rest_l126d6e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126d6e x hx)

theorem rest_l126d79 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126d79 bytes_l126d79) (entryMap (live .l126d79))
      8 0x126d79 bytes_l126d79 b_l126d79 := by
  have f0 : InstrSpec 0x126d79 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x126d79 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126d79 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126d79 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126d79 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x126d79 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126d7e [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x126d7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126d7e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126d7e 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126d7e 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x126d7e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126d83 [0x49, 0x89, 0x06] (StorePre 0x126d83 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126d83 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126d83 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126d83 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x126d83 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x126d86 [0x49, 0x89, 0x4E, 0x08] (StorePre 0x126d86 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126d86 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126d86 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126d86 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126d86 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126d8a [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x126d8a (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126d8a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126d8a 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126d8a 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126d8a 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126d8e [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126d8e) (movR32Imm32Effect 0x126d8e 6 12 0x1)
      [] [] [.reg 12, .rip] :=
    (movR32Imm32Effect_footprint 0x126d8e 6 12 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x126d8e 0x41 0xbc (by decide) (by decide) 0x1) pre_rip
  have f6 : InstrSpec 0x126d94 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x126d94) (cmpR64Imm8Effect 0x126d94 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x126d94 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x126d94 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d83) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d86) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d8a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d8e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d94) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d98) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel32_effect_step 0x126d98 6 0xe5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126d79 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126d79 :=
  Rest.liftedBlock (rest_l126d79 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126d79 x hx)

theorem rest_l126d9e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126d9e bytes_l126d9e) (entryMap (live .l126d9e))
      4 0x126d9e bytes_l126d9e b_l126d9e := by
  have f0 : InstrSpec 0x126d9e [0xB8, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126d9e) (movR32Imm32Effect 0x126d9e 5 0 0x6)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x126d9e 5 0 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x126d9e 0xb8 (by decide) 0x6) pre_rip
  have f1 : InstrSpec 0x126da3 [0x31, 0xF6] (fun s => s.RIP = 0x126da3) (xorR32R32Effect 0x126da3 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126da3 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x126da3 0xf6 (by decide)) pre_rip
  have f2 : InstrSpec 0x126da5 [0x31, 0xC9] (fun s => s.RIP = 0x126da5) (xorR32R32Effect 0x126da5 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126da5 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x126da5 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126da3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126da5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126da7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x126da7 0x5d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126d9e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126d9e :=
  Rest.liftedBlock (rest_l126d9e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126d9e x hx)

theorem rest_l126da9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126da9 bytes_l126da9) (entryMap (live .l126da9))
      17 0x126da9 bytes_l126da9 b_l126da9 := by
  have f0 : InstrSpec 0x126da9 [0x44, 0x8B, 0x7C, 0x24, 0x1C] (LoadPre 0x126da9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x126da9 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126da9 15 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x126da9 15 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x126da9 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126dae [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x126dae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126dae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dae 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126dae 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x126dae 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126db3 [0x4C, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x126db3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126db3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126db3 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x126db3 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x126db3 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126db8 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x30] (LoadPre 0x126db8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126db8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126db8 6 13 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x126db8 6 13 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x126db8 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126dbe [0x48, 0x8B, 0x4C, 0x24, 0x31] (LoadPre 0x126dbe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x126dbe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dbe 1 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126dbe 1 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (mov_r64_m64_effect_step 0x126dbe 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126dc3 [0x48, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x126dc3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126dc3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126dc3 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126dc3 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x126dc3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126dc8 [0x48, 0x8B, 0x4C, 0x24, 0x39] (LoadPre 0x126dc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x126dc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dc8 1 (.sib 4 none 0 (.d8 0x39)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126dc8 1 (.sib 4 none 0 (.d8 0x39))).toInstrSpec (mov_r64_m64_effect_step 0x126dc8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126dcd [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x126dcd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126dcd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126dcd 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126dcd 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x126dcd 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126dd5 [0x48, 0x8B, 0x4C, 0x24, 0x41] (LoadPre 0x126dd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x126dd5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dd5 1 (.sib 4 none 0 (.d8 0x41)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126dd5 1 (.sib 4 none 0 (.d8 0x41))).toInstrSpec (mov_r64_m64_effect_step 0x126dd5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126dda [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x126dda 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x126dda + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126dda 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126dda 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x126dda 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126de2 [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x126de2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126de2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126de2 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126de2 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x126de2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x126de7 [0x48, 0x89, 0x8C, 0x24, 0x8F, 0x00, 0x00, 0x00] (StorePre 0x126de7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126de7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126de7 1 (.sib 4 none 0 (.d32 0x8f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126de7 1 (.sib 4 none 0 (.d32 0x8f))).toInstrSpec (mov_m64_r64_effect_step 0x126de7 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x8f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x126def [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x126def) (movR64R64Effect 0x126def 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x126def 5 0).toInstrSpec (mov_r64_r64_effect_step 0x126def 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x126df2 [0x48, 0xC1, 0xED, 0x20] (fun s => s.RIP = 0x126df2) (shrR64Effect 0x126df2 4 5 32)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR64Effect_footprint 0x126df2 4 5 32).toInstrSpec (shr_r64_imm8_effect_step 0x126df2 0x48 0xed 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x126df6 [0x48, 0xBE, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x126df6) (movR64Imm64Effect 0x126df6 6 0xffffffff00000000)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x126df6 6 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x126df6 0x48 0xbe (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f15 : InstrSpec 0x126e00 [0x4C, 0x21, 0xD6] (fun s => s.RIP = 0x126e00) (andR64R64Effect 0x126e00 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x126e00 6 10).toInstrSpec (and_r64_r64_effect_step 0x126e00 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x126e03 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x126e03) (movR64R64Effect 0x126e03 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x126e03 1 0).toInstrSpec (mov_r64_r64_effect_step 0x126e03 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126dae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126db3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126db8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126dbe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126dc3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 61), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126dc8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 64), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126dcd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 64), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126dd5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 67), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126dda) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 67), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126de2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 55), (1, 70), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126de7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 70), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126def) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 70), (3, 3), (4, 4), (5, 73), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126df2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 70), (3, 3), (4, 4), (5, 75), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126df6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 70), (3, 3), (4, 4), (5, 75), (6, 77), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e00) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 70), (3, 3), (4, 4), (5, 75), (6, 79), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e03) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 55), (1, 81), (3, 3), (4, 4), (5, 75), (6, 79), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e06) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 83) (by decide) rfl

theorem block_l126da9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126da9 :=
  Rest.liftedBlock (rest_l126da9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126da9 x hx)

theorem rest_l126e06_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x126e06 bytes_l126e06) [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x126e5b bytes_l126e06_1 b_l126e06_1 := by
  have f20 : InstrSpec 0x126e5b [0x89, 0x53, 0x19] (StorePre 0x126e5b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x19)) s (0x126e5b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126e5b 2 (.base 3 (.d8 0x19)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126e5b 2 (.base 3 (.d8 0x19))).toInstrSpec (mov_m32_r32_low_effect_step 0x126e5b 2 (.base 3 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x126e5e [0x44, 0x89, 0x23] (StorePre 0x126e5e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x126e5e + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x126e5e 12 (.base 3 .none))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x126e5e 12 (.base 3 .none)).toInstrSpec (mov_m32_r32_effect_step 0x126e5e 0x44 (by decide) 4 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x126e61 [0x44, 0x89, 0x7B, 0x04] (StorePre 0x126e61 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126e61 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126e61 15 (.base 3 (.d8 0x4)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x126e61 15 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x126e61 0x44 (by decide) 7 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x126e65 [0x48, 0x89, 0x43, 0x08] (StorePre 0x126e65 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126e65 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e65 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126e65 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126e65 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x126e69 [0x48, 0x89, 0x4B, 0x10] (StorePre 0x126e69 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126e69 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e69 1 (.base 3 (.d8 0x10)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126e69 1 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126e69 0x48 (by decide) 1 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x126e6d [0x44, 0x88, 0x6B, 0x18] (StorePre 0x126e6d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126e6d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x126e6d 4 13 (.base 3 (.d8 0x18)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x126e6d 4 13 (.base 3 (.d8 0x18))).toInstrSpec (mov_m8_r8_rex_effect_step 0x126e6d 0x44 (by decide) 5 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e5e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e61) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e65) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e69) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e6d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e71) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 93) (by decide) rfl

theorem rest_l126e06 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126e06 bytes_l126e06) (entryMap (live .l126e06))
      26 0x126e06 bytes_l126e06 b_l126e06 := by
  have f0 : InstrSpec 0x126e06 [0x48, 0xC1, 0xE5, 0x20] (fun s => s.RIP = 0x126e06) (shlR64Effect 0x126e06 4 5 32)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR64Effect_footprint 0x126e06 4 5 32).toInstrSpec (shl_r64_imm8_effect_step 0x126e06 0x48 0xe5 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126e0a [0x81, 0xE1, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x126e0a) (andR32Imm32Effect 0x126e0a 6 1 0xffffff00)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x126e0a 6 1 0xffffff00).toInstrSpec (and_r32_imm32_effect_step 0x126e0a 0xe1 0xffffff00 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126e10 [0x48, 0x09, 0xE9] (fun s => s.RIP = 0x126e10) (orR64R64Effect 0x126e10 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x126e10 1 5).toInstrSpec (or_r64_r64_effect_step 0x126e10 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126e13 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x126e13) (movzxR32R8Effect 0x126e13 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x126e13 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x126e13 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x126e16 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x126e16) (orR64R64Effect 0x126e16 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x126e16 0 1).toInstrSpec (or_r64_r64_effect_step 0x126e16 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x126e19 [0x44, 0x89, 0xD1] (fun s => s.RIP = 0x126e19) (movR32R32Effect 0x126e19 3 1 10)
      [.gpr 10] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x126e19 3 1 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x126e19 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x126e1c [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x126e1c) (orR64R64Effect 0x126e1c 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x126e1c 1 6).toInstrSpec (or_r64_r64_effect_step 0x126e1c 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x126e1f [0x8B, 0x54, 0x24, 0x78] (LoadPre 0x126e1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126e1f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e1f 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126e1f 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r32_m32_low_effect_step 0x126e1f 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x126e23 [0x8B, 0x74, 0x24, 0x7B] (LoadPre 0x126e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7b)) s (0x126e23 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e23 6 (.sib 4 none 0 (.d8 0x7b)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x126e23 6 (.sib 4 none 0 (.d8 0x7b))).toInstrSpec (mov_r32_m32_low_effect_step 0x126e23 6 (.sib 4 none 0 (.d8 0x7b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126e27 [0x89, 0x74, 0x24, 0x53] (StorePre 0x126e27 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x126e27 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126e27 6 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126e27 6 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (mov_m32_r32_low_effect_step 0x126e27 6 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126e2b [0x89, 0x54, 0x24, 0x50] (StorePre 0x126e2b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126e2b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126e2b 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126e2b 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m32_r32_low_effect_step 0x126e2b 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x126e2f [0x48, 0x8B, 0x94, 0x24, 0x8F, 0x00, 0x00, 0x00] (LoadPre 0x126e2f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126e2f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126e2f 2 (.sib 4 none 0 (.d32 0x8f)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126e2f 2 (.sib 4 none 0 (.d32 0x8f))).toInstrSpec (mov_r64_m64_effect_step 0x126e2f 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x8f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x126e37 [0x48, 0x89, 0x53, 0x30] (StorePre 0x126e37 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126e37 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e37 2 (.base 3 (.d8 0x30)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126e37 2 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x126e37 0x48 (by decide) 2 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x126e3b [0x48, 0x8B, 0x94, 0x24, 0x87, 0x00, 0x00, 0x00] (LoadPre 0x126e3b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x87)) s (0x126e3b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126e3b 2 (.sib 4 none 0 (.d32 0x87)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126e3b 2 (.sib 4 none 0 (.d32 0x87))).toInstrSpec (mov_r64_m64_effect_step 0x126e3b 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x87)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x126e43 [0x48, 0x89, 0x53, 0x28] (StorePre 0x126e43 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126e43 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e43 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126e43 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x126e43 0x48 (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x126e47 [0x48, 0x8B, 0x54, 0x24, 0x7F] (LoadPre 0x126e47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7f)) s (0x126e47 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126e47 2 (.sib 4 none 0 (.d8 0x7f)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126e47 2 (.sib 4 none 0 (.d8 0x7f))).toInstrSpec (mov_r64_m64_effect_step 0x126e47 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x7f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x126e4c [0x48, 0x89, 0x53, 0x20] (StorePre 0x126e4c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126e4c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e4c 2 (.base 3 (.d8 0x20)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126e4c 2 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x126e4c 0x48 (by decide) 2 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x126e50 [0x8B, 0x54, 0x24, 0x50] (LoadPre 0x126e50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126e50 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e50 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126e50 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x126e50 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x126e54 [0x8B, 0x74, 0x24, 0x53] (LoadPre 0x126e54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x126e54 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e54 6 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x126e54 6 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (mov_r32_m32_low_effect_step 0x126e54 6 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x126e58 [0x89, 0x73, 0x1C] (StorePre 0x126e58 3 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x126e58 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126e58 6 (.base 3 (.d8 0x1c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126e58 6 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m32_r32_low_effect_step 0x126e58 6 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e0a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e10) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e13) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e16) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 57), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e19) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e1c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 65), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e1f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 65), (2, 67), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e23) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 65), (2, 67), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e27) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 61), (1, 65), (2, 67), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e2b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 65), (2, 67), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e2f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 65), (2, 73), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e37) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 61), (1, 65), (2, 73), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e3b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 61), (1, 65), (2, 76), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e43) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 65), (2, 76), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e47) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 65), (2, 79), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e4c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 61), (1, 65), (2, 79), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e50) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e54) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e58) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e5b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l126e06_1 code

theorem block_l126e06 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126e06 :=
  Rest.liftedBlock (rest_l126e06 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126e06 x hx)

theorem rest_l126e71 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126e71 bytes_l126e71) (entryMap (live .l126e71))
      8 0x126e71 bytes_l126e71 b_l126e71 := by
  have f0 : InstrSpec 0x126e71 [0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126e71) (addR64Imm32Effect 0x126e71 4 0xa8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x126e71 4 0xa8).toInstrSpec (add_r64_imm32_effect_step 0x126e71 0x48 0xc4 0xa8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126e78 [0x5B] (PopPre 0x126e78) (popR64Effect 0x126e78 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126e78 1 3).toInstrSpec (pop_r64_effect_step 0x126e78 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x126e79 [0x41, 0x5C] (PopPre 0x126e79) (popR64Effect 0x126e79 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126e79 2 12).toInstrSpec (pop_r64_rex_effect_step 0x126e79 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x126e7b [0x41, 0x5D] (PopPre 0x126e7b) (popR64Effect 0x126e7b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126e7b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x126e7b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x126e7d [0x41, 0x5E] (PopPre 0x126e7d) (popR64Effect 0x126e7d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126e7d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x126e7d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x126e7f [0x41, 0x5F] (PopPre 0x126e7f) (popR64Effect 0x126e7f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126e7f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x126e7f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x126e81 [0x5D] (PopPre 0x126e81) (popR64Effect 0x126e81 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126e81 1 5).toInstrSpec (pop_r64_effect_step 0x126e81 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x126e82 [0xC3] (RetPre 0x126e82) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x126e82).toInstrSpec (ret_effect_step 0x126e82) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e78) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e79) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e7b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e7d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e7f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e81) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e82) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l126e71 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126e71 :=
  Rest.liftedBlock (rest_l126e71 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126e71 x hx)

theorem rest_l126e83 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126e83 bytes_l126e83) (entryMap (live .l126e83))
      5 0x126e83 bytes_l126e83 b_l126e83 := by
  have f0 : InstrSpec 0x126e83 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x126e83) (incR64Effect 0x126e83 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x126e83 0).toInstrSpec (inc_r64_effect_step 0x126e83 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126e86 [0x49, 0x89, 0x46, 0x10] (StorePre 0x126e86 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126e86 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e86 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126e86 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126e86 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x126e8a [0x45, 0x8B, 0x7E, 0x18] (LoadPre 0x126e8a (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126e8a + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126e8a 15 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x126e8a 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x126e8a 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126e8e [0x45, 0x39, 0xFD] (fun s => s.RIP = 0x126e8e) (cmpR32R32Effect 0x126e8e 3 13 15)
      [.gpr 13, .gpr 15] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x126e8e 3 13 15).toInstrSpec (cmp_r32_r32_rex_effect_step 0x126e8e 0x45 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e86) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e8a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e8e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e91) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x126e91 6 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126e83 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126e83 :=
  Rest.liftedBlock (rest_l126e83 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126e83 x hx)

theorem rest_l126e93 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126e93 bytes_l126e93) (entryMap (live .l126e93))
      6 0x126e93 bytes_l126e93 b_l126e93 := by
  have f0 : InstrSpec 0x126e93 [0x41, 0x8D, 0x6F, 0x01] (fun s => s.RIP = 0x126e93) (leaR32Effect 0x126e93 4 5 (.base 15 (.d8 0x1)))
      [.gpr 15] [] [.reg 5, .rip] :=
    (leaR32Effect_footprint 0x126e93 4 5 (.base 15 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x126e93 0x41 (by decide) 5 (.base 15 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126e97 [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126e97) (movR32Imm32Effect 0x126e97 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x126e97 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x126e97 0xb8 (by decide) 0x3) pre_rip
  have f2 : InstrSpec 0x126e9c [0x31, 0xF6] (fun s => s.RIP = 0x126e9c) (xorR32R32Effect 0x126e9c 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126e9c 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x126e9c 0xf6 (by decide)) pre_rip
  have f3 : InstrSpec 0x126e9e [0x45, 0x89, 0xFA] (fun s => s.RIP = 0x126e9e) (movR32R32Effect 0x126e9e 3 10 15)
      [.gpr 15] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x126e9e 3 10 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x126e9e 0x45 0xfa (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x126ea1 [0x31, 0xC9] (fun s => s.RIP = 0x126ea1) (xorR32R32Effect 0x126ea1 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126ea1 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x126ea1 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e97) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e9c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 53), (6, 57), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126e9e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 53), (6, 57), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ea1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (3, 3), (4, 4), (5, 53), (6, 57), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ea3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 63) (jmp_rel32_effect_step 0x126ea3 0xffffff5e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126e93 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126e93 :=
  Rest.liftedBlock (rest_l126e93 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126e93 x hx)

theorem rest_l126ea8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126ea8 bytes_l126ea8) (entryMap (live .l126ea8))
      3 0x126ea8 bytes_l126ea8 b_l126ea8 := by
  have f0 : InstrSpec 0x126ea8 [0x45, 0x89, 0x6E, 0x18] (StorePre 0x126ea8 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126ea8 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126ea8 13 (.base 14 (.d8 0x18)))
      [.gpr 13, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x126ea8 13 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126ea8 0x45 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126eac [0x85, 0xED] (fun s => s.RIP = 0x126eac) (testR32R32Effect 0x126eac 2 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x126eac 2 5 5).toInstrSpec (test_r32_r32_effect_step 0x126eac 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126eac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126eae) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x126eae 4 0xd1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126ea8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126ea8 :=
  Rest.liftedBlock (rest_l126ea8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126ea8 x hx)

theorem rest_l126eb4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126eb4 bytes_l126eb4) (entryMap (live .l126eb4))
      4 0x126eb4 bytes_l126eb4 b_l126eb4 := by
  have f0 : InstrSpec 0x126eb4 [0x48, 0x8D, 0x7C, 0x24, 0x18] (fun s => s.RIP = 0x126eb4) (leaR64Effect 0x126eb4 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x126eb4 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x126eb4 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126eb9 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x126eb9) (movR64R64Effect 0x126eb9 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x126eb9 6 14).toInstrSpec (mov_r64_r64_effect_step 0x126eb9 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126ebc [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126ebc) (movR32Imm32Effect 0x126ebc 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x126ebc 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x126ebc 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x126ec1 [0xE8, 0xBA, 0x0C, 0x00, 0x00] (PushPre 0x126ec1 5) (callEffect (fun _ => 0x127b80) 0x126ec6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x126ec1 0x127b80 0x126ec6).toInstrSpec (call_rel32_effect_step 0x126ec1 0xcba (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126eb9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ebc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ec1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l126eb4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126eb4 :=
  Rest.liftedBlock (rest_l126eb4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126eb4 x hx)

theorem rest_l126ec6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126ec6 bytes_l126ec6) (entryMap (live .l126ec6))
      3 0x126ec6 bytes_l126ec6 b_l126ec6 := by
  have f0 : InstrSpec 0x126ec6 [0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x126ec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126ec6 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126ec6 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x126ec6 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x126ec6 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126eca [0x83, 0xFF, 0x02] (fun s => s.RIP = 0x126eca) (cmpR32Imm8Effect 0x126eca 3 7 0x2)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126eca 3 7 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126eca 0xff 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126eca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ecd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x126ecd 5 0x52) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126ec6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126ec6 :=
  Rest.liftedBlock (rest_l126ec6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126ec6 x hx)

theorem rest_l126ecf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126ecf bytes_l126ecf) (entryMap (live .l126ecf))
      3 0x126ecf bytes_l126ecf b_l126ecf := by
  have f0 : InstrSpec 0x126ecf [0x48, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x126ecf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126ecf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ecf 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126ecf 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x126ecf 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126ed4 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x126ed4) (cmpR64Imm8Effect 0x126ed4 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x126ed4 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x126ed4 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ed4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ed8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x126ed8 5 0x259) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126ecf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126ecf :=
  Rest.liftedBlock (rest_l126ecf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126ecf x hx)

theorem rest_l126ede [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126ede bytes_l126ede) (entryMap (live .l126ede))
      7 0x126ede bytes_l126ede b_l126ede := by
  have f0 : InstrSpec 0x126ede [0xFF, 0xCD] (fun s => s.RIP = 0x126ede) (decR32Effect 0x126ede 2 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (decR32Effect_footprint 0x126ede 2 5).toInstrSpec (dec_r32_effect_step 0x126ede 0xcd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126ee0 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x126ee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126ee0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ee0 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126ee0 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x126ee0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126ee5 [0x44, 0x0F, 0xB6, 0x28] (LoadPre 0x126ee5 (fun s => AddrMode.addr (.base 0 .none) s (0x126ee5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x126ee5 4 13 (.base 0 .none))
      [.gpr 0] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x126ee5 4 13 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x126ee5 0x44 (by decide) 5 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126ee9 [0x48, 0x8D, 0x7C, 0x24, 0x18] (fun s => s.RIP = 0x126ee9) (leaR64Effect 0x126ee9 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x126ee9 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x126ee9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x126eee [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x126eee) (movR64R64Effect 0x126eee 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x126eee 6 14).toInstrSpec (mov_r64_r64_effect_step 0x126eee 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x126ef1 [0x89, 0xEA] (fun s => s.RIP = 0x126ef1) (movR32R32Effect 0x126ef1 2 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x126ef1 2 2 5).toInstrSpec (mov_r32_r32_effect_step 0x126ef1 0xea (by decide)) pre_rip
  have f6 : InstrSpec 0x126ef3 [0xE8, 0x88, 0x0C, 0x00, 0x00] (PushPre 0x126ef3 5) (callEffect (fun _ => 0x127b80) 0x126ef8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x126ef3 0x127b80 0x126ef8).toInstrSpec (call_rel32_effect_step 0x126ef3 0xc88 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ee0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ee5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ee9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126eee) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 53), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ef1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 63), (3, 3), (4, 4), (5, 53), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ef3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 63), (3, 3), (4, 65), (5, 53), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l126ede [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126ede :=
  Rest.liftedBlock (rest_l126ede code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126ede x hx)

theorem rest_l126ef8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126ef8 bytes_l126ef8) (entryMap (live .l126ef8))
      3 0x126ef8 bytes_l126ef8 b_l126ef8 := by
  have f0 : InstrSpec 0x126ef8 [0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x126ef8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126ef8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126ef8 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x126ef8 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x126ef8 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126efc [0x83, 0xFF, 0x02] (fun s => s.RIP = 0x126efc) (cmpR32Imm8Effect 0x126efc 3 7 0x2)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126efc 3 7 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126efc 0xff 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126efc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126eff) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x126eff 5 0x20) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126ef8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126ef8 :=
  Rest.liftedBlock (rest_l126ef8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126ef8 x hx)

theorem rest_l126f01 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f01 bytes_l126f01) (entryMap (live .l126f01))
      4 0x126f01 bytes_l126f01 b_l126f01 := by
  have f0 : InstrSpec 0x126f01 [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x126f01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126f01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f01 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126f01 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x126f01 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126f06 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x126f06) (movR64R64Effect 0x126f06 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x126f06 0 2).toInstrSpec (mov_r64_r64_effect_step 0x126f06 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126f09 [0x48, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x126f09) (shrR64Effect 0x126f09 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x126f09 4 0 32).toInstrSpec (shr_r64_imm8_effect_step 0x126f09 0x48 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f06) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f09) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.fresh (n := 57) f2 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x126f09 4 0 32 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f0d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x126f0d 4 0x190) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126f01 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f01 :=
  Rest.liftedBlock (rest_l126f01 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f01 x hx)

theorem rest_l126f13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f13 bytes_l126f13) (entryMap (live .l126f13))
      4 0x126f13 bytes_l126f13 b_l126f13 := by
  have f0 : InstrSpec 0x126f13 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x126f13 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126f13 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f13 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126f13 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126f13 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126f18 [0xB9, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126f18) (movR32Imm32Effect 0x126f18 5 1 0xc)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x126f18 5 1 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x126f18 0xb9 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x126f1d [0x31, 0xFF] (fun s => s.RIP = 0x126f1d) (xorR32R32Effect 0x126f1d 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126f1d 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x126f1d 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f18) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f1d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (7, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f1f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 58) (jmp_rel8_effect_step 0x126f1f 0x41 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126f13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f13 :=
  Rest.liftedBlock (rest_l126f13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f13 x hx)

theorem rest_l126f21 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f21 bytes_l126f21) (entryMap (live .l126f21))
      13 0x126f21 bytes_l126f21 b_l126f21 := by
  have f0 : InstrSpec 0x126f21 [0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x126f21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x126f21 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126f21 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126f21 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x126f21 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126f25 [0x48, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x126f25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126f25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f25 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126f25 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x126f25 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126f2a [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x126f2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126f2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f2a 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126f2a 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x126f2a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126f2f [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x126f2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126f2f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f2f 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126f2f 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126f2f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126f34 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x30] (LoadPre 0x126f34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126f34 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126f34 6 13 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x126f34 6 13 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x126f34 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126f3a [0x48, 0x8B, 0x44, 0x24, 0x31] (LoadPre 0x126f3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x126f3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f3a 0 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126f3a 0 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (mov_r64_m64_effect_step 0x126f3a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x126f3f [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x126f3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126f3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f3f 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126f3f 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x126f3f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x126f44 [0x48, 0x8B, 0x44, 0x24, 0x39] (LoadPre 0x126f44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x126f44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f44 0 (.sib 4 none 0 (.d8 0x39)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126f44 0 (.sib 4 none 0 (.d8 0x39))).toInstrSpec (mov_r64_m64_effect_step 0x126f44 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x126f49 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x126f49 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126f49 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f49 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126f49 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x126f49 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x126f4e [0x48, 0x8B, 0x44, 0x24, 0x41] (LoadPre 0x126f4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x126f4e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f4e 0 (.sib 4 none 0 (.d8 0x41)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126f4e 0 (.sib 4 none 0 (.d8 0x41))).toInstrSpec (mov_r64_m64_effect_step 0x126f4e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x126f53 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x126f53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126f53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f53 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126f53 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x126f53 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x126f58 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x126f58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126f58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f58 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126f58 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x126f58 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x126f5d [0x48, 0x89, 0x44, 0x24, 0x6F] (StorePre 0x126f5d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x126f5d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f5d 0 (.sib 4 none 0 (.d8 0x6f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126f5d 0 (.sib 4 none 0 (.d8 0x6f))).toInstrSpec (mov_m64_r64_effect_step 0x126f5d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x6f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f25) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f2a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f2f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f34) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f3a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f3f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f44) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f49) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f4e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f53) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f58) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f5d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f62) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l126f21 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f21 :=
  Rest.liftedBlock (rest_l126f21 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f21 x hx)

theorem rest_l126f62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f62 bytes_l126f62) (entryMap (live .l126f62))
      5 0x126f62 bytes_l126f62 b_l126f62 := by
  have f0 : InstrSpec 0x126f62 [0x89, 0x54, 0x24, 0x0C] (StorePre 0x126f62 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126f62 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126f62 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126f62 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x126f62 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126f66 [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x126f66) (movR32R32Effect 0x126f66 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x126f66 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x126f66 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126f69 [0x41, 0x81, 0xE0, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x126f69) (andR32Imm32Effect 0x126f69 7 8 0xffffff00)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x126f69 7 8 0xffffff00).toInstrSpec (and_r32_imm32_rex_effect_step 0x126f69 0x41 0xe0 0xffffff00 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126f70 [0x49, 0xBB, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x126f70) (movR64Imm64Effect 0x126f70 11 0xffffff0000000000)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x126f70 11 0xffffff0000000000).toInstrSpec (mov_r64_imm64_effect_step 0x126f70 0x49 0xbb (by decide) (by decide) 0xffffff0000000000) pre_rip
  have f4 : InstrSpec 0x126f7a [0x49, 0x21, 0xCB] (fun s => s.RIP = 0x126f7a) (andR64R64Effect 0x126f7a 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x126f7a 11 1).toInstrSpec (and_r64_r64_effect_step 0x126f7a 0x49 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f66) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 54), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f69) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f70) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 56), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f7a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 56), (11, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f7d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l126f62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f62 :=
  Rest.liftedBlock (rest_l126f62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f62 x hx)

theorem rest_l126f7d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f7d bytes_l126f7d) (entryMap (live .l126f7d))
      3 0x126f7d bytes_l126f7d b_l126f7d := by
  have f0 : InstrSpec 0x126f7d [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x126f7d) (movR64R64Effect 0x126f7d 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x126f7d 9 1).toInstrSpec (mov_r64_r64_effect_step 0x126f7d 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126f80 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x126f80) (movR64R64Effect 0x126f80 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x126f80 0 1).toInstrSpec (mov_r64_r64_effect_step 0x126f80 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f80) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f83) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x126f83 0x1a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126f7d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f7d :=
  Rest.liftedBlock (rest_l126f7d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f7d x hx)

theorem rest_l126f85 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f85 bytes_l126f85) (entryMap (live .l126f85))
      2 0x126f85 bytes_l126f85 b_l126f85 := by
  have f0 : InstrSpec 0x126f85 [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126f85) (movR32Imm32Effect 0x126f85 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x126f85 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x126f85 0xb8 (by decide) 0xc) pre_rip
  have f1 : InstrSpec 0x126f8a [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x126f8a) (xorR32R32Effect 0x126f8a 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126f8a 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x126f8a 0x45 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f8a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f8d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l126f85 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f85 :=
  Rest.liftedBlock (rest_l126f85 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f85 x hx)

theorem rest_l126f8d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f8d bytes_l126f8d) (entryMap (live .l126f8d))
      4 0x126f8d bytes_l126f8d b_l126f8d := by
  have f0 : InstrSpec 0x126f8d [0xC7, 0x44, 0x24, 0x0C, 0x00, 0x00, 0x00, 0x00] (StorePre 0x126f8d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126f8d + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x126f8d 8 (.sib 4 none 0 (.d8 0xc)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x126f8d 8 (.sib 4 none 0 (.d8 0xc)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x126f8d (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126f95 [0x31, 0xC9] (fun s => s.RIP = 0x126f95) (xorR32R32Effect 0x126f95 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126f95 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x126f95 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x126f97 [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x126f97) (xorR32R32Effect 0x126f97 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126f97 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x126f97 0x45 0xdb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126f9a [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x126f9a) (xorR32R32Effect 0x126f9a 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126f9a 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x126f9a 0x45 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f95) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f97) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f9a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 58), (11, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f9d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l126f8d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f8d :=
  Rest.liftedBlock (rest_l126f8d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f8d x hx)

theorem rest_l126f9d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f9d bytes_l126f9d) (entryMap (live .l126f9d))
      1 0x126f9d bytes_l126f9d b_l126f9d := by
  have f0 : InstrSpec 0x126f9d [0x31, 0xFF] (fun s => s.RIP = 0x126f9d) (xorR32R32Effect 0x126f9d 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x126f9d 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x126f9d 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126f9f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l126f9d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f9d :=
  Rest.liftedBlock (rest_l126f9d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f9d x hx)

theorem rest_l126f9f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126f9f bytes_l126f9f) (entryMap (live .l126f9f))
      17 0x126f9f bytes_l126f9f b_l126f9f := by
  have f0 : InstrSpec 0x126f9f [0x45, 0x8B, 0x56, 0x18] (LoadPre 0x126f9f (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126f9f + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126f9f 10 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x126f9f 10 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x126f9f 0x45 (by decide) 2 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126fa3 [0x41, 0x8B, 0x6E, 0x1C] (LoadPre 0x126fa3 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126fa3 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126fa3 5 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 5, .rip] :=
    (movR32M32Effect_footprint 0x126fa3 5 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x126fa3 0x41 (by decide) 5 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126fa7 [0x41, 0x29, 0xEA] (fun s => s.RIP = 0x126fa7) (subR32R32Effect 0x126fa7 3 10 5)
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (subR32R32Effect_footprint 0x126fa7 3 10 5).toInstrSpec (sub_r32_r32_rex_effect_step 0x126fa7 0x41 0xea (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126faa [0x0F, 0x96, 0xC2] (fun s => s.RIP = 0x126faa) (atFlags (condHolds 6) (setccR8Effect 0x126faa 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x126faa 3 2 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x126faa 6 0xc2 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x126fad [0x48, 0x8B, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x126fad (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126fad + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126fad 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126fad 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x126fad 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126fb5 [0x49, 0x89, 0x36] (StorePre 0x126fb5 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126fb5 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126fb5 6 (.base 14 .none))
      [.gpr 6, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126fb5 6 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x126fb5 0x49 (by decide) 6 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126fb8 [0x48, 0x8B, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x126fb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126fb8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126fb8 6 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126fb8 6 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x126fb8 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126fc0 [0x49, 0x89, 0x76, 0x08] (StorePre 0x126fc0 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126fc0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126fc0 6 (.base 14 (.d8 0x8)))
      [.gpr 6, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126fc0 6 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126fc0 0x49 (by decide) 6 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126fc4 [0x45, 0x89, 0x7E, 0x18] (StorePre 0x126fc4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126fc4 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126fc4 15 (.base 14 (.d8 0x18)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x126fc4 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126fc4 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x126fc8 [0x4D, 0x8B, 0x7E, 0x10] (LoadPre 0x126fc8 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126fc8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126fc8 15 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x126fc8 15 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126fc8 0x4d (by decide) 7 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x126fcc [0x49, 0x83, 0xFF, 0x01] (fun s => s.RIP = 0x126fcc) (cmpR64Imm8Effect 0x126fcc 15 0x1)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x126fcc 15 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x126fcc 0x49 0xff 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x126fd0 [0x49, 0x83, 0xD7, 0xFF] (fun s => s.RIP = 0x126fd0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126fd0 15 0xff))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x126fd0 15 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x126fd0 0x49 0xd7 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f12 : InstrSpec 0x126fd4 [0x4D, 0x89, 0x7E, 0x10] (StorePre 0x126fd4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126fd4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126fd4 15 (.base 14 (.d8 0x10)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126fd4 15 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126fd4 0x4d (by decide) 7 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x126fd8 [0x83, 0xFF, 0x02] (fun s => s.RIP = 0x126fd8) (cmpR32Imm8Effect 0x126fd8 3 7 0x2)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126fd8 3 7 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126fd8 0xff 0x2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x126fdb [0x41, 0x0F, 0x95, 0xC7] (fun s => s.RIP = 0x126fdb) (atFlags (condHolds 5) (setccR8Effect 0x126fdb 4 15))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 15, .rip] :=
    (setccR8Effect_footprint 0x126fdb 4 15 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x126fdb 5 0x41 (by decide) 0xc7 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x126fdf [0x41, 0x08, 0xD7] (fun s => s.RIP = 0x126fdf) (orR8R8Effect 0x126fdf 3 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (orR8R8Effect_footprint 0x126fdf 3 15 2).toInstrSpec (or_r8_r8_rex_effect_step 0x126fdf 0x41 0xd7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fa3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fa7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 59) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126faa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fad) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 63), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fb5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 63), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fb8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fc0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fc4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fc8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 70), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fcc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 70), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fd0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fd4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fd8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 74), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fdb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 79), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fdf) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fe2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 83) (jcc_rel8_effect_step 0x126fe2 4 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126f9f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126f9f :=
  Rest.liftedBlock (rest_l126f9f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126f9f x hx)

theorem rest_l126fe4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126fe4 bytes_l126fe4) (entryMap (live .l126fe4))
      13 0x126fe4 bytes_l126fe4 b_l126fe4 := by
  have f0 : InstrSpec 0x126fe4 [0x48, 0xBA, 0x00, 0x00, 0x00, 0x00, 0xFF, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126fe4) (movR64Imm64Effect 0x126fe4 2 0xff00000000)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x126fe4 2 0xff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x126fe4 0x48 0xba (by decide) (by decide) 0xff00000000) pre_rip
  have f1 : InstrSpec 0x126fee [0x49, 0x21, 0xD1] (fun s => s.RIP = 0x126fee) (andR64R64Effect 0x126fee 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x126fee 9 2).toInstrSpec (and_r64_r64_effect_step 0x126fee 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126ff1 [0x4D, 0x09, 0xD9] (fun s => s.RIP = 0x126ff1) (orR64R64Effect 0x126ff1 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x126ff1 9 11).toInstrSpec (or_r64_r64_effect_step 0x126ff1 0x4d 0xd9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126ff4 [0x48, 0x8B, 0x54, 0x24, 0x6F] (LoadPre 0x126ff4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x126ff4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ff4 2 (.sib 4 none 0 (.d8 0x6f)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126ff4 2 (.sib 4 none 0 (.d8 0x6f))).toInstrSpec (mov_r64_m64_effect_step 0x126ff4 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x6f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126ff9 [0x48, 0x89, 0x94, 0x24, 0x8F, 0x00, 0x00, 0x00] (StorePre 0x126ff9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126ff9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126ff9 2 (.sib 4 none 0 (.d32 0x8f)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126ff9 2 (.sib 4 none 0 (.d32 0x8f))).toInstrSpec (mov_m64_r64_effect_step 0x126ff9 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x8f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127001 [0x48, 0x8B, 0x54, 0x24, 0x68] (LoadPre 0x127001 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x127001 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127001 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x127001 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x127001 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x127006 [0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x127006 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x127006 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x127006 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127006 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x127006 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12700e [0x48, 0x8B, 0x54, 0x24, 0x58] (LoadPre 0x12700e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12700e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12700e 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12700e 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x12700e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x127013 [0x4C, 0x8B, 0x54, 0x24, 0x60] (LoadPre 0x127013 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x127013 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127013 10 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x127013 10 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x127013 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x127018 [0x4C, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x127018 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x127018 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x127018 10 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127018 10 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x127018 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x127020 [0x48, 0x89, 0x54, 0x24, 0x78] (StorePre 0x127020 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x127020 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127020 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127020 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x127020 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x127025 [0x83, 0xFF, 0x02] (fun s => s.RIP = 0x127025) (cmpR32Imm8Effect 0x127025 3 7 0x2)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x127025 3 7 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x127025 0xff 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126fee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 55), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ff1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ff4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126ff9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127001) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127006) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12700e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127013) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 67), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127018) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 67), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127020) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 67), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127025) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 67), (11, 11), (13, 13), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127028) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel8_effect_step 0x127028 5 0x4f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126fe4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126fe4 :=
  Rest.liftedBlock (rest_l126fe4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126fe4 x hx)

theorem rest_l12702a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12702a bytes_l12702a) (entryMap (live .l12702a))
      14 0x12702a bytes_l12702a b_l12702a := by
  have f0 : InstrSpec 0x12702a [0x81, 0xE1, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x12702a) (andR32Imm32Effect 0x12702a 6 1 0xffffff00)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x12702a 6 1 0xffffff00).toInstrSpec (and_r32_imm32_effect_step 0x12702a 0xe1 0xffffff00 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127030 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x127030) (movzxR32R8Effect 0x127030 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x127030 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x127030 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127033 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x127033) (orR64R64Effect 0x127033 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x127033 0 1).toInstrSpec (or_r64_r64_effect_step 0x127033 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127036 [0x4C, 0x09, 0xC8] (fun s => s.RIP = 0x127036) (orR64R64Effect 0x127036 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x127036 0 9).toInstrSpec (or_r64_r64_effect_step 0x127036 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127039 [0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x127039 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x127039 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127039 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x127039 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r32_m32_low_effect_step 0x127039 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12703d [0x8B, 0x54, 0x24, 0x5B] (LoadPre 0x12703d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x12703d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12703d 2 (.sib 4 none 0 (.d8 0x5b)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x12703d 2 (.sib 4 none 0 (.d8 0x5b))).toInstrSpec (mov_r32_m32_low_effect_step 0x12703d 2 (.sib 4 none 0 (.d8 0x5b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x127041 [0x89, 0x53, 0x1C] (StorePre 0x127041 3 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x127041 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127041 2 (.base 3 (.d8 0x1c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127041 2 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m32_r32_low_effect_step 0x127041 2 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x127044 [0x89, 0x4B, 0x19] (StorePre 0x127044 3 (fun s => AddrMode.addr (.base 3 (.d8 0x19)) s (0x127044 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127044 1 (.base 3 (.d8 0x19)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127044 1 (.base 3 (.d8 0x19))).toInstrSpec (mov_m32_r32_low_effect_step 0x127044 1 (.base 3 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x127047 [0x48, 0x89, 0x43, 0x08] (StorePre 0x127047 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x127047 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127047 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127047 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127047 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12704b [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x12704b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12704b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12704b 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12704b 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12704b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x127050 [0x48, 0x89, 0x43, 0x10] (StorePre 0x127050 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x127050 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127050 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127050 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127050 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x127054 [0x44, 0x88, 0x6B, 0x18] (StorePre 0x127054 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x127054 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127054 4 13 (.base 3 (.d8 0x18)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x127054 4 13 (.base 3 (.d8 0x18))).toInstrSpec (mov_m8_r8_rex_effect_step 0x127054 0x44 (by decide) 5 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x127058 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x127058 6 (fun s => AddrMode.addr (.base 3 .none) s (0x127058 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127058 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127058 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x127058 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127030) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127033) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127036) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127039) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12703d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127041) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127044) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127047) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12704b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127050) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127054) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127058) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12705e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 73) (jmp_rel32_effect_step 0x12705e 0xfffffe0e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12702a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12702a :=
  Rest.liftedBlock (rest_l12702a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12702a x hx)

theorem rest_l127063 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127063 bytes_l127063) (entryMap (live .l127063))
      6 0x127063 bytes_l127063 b_l127063 := by
  have f0 : InstrSpec 0x127063 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x127063 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x127063 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x127063 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x127063 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x127063 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127068 [0xB8, 0x13, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127068) (movR32Imm32Effect 0x127068 5 0 0x13)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x127068 5 0 0x13).toInstrSpec (mov_r32_imm32_effect_step 0x127068 0xb8 (by decide) 0x13) pre_rip
  have f2 : InstrSpec 0x12706d [0x31, 0xF6] (fun s => s.RIP = 0x12706d) (xorR32R32Effect 0x12706d 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12706d 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x12706d 0xf6 (by decide)) pre_rip
  have f3 : InstrSpec 0x12706f [0x41, 0x89, 0xEF] (fun s => s.RIP = 0x12706f) (movR32R32Effect 0x12706f 3 15 5)
      [.gpr 5] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x12706f 3 15 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x12706f 0x41 0xef (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127072 [0x31, 0xC9] (fun s => s.RIP = 0x127072) (xorR32R32Effect 0x127072 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127072 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x127072 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127068) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12706d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (3, 3), (4, 4), (5, 5), (6, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12706f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (3, 3), (4, 4), (5, 5), (6, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127072) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 54), (1, 60), (3, 3), (4, 4), (5, 5), (6, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127074) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 62) (jmp_rel32_effect_step 0x127074 0xfffffd8d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127063 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127063 :=
  Rest.liftedBlock (rest_l127063 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127063 x hx)

theorem rest_l127079 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127079 bytes_l127079) (entryMap (live .l127079))
      9 0x127079 bytes_l127079 b_l127079 := by
  have f0 : InstrSpec 0x127079 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x0C] (LoadPre 0x127079 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x127079 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x127079 6 15 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x127079 6 15 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x127079 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12707f [0x45, 0x09, 0xC7] (fun s => s.RIP = 0x12707f) (orR32R32Effect 0x12707f 3 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (orR32R32Effect_footprint 0x12707f 3 15 8).toInstrSpec (or_r32_r32_rex_effect_step 0x12707f 0x45 0xc7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127082 [0x49, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x127082) (shrR64Effect 0x127082 4 9 32)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x127082 4 9 32).toInstrSpec (shr_r64_imm8_effect_step 0x127082 0x49 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127086 [0x48, 0xBE, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x127086) (movR64Imm64Effect 0x127086 6 0xffffffff00000000)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x127086 6 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x127086 0x48 0xbe (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f4 : InstrSpec 0x127090 [0x4C, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x127090 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127090 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127090 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x127090 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x127090 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x127095 [0x4C, 0x21, 0xD6] (fun s => s.RIP = 0x127095) (andR64R64Effect 0x127095 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x127095 6 10).toInstrSpec (and_r64_r64_effect_step 0x127095 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x127098 [0x41, 0x89, 0xFC] (fun s => s.RIP = 0x127098) (movR32R32Effect 0x127098 3 12 7)
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x127098 3 12 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x127098 0x41 0xfc (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12709b [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x12709b) (movR32R32Effect 0x12709b 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x12709b 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x12709b 0x44 0xcd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12707f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127082) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 57), (11, 11), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127086) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 57), (11, 11), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127090) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 57), (10, 61), (11, 11), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127095) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 57), (10, 61), (11, 11), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127098) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 57), (10, 61), (11, 11), (12, 65), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12709b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 67), (6, 63), (7, 7), (8, 8), (9, 57), (10, 61), (11, 11), (12, 65), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12709e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 69) (jmp_rel32_effect_step 0x12709e 0xfffffd63 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127079 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127079 :=
  Rest.liftedBlock (rest_l127079 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127079 x hx)

theorem rest_l1270a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1270a3 bytes_l1270a3) (entryMap (live .l1270a3))
      4 0x1270a3 bytes_l1270a3 b_l1270a3 := by
  have f0 : InstrSpec 0x1270a3 [0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1270a3) (movR64Imm64Effect 0x1270a3 9 0x200000000)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x1270a3 9 0x200000000).toInstrSpec (mov_r64_imm64_effect_step 0x1270a3 0x49 0xb9 (by decide) (by decide) 0x200000000) pre_rip
  have f1 : InstrSpec 0x1270ad [0xB8, 0x15, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1270ad) (movR32Imm32Effect 0x1270ad 5 0 0x15)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1270ad 5 0 0x15).toInstrSpec (mov_r32_imm32_effect_step 0x1270ad 0xb8 (by decide) 0x15) pre_rip
  have f2 : InstrSpec 0x1270b2 [0x41, 0x80, 0xFD, 0x07] (fun s => s.RIP = 0x1270b2) (cmpR8Imm8Effect 0x1270b2 4 13 0x7)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1270b2 4 13 0x7).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x1270b2 0x41 0xfd 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270ad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270b6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x1270b6 7 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1270a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1270a3 :=
  Rest.liftedBlock (rest_l1270a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1270a3 x hx)

theorem rest_l1270b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1270b8 bytes_l1270b8) (entryMap (live .l1270b8))
      6 0x1270b8 bytes_l1270b8 b_l1270b8 := by
  have f0 : InstrSpec 0x1270b8 [0x45, 0x84, 0xED] (fun s => s.RIP = 0x1270b8) (testR8R8Effect 0x1270b8 3 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1270b8 3 13 13).toInstrSpec (test_r8_r8_rex_effect_step 0x1270b8 0x45 0xed (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1270bb [0x0F, 0x95, 0xC1] (fun s => s.RIP = 0x1270bb) (atFlags (condHolds 5) (setccR8Effect 0x1270bb 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x1270bb 3 1 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1270bb 5 0xc1 (by decide) (by decide) c)) pre_rip
  have f2 : InstrSpec 0x1270be [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x1270be) (testR64R64Effect 0x1270be 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1270be 2 2).toInstrSpec (test_r64_r64_effect_step 0x1270be 0x48 0xd2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1270c1 [0x40, 0x0F, 0x94, 0xC6] (fun s => s.RIP = 0x1270c1) (atFlags (condHolds 4) (setccR8Effect 0x1270c1 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x1270c1 4 6 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1270c1 4 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f4 : InstrSpec 0x1270c5 [0x40, 0x84, 0xF1] (fun s => s.RIP = 0x1270c5) (testR8R8Effect 0x1270c5 3 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1270c5 3 1 6).toInstrSpec (test_r8_r8_rex_effect_step 0x1270c5 0x40 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270bb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270be) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270c1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270c5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270c8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x1270c8 4 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1270b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1270b8 :=
  Rest.liftedBlock (rest_l1270b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1270b8 x hx)

theorem rest_l1270ca [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1270ca bytes_l1270ca) (entryMap (live .l1270ca))
      5 0x1270ca bytes_l1270ca b_l1270ca := by
  have f0 : InstrSpec 0x1270ca [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1270ca) (xorR32R32Effect 0x1270ca 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1270ca 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1270ca 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1270cd [0xC7, 0x44, 0x24, 0x0C, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1270cd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1270cd + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1270cd 8 (.sib 4 none 0 (.d8 0xc)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1270cd 8 (.sib 4 none 0 (.d8 0xc)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x1270cd (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1270d5 [0x31, 0xC9] (fun s => s.RIP = 0x1270d5) (xorR32R32Effect 0x1270d5 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1270d5 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1270d5 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x1270d7 [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x1270d7) (xorR32R32Effect 0x1270d7 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1270d7 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1270d7 0x45 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270cd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270d5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (2, 2), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270d7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 56), (2, 2), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270da) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 60) (jmp_rel32_effect_step 0x1270da 0xfffffebe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1270ca [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1270ca :=
  Rest.liftedBlock (rest_l1270ca code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1270ca x hx)

theorem rest_l1270df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1270df bytes_l1270df) (entryMap (live .l1270df))
      5 0x1270df bytes_l1270df b_l1270df := by
  have f0 : InstrSpec 0x1270df [0x41, 0x0F, 0xB6, 0xC5] (fun s => s.RIP = 0x1270df) (movzxR32R8Effect 0x1270df 4 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x1270df 4 0 13).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1270df 0x41 (by decide) 0xc5 (by decide)) pre_rip
  have f1 : InstrSpec 0x1270e3 [0x48, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1270e3) (leaR64Effect 0x1270e3 1 (.abs (some 2) 3 0x0))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1270e3 1 (.abs (some 2) 3 0x0)).toInstrSpec (lea_r64_effect_step 0x1270e3 0x48 (by decide) 1 (.abs (some 2) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1270eb [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1270eb) (xorR32R32Effect 0x1270eb 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1270eb 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1270eb 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1270ee [0x48, 0x39, 0xC1] (fun s => s.RIP = 0x1270ee) (cmpR64R64Effect 0x1270ee 1 0)
      [.gpr 1, .gpr 0] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1270ee 1 0).toInstrSpec (cmp_r64_r64_effect_step 0x1270ee 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270eb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270f1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1270f1 3 0xa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1270df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1270df :=
  Rest.liftedBlock (rest_l1270df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1270df x hx)

theorem rest_l1270f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1270f3 bytes_l1270f3) (entryMap (live .l1270f3))
      2 0x1270f3 bytes_l1270f3 b_l1270f3 := by
  have f0 : InstrSpec 0x1270f3 [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1270f3) (movR32Imm32Effect 0x1270f3 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1270f3 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x1270f3 0xb8 (by decide) 0xc) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1270f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1270f8 0xfffffe90 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1270f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1270f3 :=
  Rest.liftedBlock (rest_l1270f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1270f3 x hx)

theorem rest_l1270fd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1270fd bytes_l1270fd) (entryMap (live .l1270fd))
      7 0x1270fd bytes_l1270fd b_l1270fd := by
  have f0 : InstrSpec 0x1270fd [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x1270fd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1270fd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1270fd 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1270fd 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1270fd 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127102 [0x48, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x127102 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x127102 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127102 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x127102 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x127102 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127107 [0x49, 0xBB, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x127107) (movR64Imm64Effect 0x127107 11 0xffffff0000000000)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x127107 11 0xffffff0000000000).toInstrSpec (mov_r64_imm64_effect_step 0x127107 0x49 0xbb (by decide) (by decide) 0xffffff0000000000) pre_rip
  have f3 : InstrSpec 0x127111 [0x49, 0x21, 0xCB] (fun s => s.RIP = 0x127111) (andR64R64Effect 0x127111 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x127111 11 1).toInstrSpec (and_r64_r64_effect_step 0x127111 0x49 0xcb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127114 [0xBF, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127114) (movR32Imm32Effect 0x127114 5 7 0x2)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x127114 5 7 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x127114 0xbf (by decide) 0x2) pre_rip
  have f5 : InstrSpec 0x127119 [0xC7, 0x44, 0x24, 0x0C, 0x00, 0x00, 0x00, 0x00] (StorePre 0x127119 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x127119 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x127119 8 (.sib 4 none 0 (.d8 0xc)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127119 8 (.sib 4 none 0 (.d8 0xc)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x127119 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127102) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127107) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (8, 8), (11, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127111) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (8, 8), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127114) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (7, 60), (8, 8), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127119) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (7, 60), (8, 8), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127121) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 63) (jmp_rel32_effect_step 0x127121 0xfffffe57 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1270fd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1270fd :=
  Rest.liftedBlock (rest_l1270fd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1270fd x hx)

theorem rest_l127126 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127126 bytes_l127126) (entryMap (live .l127126))
      5 0x127126 bytes_l127126 b_l127126 := by
  have f0 : InstrSpec 0x127126 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x127126) (xorR32R32Effect 0x127126 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127126 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x127126 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127129 [0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127129) (movR32Imm32Effect 0x127129 5 0 0xc)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x127129 5 0 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x127129 0xb8 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x12712e [0x31, 0xF6] (fun s => s.RIP = 0x12712e) (xorR32R32Effect 0x12712e 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12712e 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x12712e 0xf6 (by decide)) pre_rip
  have f3 : InstrSpec 0x127130 [0x31, 0xC9] (fun s => s.RIP = 0x127130) (xorR32R32Effect 0x127130 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127130 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x127130 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127129) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12712e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127130) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127132) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel32_effect_step 0x127132 0xfffffccf (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127126 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127126 :=
  Rest.liftedBlock (rest_l127126 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127126 x hx)

theorem rest_l127137 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127137 bytes_l127137) (entryMap (live .l127137))
      3 0x127137 bytes_l127137 b_l127137 := by
  have f0 : InstrSpec 0x127137 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127137) (movR32Imm32Effect 0x127137 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x127137 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x127137 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x12713c [0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x12713c) (movR64Imm32Effect 0x12713c 2 0x2036e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x12713c 2 0x2036e0).toInstrSpec (mov_r64_imm32_effect_step 0x12713c 0x48 0xc2 (by decide) (by decide) (by decide) 0x2036e0) pre_rip
  have f2 : InstrSpec 0x127143 [0xE8, 0x48, 0x2B, 0x00, 0x00] (PushPre 0x127143 5) (callEffect (fun _ => 0x129c90) 0x127148)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x127143 0x129c90 0x127148).toInstrSpec (call_rel32_effect_step 0x127143 0x2b48 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x12713c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x127143) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l127137 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127137 :=
  Rest.liftedBlock (rest_l127137 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127137 x hx)

theorem rest_l127148 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127148 bytes_l127148) (entryMap (live .l127148))
      1 0x127148 bytes_l127148 b_l127148 := by
  have f0 : InstrSpec 0x127148 [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127148) (fun _ => nopEffect 0x127148 8)
      [] [] [.rip] :=
    (nopEffect_footprint 0x127148 8).toInstrSpec (nop_m_effect_step 0x127148 [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127150) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l127148 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127148 :=
  Rest.liftedBlock (rest_l127148 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127148 x hx)

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

theorem_by block_l126d20_eval :
    program.runBlock (dialect code) ⟨.l126d20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126d47_eval :
    program.runBlock (dialect code) ⟨.l126d47, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126d6e_eval :
    program.runBlock (dialect code) ⟨.l126d6e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126d79_eval :
    program.runBlock (dialect code) ⟨.l126d79, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126d9e_eval :
    program.runBlock (dialect code) ⟨.l126d9e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126da9_eval :
    program.runBlock (dialect code) ⟨.l126da9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126e06_eval :
    program.runBlock (dialect code) ⟨.l126e06, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126e71_eval :
    program.runBlock (dialect code) ⟨.l126e71, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126e83_eval :
    program.runBlock (dialect code) ⟨.l126e83, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126e93_eval :
    program.runBlock (dialect code) ⟨.l126e93, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126ea8_eval :
    program.runBlock (dialect code) ⟨.l126ea8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126eb4_eval :
    program.runBlock (dialect code) ⟨.l126eb4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126ec6_eval :
    program.runBlock (dialect code) ⟨.l126ec6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126ecf_eval :
    program.runBlock (dialect code) ⟨.l126ecf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126ede_eval :
    program.runBlock (dialect code) ⟨.l126ede, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126ef8_eval :
    program.runBlock (dialect code) ⟨.l126ef8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f01_eval :
    program.runBlock (dialect code) ⟨.l126f01, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f13_eval :
    program.runBlock (dialect code) ⟨.l126f13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f21_eval :
    program.runBlock (dialect code) ⟨.l126f21, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f62_eval :
    program.runBlock (dialect code) ⟨.l126f62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f7d_eval :
    program.runBlock (dialect code) ⟨.l126f7d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f85_eval :
    program.runBlock (dialect code) ⟨.l126f85, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f8d_eval :
    program.runBlock (dialect code) ⟨.l126f8d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f9d_eval :
    program.runBlock (dialect code) ⟨.l126f9d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126f9f_eval :
    program.runBlock (dialect code) ⟨.l126f9f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126fe4_eval :
    program.runBlock (dialect code) ⟨.l126fe4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12702a_eval :
    program.runBlock (dialect code) ⟨.l12702a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127063_eval :
    program.runBlock (dialect code) ⟨.l127063, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127079_eval :
    program.runBlock (dialect code) ⟨.l127079, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1270a3_eval :
    program.runBlock (dialect code) ⟨.l1270a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1270b8_eval :
    program.runBlock (dialect code) ⟨.l1270b8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1270ca_eval :
    program.runBlock (dialect code) ⟨.l1270ca, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1270df_eval :
    program.runBlock (dialect code) ⟨.l1270df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1270f3_eval :
    program.runBlock (dialect code) ⟨.l1270f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1270fd_eval :
    program.runBlock (dialect code) ⟨.l1270fd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127126_eval :
    program.runBlock (dialect code) ⟨.l127126, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127137_eval :
    program.runBlock (dialect code) ⟨.l127137, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127148_eval :
    program.runBlock (dialect code) ⟨.l127148, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
